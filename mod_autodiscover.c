/* Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * mod_autodiscover.c --- The Apache mod_autodiscover module provides an input
 *                        filter able to parse an Autodiscover request body.
 *
 * Example config:
 *
 * <IfModule mod_autodiscover.c>
 *   <Location /autodiscover>
 *     SetInputFilter AUTODISCOVER
 *   </Location>
 * </IfModule>
 *
 * The email address, if present, is made available in the environment variable
 * AUTODISCOVER_EMAIL.
 */

#include "apr.h"
#include "apr_escape.h"
#include "apr_strings.h"
#include "apr_buckets.h"
#include "apr_lib.h"
#include "apr_hash.h"
#include "apr_tables.h"
#include "apr_cstr.h"
#include "apr_uuid.h"
#include "apr_xml.h"

#include "ap_config.h"
#include "ap_expr.h"
#include "ap_mpm.h"
#include "util_filter.h"
#include "httpd.h"
#include "http_config.h"
#include "http_log.h"
#include "http_protocol.h"
#include "http_request.h"

#undef PACKAGE_BUGREPORT
#undef PACKAGE_NAME
#undef PACKAGE_STRING
#undef PACKAGE_TARNAME
#undef PACKAGE_VERSION

#include "config.h"

module AP_MODULE_DECLARE_DATA autodiscover_module;

#define AUTODISCOVER_FILTER "AUTODISCOVER"
#define AUTODISCOVER_EMAILADDRESS "AUTODISCOVER_EMAILADDRESS"

typedef struct buffer_ctx {
    apr_bucket_brigade *bb;
    apr_bucket_brigade *tmp;
    apr_xml_parser *xml;
    int seen_eos;
} autodiscover_ctx;

static void log_message(request_rec *r, apr_status_t status,
        const char *message, const char *err)
{

    /* Allow "error-notes" string to be printed by ap_send_error_response() */
    apr_table_setn(r->notes, "verbose-error-to", "*");

    if (err) {

        apr_table_setn(r->notes, "error-notes",
                ap_escape_html(r->pool,
                        apr_pstrcat(r->pool, "XML error: ", message, ": ", err,
                                NULL)));

        ap_log_rerror(
                APLOG_MARK, APLOG_ERR, status, r, "mod_autodiscover: "
                "%s (%s)", message, err);
    }
    else {

        apr_table_setn(r->notes, "error-notes",
                ap_escape_html(r->pool,
                        apr_pstrcat(r->pool, "XML error: ", message, NULL)));

        ap_log_rerror(APLOG_MARK, APLOG_ERR, status, r, "mod_autodiscover: "
            "%s", message);
    }

}

static apr_xml_elem *autodiscover_find_child_ns(const apr_xml_elem *elem,
                                                int ns, const char *tagname)
{
    apr_xml_elem *child = elem->first_child;

    for (; child; child = child->next)
        if (child->ns == ns && !strcmp(child->name, tagname))
            return child;
    return NULL;
}

static const char *autodiscover_xml_get_cdata(const apr_xml_elem *elem,
                                              apr_pool_t *pool,
                                              int strip_white)
{
    apr_size_t len = 0;
    apr_text *scan;
    const apr_xml_elem *child;
    char *cdata;
    char *s;
    apr_size_t tlen;
    const char *found_text = NULL;
    int found_count = 0;

    for (scan = elem->first_cdata.first; scan != NULL; scan = scan->next) {
        found_text = scan->text;
        ++found_count;
        len += strlen(found_text);
    }

    for (child = elem->first_child; child != NULL; child = child->next) {
        for (scan = child->following_cdata.first;
             scan != NULL;
             scan = scan->next) {
            found_text = scan->text;
            ++found_count;
            len += strlen(found_text);
        }
    }

    /* some fast-path cases:
     * 1) zero-length cdata
     * 2) a single piece of cdata with no whitespace to strip
     */
    if (len == 0)
        return "";
    if (found_count == 1) {
        if (!strip_white
            || (!apr_isspace(*found_text)
                && !apr_isspace(found_text[len - 1])))
            return found_text;
    }

    cdata = s = apr_palloc(pool, len + 1);

    for (scan = elem->first_cdata.first; scan != NULL; scan = scan->next) {
        tlen = strlen(scan->text);
        memcpy(s, scan->text, tlen);
        s += tlen;
    }

    for (child = elem->first_child; child != NULL; child = child->next) {
        for (scan = child->following_cdata.first;
             scan != NULL;
             scan = scan->next) {
            tlen = strlen(scan->text);
            memcpy(s, scan->text, tlen);
            s += tlen;
        }
    }

    *s = '\0';

    if (strip_white) {
        /* trim leading whitespace */
        while (apr_isspace(*cdata)) {     /* assume: return false for '\0' */
            ++cdata;
            --len;
        }

        /* trim trailing whitespace */
        while (len-- > 0 && apr_isspace(cdata[len]))
            continue;
        cdata[len + 1] = '\0';
    }

    return cdata;
}

/**
 * This is the AUTODISCOVER filter for HTTP requests, for parsing the body for
 * the Autodiscover XML document and making it available for future use by
 * other modules.
 */
static apr_status_t autodiscover_filter(ap_filter_t *f, apr_bucket_brigade *bb,
                                        ap_input_mode_t mode,
                                        apr_read_type_e block,
                                        apr_off_t readbytes)
{
    autodiscover_ctx *ctx = f->ctx;
    apr_status_t rv;

    /* autodiscover on main requests only */
    if (!ap_is_initial_req(f->r)) {
        ap_remove_input_filter(f);
        return ap_get_brigade(f->next, bb, mode, block, readbytes);
    }

    /* first time in? create a context */
    if (!ctx) {
        ctx = f->ctx = apr_pcalloc(f->r->pool, sizeof(*ctx));
        ctx->bb = apr_brigade_create(f->r->pool, f->c->bucket_alloc);
        ctx->tmp = apr_brigade_create(f->r->pool, f->c->bucket_alloc);
        ctx->xml = apr_xml_parser_create(f->r->pool);
    }

    /* just get out of the way of things we don't want. */
    if (mode != AP_MODE_READBYTES) {
        return ap_get_brigade(f->next, bb, mode, block, readbytes);
    }

    do {
        apr_bucket *b;

        apr_brigade_cleanup(ctx->bb);

        rv = ap_get_brigade(f->next, ctx->bb, AP_MODE_READBYTES, block,
                                1024);

        /* ap_get_brigade may return success with an empty brigade for
         * a non-blocking read which would block (an empty brigade for
         * a blocking read is an issue which is simply forwarded here).
         */
        if (rv != APR_SUCCESS || APR_BRIGADE_EMPTY(ctx->bb)) {
            return rv;
        }

        for (b = APR_BRIGADE_FIRST(ctx->bb);
             b != APR_BRIGADE_SENTINEL(ctx->bb);
             b = APR_BUCKET_NEXT(b))
        {
            const char *data;
            apr_size_t size;

            if (APR_BUCKET_IS_EOS(b)) {
                apr_xml_doc *doc;
                apr_xml_elem *elem;

                /* parse the XML */
                if (APR_SUCCESS != (rv = apr_xml_parser_done(ctx->xml, &doc))) {
                    char err[MAX_STRING_LEN];
                    apr_xml_parser_geterror(ctx->xml, err, sizeof(err));
                    log_message(f->r, rv, "Could not parse XML", err);
                    return rv;
                }

                /* extract the data */
                if (strcmp(doc->root->name, "Autodiscover")) {
                    log_message(f->r, rv, "Autodiscover element not recognised", doc->root->name);
                    return APR_EINVAL;
                }
                else if (!(elem = autodiscover_find_child_ns(doc->root, doc->root->ns, "Request"))) {
                    log_message(f->r, rv, "Autodiscover/Request element not found", NULL);
                    return APR_EINVAL;
                }
                else if (!(elem = autodiscover_find_child_ns(elem, doc->root->ns, "EMailAddress"))) {
                    log_message(f->r, rv, "Autodiscover/Request/EMailAddress element not found", NULL);
                    return APR_EINVAL; 
                }
                else if (!elem->first_cdata.first || !elem->first_cdata.first->text) {
                    log_message(f->r, rv, "Autodiscover/Request/EMailAddress element is empty", NULL);
                    return APR_EINVAL;
                }
                else {
                    const char *email = autodiscover_xml_get_cdata(elem, f->r->pool, 1);
                    apr_table_setn(f->r->subprocess_env, AUTODISCOVER_EMAILADDRESS, email);
                    ap_log_rerror(APLOG_MARK, APLOG_DEBUG, APR_SUCCESS, f->r, "mod_autodiscover: "
                                  "AUTODISCOVER_EMAILADDRESS set to: %s", email);
                }

                /* Move everything to the returning brigade. */
                APR_BUCKET_REMOVE(b);
                APR_BRIGADE_INSERT_TAIL(bb, b);

                ap_remove_input_filter(f);
                return APR_SUCCESS;
            }

            if (APR_SUCCESS != (rv = apr_bucket_read(b, &data, &size,
                APR_BLOCK_READ))) {
                return rv;
            }

            if (APR_SUCCESS != (rv = apr_xml_parser_feed(ctx->xml, data, size))) {
                char err[MAX_STRING_LEN];
                apr_xml_parser_geterror(ctx->xml, err, sizeof(err));
                log_message(f->r, rv, "Could not parse XML", err);
                return rv;
            }

        }

    } while (1);

}

static const command_rec autodiscover_cmds[] = {
    { NULL }
};

static void register_hooks(apr_pool_t *p)
{
    ap_register_input_filter(AUTODISCOVER_FILTER, autodiscover_filter,
                             NULL, AP_FTYPE_RESOURCE);
}

AP_DECLARE_MODULE(autodiscover) = {
    STANDARD20_MODULE_STUFF,
    NULL, /* create per-directory config structure */
    NULL, /* merge per-directory config structures */
    NULL, /* create per-server config structure */
    NULL, /* merge per-server config structures */
    autodiscover_cmds, /* command apr_table_t */
    register_hooks /* register hooks */
};
