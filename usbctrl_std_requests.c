#include "api/libusbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl.h"


/**********************************************************************
 * About utility functions
 * Here, we handle the bmRequestType field, which is a bitmap. We return the requested
 * field independently
 *********************************************************************/

/*
 * USB request type is set on 2 bits, the enumerate is complete, no other value is
 * possible
 */
typedef enum {
   USB_REQ_TYPE_STD      = 0,
   USB_REQ_TYPE_CLASS    = 1,
   USB_REQ_TYPE_VENDOR   = 2,
   USB_REQ_TYPE_RESERVED = 3
} usbctrl_req_type_t;

/*
 * USB request direction is set on 1 bit. Enumerate complete
 */
typedef enum {
   USB_REQ_DIR_H2D    = 0,
   USB_REQ_DIR_D2H    = 1,
} usbctrl_req_dir_t;

/*
 * USB request recipient, set on 5 bits (0..4). Value 4 to 31 are reserved
 */
typedef enum {
   USB_REQ_RECIPIENT_DEVICE       = 0,
   USB_REQ_RECIPIENT_INTERFACE    = 1,
   USB_REQ_RECIPIENT_ENDPOINT     = 2,
   USB_REQ_RECIPIENT_OTHER        = 3,
} usbctrl_req_recipient_t;




static inline usbctrl_req_type_t usbcrl_std_req_get_type(usbctrl_setup_pkt_t *pkt)
{
    /* bits 6..5 */
    return ((pkt->bmRequestType >> 5) & 0x3);
}

static inline usbctrl_req_dir_t usbcrl_std_req_get_dir(usbctrl_setup_pkt_t *pkt)
{
    /* bit 7 */
    return ((pkt->bmRequestType >> 7) & 0x1);
}

static inline usbctrl_req_recipient_t usbcrl_std_req_get_recipient(usbctrl_setup_pkt_t *pkt)
{
    /* bits 4..0 */
    return ((pkt->bmRequestType) & 0x1F);
}


/****************************************************
 * About state check
 *
 * All requests must be sent in one of the following states:
 * DEFAUT, ADDRESS, CONFIGURED.
 * The check must be done before handling any requests
 ***************************************************/
static inline bool is_request_allowed(usbctrl_context_t *ctx)
{
    if (ctx->state == USB_DEVICE_STATE_DEFAULT ||
        ctx->state == USB_DEVICE_STATE_ADDRESS ||
        ctx->state == USB_DEVICE_STATE_CONFIGURED)
    {
        return true;
    }
    return false;
}


/*
 * About standard requests handling.
 *
 * All standard requests are not handled in any state. Current state automaton must
 * be checked.
 * The following functions handle one dedicated standard request.
 */

static mbed_error_t usbctrl_std_req_handle_clear_feature(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_get_status(usbctrl_setup_pkt_t *pkt,
                                                      usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}


static mbed_error_t usbctrl_std_req_handle_get_interface(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_address(usbctrl_setup_pkt_t *pkt,
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_configuration(usbctrl_setup_pkt_t *pkt,
                                                             usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_get_descriptor(usbctrl_setup_pkt_t *pkt,
                                                          usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_descriptor(usbctrl_setup_pkt_t *pkt,
                                                          usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}


static mbed_error_t usbctrl_std_req_handle_set_feature(usbctrl_setup_pkt_t *pkt,
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_interface(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_synch_frame(usbctrl_setup_pkt_t *pkt,
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_request_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
err:
    return errcode;
}


/*
 * Standard requests must be supported by any devices and are handled here.
 * These requests handlers are written above and executed directly by the libusbctrl
 */
static inline mbed_error_t usbctrl_handle_std_requests(usbctrl_setup_pkt_t *pkt,
                                                       usbctrl_context_t   *ctx)
{
    pkt = pkt;
    ctx = ctx;
    return MBED_ERROR_NONE;
}

/*
 * TODO: The previous usb_control implementation didn't support the vendor requests.
 * It would be great to implement properly these requests now.
 */
static inline mbed_error_t usbctrl_handle_vendor_requests(usbctrl_setup_pkt_t *pkt,
                                                          usbctrl_context_t   *ctx)
{
    pkt = pkt;
    ctx = ctx;
    return MBED_ERROR_NONE;
}

/*
 * Class requests targets personalities (i.e. registered interfaces).
 * These requests are transfered to each upper pesonalities class request handlers
 * to find which one is able to respond to the current setup pkt.
 * this function is a dispatcher between the various registered personalities
 */
static inline mbed_error_t usbctrl_handle_class_requests(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t   *ctx)
{
    pkt = pkt;
    ctx = ctx;
    return MBED_ERROR_NONE;
}


/*
 * Fallback. Here the requests is invalid, using a reserved value. an error is
 * returned.
 */
static inline mbed_error_t usbctrl_handle_unknown_requests(usbctrl_setup_pkt_t *pkt,
                                                           usbctrl_context_t   *ctx)
{
    pkt = pkt;
    ctx = ctx;
    return MBED_ERROR_NONE;
}

/*
 * Global requests dispatcher
 */
mbed_error_t usbctrl_handle_requests(usbctrl_setup_pkt_t *pkt,
                                     uint32_t             dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;

    /* Sanitation */
    if (pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* Detect which context is assocated to current request and set local ctx */
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {
        /* trapped on oepint() from a device which is not handled here ! what ? */
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }

    if (usbcrl_std_req_get_type(pkt) == USB_REQ_TYPE_STD) {
        /* For current request of current context, is the current context is a standard
         * request ? If yes, handle localy */
        errcode = usbctrl_handle_std_requests(pkt, ctx);
    } else if (usbcrl_std_req_get_type(pkt) == USB_REQ_TYPE_VENDOR) {
        /* ... or, is the current request is a vendor request, then handle locally
         * for vendor */
        errcode = usbctrl_handle_vendor_requests(pkt, ctx);
    } else if (usbcrl_std_req_get_type(pkt) == USB_REQ_TYPE_CLASS) {
        /* ... or, is the current request is a class request, then handle in upper layer*/
    } else {
        /* ... or unknown, return an error */
        errcode = usbctrl_handle_unknown_requests(pkt, ctx);
    }
err:
    return errcode;
}
