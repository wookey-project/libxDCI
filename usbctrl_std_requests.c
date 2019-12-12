#include "api/libusbctrl.h"
#include "api/"


/*
 * About standard requests handling.
 *
 * All standard requests are not handled in any state. Current state automaton must
 * be checked.
 * The following functions handle one dedicated standard request.
 */

static mbed_error_t usbctrl_std_req_handle_clear_feature(usbctrl_setup_pkt_t *pkt
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_CLEAR_FEATURE, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_get_status(usbctrl_setup_pkt_t *pkt
                                                      usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_GET_STATUS, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_get_descriptor(usbctrl_setup_pkt_t *pkt
                                                          usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_GET_DESCRIPTOR, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_get_interface(usbctrl_setup_pkt_t *pkt
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_GET_INTERFACE, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_status(usbctrl_setup_pkt_t *pkt
                                                      usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_SET_STATUS, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_address(usbctrl_setup_pkt_t *pkt
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_SET_ADDRESS, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_configuration(usbctrl_setup_pkt_t *pkt
                                                             usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_SET_CONFIGURATION, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_description(usbctrl_setup_pkt_t *pkt
                                                           usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_SET_DESCRIPTION, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_feature(usbctrl_setup_pkt_t *pkt
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_SET_FEATURE, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_interface(usbctrl_setup_pkt_t *pkt
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_SET_INTERFACE, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_synch_frame(usbctrl_setup_pkt_t *pkt
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usb_is_valid_transition(USB_REQ_SYNCH_FRAME, ctx->state)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
err:
    return errcode;
}



/*
 * Global requests dispatcher
 */
mbed_error_t usbctrl_handle_requests(usbctrl_setup_pkt_t *pkt,
                                     usb_device_identifier_t id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;

    /* Sanitation */
    if (pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* Detect which context is assocated to current request and set local ctx */


    /* For current request of current context, is the current context is a standard
     * request ? If yes, handle localy */
    /* ... or, is the current request is a vendor request, then handle locally for vendor*/
    /* ... or, is the current request is a class request, then handle in upper layer*/
    /* ... or return an error */
err:
    return errcode;
}
