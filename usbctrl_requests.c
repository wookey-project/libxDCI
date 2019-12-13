#include "api/libusbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl.h"

/* include driver header */
#include "usb.h"


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




static inline usbctrl_req_type_t usbctrl_std_req_get_type(usbctrl_setup_pkt_t *pkt)
{
    /* bits 6..5 */
    return ((pkt->bmRequestType >> 5) & 0x3);
}

static inline usbctrl_req_dir_t usbctrl_std_req_get_dir(usbctrl_setup_pkt_t *pkt)
{
    /* bit 7 */
    return ((pkt->bmRequestType >> 7) & 0x1);
}

static inline usbctrl_req_recipient_t usbctrl_std_req_get_recipient(usbctrl_setup_pkt_t *pkt)
{
    /* bits 4..0 */
    return ((pkt->bmRequestType) & 0x1F);
}


typedef enum {
    USB_REQ_DESCRIPTOR_DEVICE           = 1,
    USB_REQ_DESCRIPTOR_CONFIGURATION    = 2,
    USB_REQ_DESCRIPTOR_STRING           = 3,
    USB_REQ_DESCRIPTOR_INTERFACE        = 4,
    USB_REQ_DESCRIPTOR_ENDPOINT         = 5,
    USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER = 6,
    USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG  = 7,
    USB_REQ_DESCRIPTOR_INTERFACE_POWER  = 8,
} usbctrl_req_descriptor_type_t;

static inline usbctrl_req_descriptor_type_t usbctrl_std_req_get_descriptor_type(usbctrl_setup_pkt_t *pkt)
{
    /* explicit cast of the high byte of wValue */
    usbctrl_req_descriptor_type_t val = (usbctrl_req_descriptor_type_t)(pkt->wValue >> 8);
    return val;
}


/****************************************************
 * About state check
 *
 * All requests must be sent in one of the following states:
 * DEFAUT, ADDRESS, CONFIGURED.
 * The check must be done before handling any requests
 ***************************************************/
static inline bool is_std_requests_allowed(usbctrl_context_t *ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_DEFAULT ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_ADDRESS ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {
        return true;
    }
    return false;
}

static inline bool is_vendor_requests_allowed(usbctrl_context_t *ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_DEFAULT ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_ADDRESS ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {
        return true;
    }
    return false;
}


static inline bool is_class_requests_allowed(usbctrl_context_t *ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
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
    if (!is_std_requests_allowed(ctx)) {
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
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            /* This case is not forbidden by USB2.0 standard, but the behavior is
             * undefined. We can, for example, stall out. (FIXME) */
            usb_driver_stall_out(EP0);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            if (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_ENDPOINT &&
                usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usb_driver_stall_out(EP0);
                goto err;
            }
            if ((pkt->wIndex & 0xf) != 0) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usb_driver_stall_out(EP0);
                goto err;
            }
            /* handling get_status() for other cases */
            switch (usbctrl_std_req_get_recipient(pkt)) {
                case USB_REQ_RECIPIENT_ENDPOINT: {
                    /*does requested EP exists ? */
                    uint8_t epnum = pkt->wIndex & 0xf;
                    if (!usbctrl_is_endpoint_exists(ctx, epnum)) {
                        usb_driver_stall_out(EP0);
                        goto err;
                    }
                    /* FIXME: check EP direction too before returning status */
                    //bool dir_in = (pkt->wIndex >> 7) & 0x1;
                    /* return the recipient status (2 bytes) */
                    uint8_t resp[2] = { 0 };
                    if (pkt->wLength >= 2) {
                        usb_driver_setup_send((uint8_t *)&resp, 2, EP0);
                    } else {
                        usb_driver_setup_send((uint8_t *)&resp, pkt->wLength, EP0);
                    }
                    usb_driver_setup_read_status();
                    break;
                }
                default:
                    usb_driver_stall_out(EP0);
                    goto err;
            }

            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* check that the recipient exists */
            /* return the recipient status */
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_driver_stall_out(EP0);
            break;
    }
err:
    return errcode;
}


static mbed_error_t usbctrl_std_req_handle_get_interface(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_std_requests_allowed(ctx)) {
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
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    /* handling standard Request, see USB 2.0 chap 9.4.6 */
    /* This request is a Request assignment. This is a state automaton transition with
     * three different behaviors depending on the current state */
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            if (pkt->wValue != 0) {
                ctx->address = pkt->wValue;
                usbctrl_set_state(ctx, USB_DEVICE_STATE_ADDRESS);
            }
            /* wValue set to 0 is *not* an error condition */
        	usb_driver_setup_send_status(EP0);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            if (pkt->wValue != 0) {
                /* simple update of address */
                ctx->address = pkt->wValue;
                usb_driver_set_address(ctx->address);
            } else {
                /* going back to default state */
                usbctrl_set_state(ctx, USB_DEVICE_STATE_DEFAULT);
            }
        	usb_driver_setup_send_status(EP0);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* This case is not forbidden by USB2.0 standard, but the behavior is
             * undefined. We can, for example, stall out. (FIXME) */
            usb_driver_stall_out(EP0);

            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_driver_stall_out(EP0);
            break;
    }
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_configuration(usbctrl_setup_pkt_t *pkt,
                                                             usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_std_requests_allowed(ctx)) {
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
 * Most descriptors can be generated from all informations registered in context
 * (including personalities and EPs).
 * The only 'uncontrolled' descriptor is the functional descriptor of a given
 * interface class, for wich, here we dereference the functional descriptor
 * registered during the personality registration, if this descriptor is not null.
 *
 * Other descriptors are built dynamically.
 *
 * Here is
 */
static mbed_error_t usbctrl_std_req_handle_get_descriptor(usbctrl_setup_pkt_t *pkt,
                                                          usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_req_descriptor_type_t desctype;
    uint16_t maxlength;
    bool send_zlp = false; /* set to true if descriptor size is smaller than maxlength */
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    desctype = usbctrl_std_req_get_descriptor_type(pkt);
    /* max length to send */
    maxlength = pkt->wLength;
    switch (desctype) {
        case USB_REQ_DESCRIPTOR_DEVICE:
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            break;
        case USB_REQ_DESCRIPTOR_CONFIGURATION:
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            /* USB 2.0 standard, chap 9.4.3
             *
             * A request for configuration descriptor returns :
             * - the configuration descriptor
             * - all interfaces descriptors (including EP descriptors for each interface)
             * in a single request
             *
             * ° The first interface descriptor follow the configuration descriptor
             * ° The endpoint descriptors for the first interface follow the first interface descriptor
             * ° If there are additional interfaces, their interfaces descriptor and endpoint descriptors
             * follow the first interface endpoints descriptors
             * * Class specific and/or vendor specific descriptors follow the standard descriptors they extend
             * or modify
             * ° If the device does not support requested descriptor, it must respond with a Request Error
             *
             */
            break;
        case USB_REQ_DESCRIPTOR_STRING:
            /*TODO */
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE:
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            break;
        case USB_REQ_DESCRIPTOR_ENDPOINT:
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            break;
        case USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER:
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            break;
        case USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG:
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE_POWER:
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            break;
        default:
            goto err;
            break;
    }
    ctx = ctx;
    return errcode;
err:
    usb_driver_stall_out(EP0);
    return errcode;
}


/*
 * The host can set descriptors. Altough, this standard request is optional.
 *
 * In DEFAULT mode, the behavior of this request is not defined.
 * In ADDRESSED and CONFIGURED mode, the device can:
 *   - handle the descriptor set, if supported by the device
 *   - returns a request error, if not supported
 *
 * In our case, we don't support this optional standard request for security
 * constraint
 */
static mbed_error_t usbctrl_std_req_handle_set_descriptor(usbctrl_setup_pkt_t *pkt __attribute__((unused)),
                                                          usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    /* By now, we do not which to allow the host to set one of our descriptors.
     * As a consequence, we reply a request error to the host, meaning that this
     * behavior is not supported by the device.
     */
    usb_driver_stall_out(EP0);
err:
    return errcode;
}


static mbed_error_t usbctrl_std_req_handle_set_feature(usbctrl_setup_pkt_t *pkt,
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_std_requests_allowed(ctx)) {
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
    if (!is_std_requests_allowed(ctx)) {
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
    if (!is_std_requests_allowed(ctx)) {
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
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_vendor_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    pkt = pkt;
err:
    return errcode;
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
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_class_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    pkt = pkt;
err:
    return errcode;
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

    if (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_STD) {
        /* For current request of current context, is the current context is a standard
         * request ? If yes, handle localy */
        errcode = usbctrl_handle_std_requests(pkt, ctx);
    } else if (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_VENDOR) {
        /* ... or, is the current request is a vendor request, then handle locally
         * for vendor */
        errcode = usbctrl_handle_vendor_requests(pkt, ctx);
    } else if (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_CLASS) {
        /* ... or, is the current request is a class request, then handle in upper layer*/
    } else {
        /* ... or unknown, return an error */
        errcode = usbctrl_handle_unknown_requests(pkt, ctx);
    }
err:
    return errcode;
}
