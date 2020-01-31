#include "api/libusbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl.h"
#include "usbctrl_descriptors.h"

/* include driver header */
#include "libusbotghs.h"


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
    log_printf("[USBCTRL] Std req: clear feature\n");
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
    log_printf("[USBCTRL] Std req: get status\n");
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
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            if (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_ENDPOINT &&
                usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
                goto err;
            }
            if ((pkt->wIndex & 0xf) != 0) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
                goto err;
            }
            /* handling get_status() for other cases */
            switch (usbctrl_std_req_get_recipient(pkt)) {
                case USB_REQ_RECIPIENT_ENDPOINT: {
                    /*does requested EP exists ? */
                    uint8_t epnum = pkt->wIndex & 0xf;
                    if (!usbctrl_is_endpoint_exists(ctx, epnum)) {
                        usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
                        goto err;
                    }
                    /* FIXME: check EP direction too before returning status */
                    //bool dir_in = (pkt->wIndex >> 7) & 0x1;
                    /* return the recipient status (2 bytes, or wLength if smaller) */
                    uint8_t resp[2] = { 0 };
                    usbotghs_send_data((uint8_t *)&resp, (pkt->wLength >=  2 ? 2 : pkt->wLength), EP0);
                    usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
                    break;
                }
                default:
                    usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
                    goto err;
            }

            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* check that the recipient exists */
            /* return the recipient status */
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
    }
err:
    return errcode;
}


static mbed_error_t usbctrl_std_req_handle_get_interface(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: get iface\n");
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
    log_printf("[USBCTRL] Std req: set address\n");
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
                usbotghs_set_address(ctx->address);
            }
            /* wValue set to 0 is *not* an error condition */
            usbotghs_send_zlp(0);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            if (pkt->wValue != 0) {
                /* simple update of address */
                ctx->address = pkt->wValue;
                usbotghs_set_address(ctx->address);
            } else {
                /* going back to default state */
                usbctrl_set_state(ctx, USB_DEVICE_STATE_DEFAULT);
            }
            usbotghs_send_zlp(0);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* This case is not forbidden by USB2.0 standard, but the behavior is
             * undefined. We can, for example, stall out. (FIXME) */
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
    }
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_get_configuration(usbctrl_setup_pkt_t *pkt,
                                                             usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t resp[1];
    log_printf("[USBCTRL] Std req: get configuration\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            resp[0] = 0;
            usbotghs_send_data((uint8_t *)&resp, 1, EP0);
            /* usb driver read status... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            resp[0] = 0;
            usbotghs_send_data((uint8_t *)&resp, 1, EP0);
            /* usb driver read status... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            resp[0] = 1; /* should be bConfigurationValue of the current config */
            usbotghs_send_data((uint8_t *)&resp, 1, EP0);
            /* usb driver read status... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */

            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
    }
    pkt = pkt;

err:
    return errcode;
}



static mbed_error_t usbctrl_std_req_handle_set_configuration(usbctrl_setup_pkt_t *pkt,
                                                             usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t requested_configuration;
    log_printf("[USBCTRL] Std req: set configuration\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* request is allowed, meaning that we are in ADDRESS state. We
     * can move along to CONFIGURED state and start nominal behavior from now on. */
    usbctrl_set_state(ctx, USB_DEVICE_STATE_CONFIGURED);
    /* deactivate previous EPs */
    /* FIXME: for previous potential configuration & interface, deconfigure EPs */
    /* this should be done by detecting any configured EP of any registered iface that is set
     * 'configured' just now */
    requested_configuration = pkt->wValue;
    /* activate endpoints... */
    for (uint8_t iface = 0; iface < ctx->interface_num; ++iface) {
        if (ctx->interfaces[iface].cfg_id != ctx->curr_cfg) {
            continue;
        }
        for (uint8_t i = 0; i < ctx->interfaces[iface].usb_ep_number; ++i) {
            usbotghs_ep_dir_t dir;
            if (ctx->interfaces[iface].eps[i].mode == USB_EP_MODE_READ) {
                dir = USBOTG_HS_EP_DIR_OUT;
            } else {
                dir = USBOTG_HS_EP_DIR_IN;
            }
            log_printf("[LIBCTRL] enabling EP %d (dir %d)\n", ctx->interfaces[iface].eps[i].ep_num, dir);
            usbotghs_configure_endpoint(ctx->interfaces[iface].eps[i].ep_num,
                    ctx->interfaces[iface].eps[i].type,
                    dir,
                    ctx->interfaces[iface].eps[i].pkt_maxsize,
                    USB_HS_DXEPCTL_SD1PID_SODDFRM);
            /* handled by usb_bbb read_cmd() */
            usbotghs_activate_endpoint(ctx->interfaces[iface].eps[i].ep_num, dir);
            //usbotghs_endpoint_clear_nak(ctx->interfaces[ctx->curr_cfg].eps[i].ep_num, dir);
            ctx->interfaces[iface].eps[i].configured = true;
        }
    }
    usbotghs_send_zlp(0);
    /* handling standard Request */
    pkt = pkt;
err:
    return errcode;
}

/*
 * Most descriptors can be generated from all informations registered in context
 * (including personalities and EPs).
 * The only 'uncontrolled' descriptor is the functional descriptor of a given
 * interface class, for wich, here we dereference the functional descriptor
 * registered during the interface registration, if this descriptor is not null.
 *
 * Other descriptors are built dynamically.
 *
 * Here is
 */
static mbed_error_t usbctrl_std_req_handle_get_descriptor(usbctrl_setup_pkt_t *pkt,
                                                          usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: get descriptor\n");
    usbctrl_req_descriptor_type_t desctype;
    uint16_t maxlength;
    bool send_zlp = false; /* set to true if descriptor size is smaller than maxlength */
    send_zlp = send_zlp;
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    desctype = usbctrl_std_req_get_descriptor_type(pkt);
    /* max length to send */
    maxlength = pkt->wLength;
    if (maxlength == 0) {
        /* nothing to send */
        goto err;
    }
    /* FIXME: we should calculate the maximum descriptor we can genrate and compare
     * to current buffer */
    uint8_t buf[128];
    uint32_t size = 0;
    switch (desctype) {
        case USB_REQ_DESCRIPTOR_DEVICE:
            log_printf("[USBCTRL] Std req: get device descriptor\n");
            if (pkt->wIndex != 0) {
                goto err;
            }
            if (maxlength == 0) {
                errcode = usbotghs_send_zlp(0);
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_DEVICE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                log_printf("[USBCTRL] Failure while generating descriptor !!!\n");
                    goto err;
                }
                log_printf("[USBCTRL] sending dev desc (%d bytes req, %d bytes needed)\n", maxlength, size);
                if (maxlength >= size) {
                    errcode = usbotghs_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usbotghs_send_data(&(buf[0]), maxlength, 0);
                    if (errcode != MBED_ERROR_NONE) {
                        log_printf("[USBCTRL] Error while sending data\n");
                    }
                    /* should we not inform the host that there is not enough
                     * space ? TODO: we should: sending NYET or NAK
                     * XXX: check USB2.0 standard */
                }
            }
            /* read status .... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_CONFIGURATION:
            log_printf("[USBCTRL] Std req: get configuration descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            if (maxlength == 0) {
                errcode = usbotghs_send_zlp(0);
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_CONFIGURATION, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    goto err;
                }
                usbctrl_set_state(ctx, USB_DEVICE_STATE_CONFIGURED);
                if (maxlength > size) {
                    errcode = usbotghs_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usbotghs_send_data(&(buf[0]), maxlength, 0);
                    /* should we not inform the host that there is not enough
                     * space ? Well no, the host, send again a new descriptor
                     * request with the correct size in it.
                     * XXX: check USB2.0 standard */
                }
            }
            /* read status .... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);

            /* it is assumed by the USB standard that the returned configuration is now active.
             * From now on, the device is in CONFIGUED state, and the returned configuration is
             * the one currently active */
            break;
        case USB_REQ_DESCRIPTOR_STRING:
            log_printf("[USBCTRL] Std req: get string descriptor\n");
            if ((errcode = usbctrl_get_descriptor(USB_DESC_STRING, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                goto err;
            }
            if (maxlength == 0) {
                errcode = usbotghs_send_zlp(0);
            } else {
                if (maxlength > size) {
                    errcode = usbotghs_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usbotghs_send_data(&(buf[0]), maxlength, 0);
                    /* should we not inform the host that there is not enough
                     * space ?
                     * XXX: check USB2.0 standard */
                }
            }
            /* read status .... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE:
            /* wIndex (language ID) should be zero */
            log_printf("[USBCTRL] Std req: get interface descriptor\n");
            if (pkt->wIndex != 0) {
                goto err;
            }
            if (maxlength == 0) {
                errcode = usbotghs_send_zlp(0);
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_INTERFACE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    goto err;
                }
                if (maxlength > size) {
                    errcode = usbotghs_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usbotghs_send_data(&(buf[0]), maxlength, 0);
                    /* should we not inform the host that there is not enough
                     * space ?
                     * XXX: check USB2.0 standard */
                }
            }
            /* read status .... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_ENDPOINT:
            log_printf("[USBCTRL] Std req: get EP descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            if ((errcode = usbctrl_get_descriptor(USB_DESC_ENDPOINT, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                goto err;
            }
            if (maxlength > size) {
                errcode = usbotghs_send_data(&(buf[0]), size, 0);
            } else {
                errcode = usbotghs_send_data(&(buf[0]), maxlength, 0);
                /* should we not inform the host that there is not enough
                 * space ?
                 * XXX: check USB2.0 standard */
            }
            /* read status .... */
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER:
            log_printf("[USBCTRL] Std req: get dev qualifier descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
        case USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG:
            log_printf("[USBCTRL] Std req: get othspeed descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE_POWER:
            log_printf("[USBCTRL] Std req: get iface power descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                goto err;
            }
            /*TODO */
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
        default:
            goto err;
            break;
    }

    return errcode;
err:
    usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
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
    log_printf("[USBCTRL] Std req: set descriptor\n");
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

    usbotghs_send_zlp(0);
err:
    return errcode;
}


static mbed_error_t usbctrl_std_req_handle_set_feature(usbctrl_setup_pkt_t *pkt,
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: set feature\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    usbotghs_send_zlp(0);
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_set_interface(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: set interface\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    usbotghs_send_zlp(0);
err:
    return errcode;
}

static mbed_error_t usbctrl_std_req_handle_synch_frame(usbctrl_setup_pkt_t *pkt,
                                                       usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: sync_frame\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    usbotghs_send_zlp(0);
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
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* dispatching STD requests */
    switch (pkt->bRequest) {
        case USB_REQ_GET_STATUS:
            errcode = usbctrl_std_req_handle_get_status(pkt, ctx);
            break;
        case USB_REQ_CLEAR_FEATURE:
            errcode = usbctrl_std_req_handle_clear_feature(pkt, ctx);
            break;
        case USB_REQ_SET_FEATURE:
            errcode = usbctrl_std_req_handle_set_feature(pkt, ctx);
            break;
        case USB_REQ_SET_ADDRESS:
            errcode = usbctrl_std_req_handle_set_address(pkt, ctx);
            break;
        case USB_REQ_GET_DESCRIPTOR:
            errcode = usbctrl_std_req_handle_get_descriptor(pkt, ctx);
            break;
        case USB_REQ_SET_DESCRIPTOR:
            errcode = usbctrl_std_req_handle_set_descriptor(pkt, ctx);
            break;
        case USB_REQ_GET_CONFIGURATION:
            errcode = usbctrl_std_req_handle_get_configuration(pkt, ctx);
            break;
        case USB_REQ_SET_CONFIGURATION:
            errcode = usbctrl_std_req_handle_set_configuration(pkt, ctx);
            break;
        case USB_REQ_GET_INTERFACE:
            errcode = usbctrl_std_req_handle_get_interface(pkt, ctx);
            break;
        case USB_REQ_SET_INTERFACE:
            errcode = usbctrl_std_req_handle_set_interface(pkt, ctx);
            break;
        case USB_REQ_SYNCH_FRAME:
            errcode = usbctrl_std_req_handle_synch_frame(pkt, ctx);
            break;
        default:
            log_printf("[USBCTRL] Unknown std request %d\n", pkt->bRequest);
            usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
            break;
    }
    return errcode;
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
 * Class requests targets interfaces (i.e. registered interfaces).
 * These requests are transfered to each upper pesonalities class request handlers
 * to find which one is able to respond to the current setup pkt.
 * this function is a dispatcher between the various registered personalities
 */
static inline mbed_error_t usbctrl_handle_class_requests(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t   *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t iface_idx = 0;
    usbctrl_interface_t* iface = NULL;

    if (!is_class_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* when sending a class request, this should be to a specific interface.
     * Interfaces are identified by their cell number in the interfaces[] table,
     * and declared to the host through the descriptors, through which
     * interfaces are sent in the interfaces[] table order.
     *
     * This permit to delect which interface is targeted by the current
     * request
     * Nota Bene: USB interfaces index start with 1, cells with 0 */
    iface_idx = (((pkt->wIndex) & 0xff) - 1);

    if (!usbctrl_is_interface_exists(ctx, iface_idx)) {
        errcode = MBED_ERROR_NOTFOUND;
        usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
        goto err;
    }
    if ((iface = usbctrl_get_interface(ctx, iface_idx)) == NULL) {
        errcode = MBED_ERROR_UNKNOWN;
        usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
        goto err;
    }
    /* interface found, call its dedicated request handler */
    errcode = iface->rqst_handler(ctx, pkt);
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
    ctx = ctx;
    pkt = pkt;
    log_printf("[USBCTRL] Unknown Request type %d/%x\n", pkt->bmRequestType, pkt->bRequest);
    usbotghs_endpoint_stall(EP0, USBOTG_HS_EP_DIR_IN);
    return MBED_ERROR_UNKNOWN;
}

/*
 * Global requests dispatcher. This function call the corresponding request handler, get back
 * its error code in return, release the EP0 receive FIFO lock and return the error code.
 *
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

        log_printf("[USBCTRL] receiving class Request\n");
        /* ... or, is the current request is a class request, then handle in upper layer*/
        for (uint8_t i = 0; i < ctx->interface_num; ++i) {
            if (ctx->interfaces[i].cfg_id == ctx->curr_cfg) {
                if (ctx->interfaces[i].rqst_handler) {
                    log_printf("[USBCTRL] execute iface class handler\n");
                    ctx->interfaces[i].rqst_handler(ctx, pkt);
                }
            }
        }
    } else {
        /* ... or unknown, return an error */
        errcode = usbctrl_handle_unknown_requests(pkt, ctx);
    }
err:
    /* release EP0 recv FIFO */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
    return errcode;
}
