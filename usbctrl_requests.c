#include "libc/sync.h"
#include "api/libusbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl.h"
#include "usbctrl_descriptors.h"



/**********************************************************************
 * About utility functions
 * Here, we handle the bmRequestType field, which is a bitmap. We return the requested
 * field independently
 *********************************************************************/

#if defined(__FRAMAC__)

static bool conf_set = false;

/*@
    @ assigns conf_set;
*/

void usbctrl_configuration_set(void)
{
    set_bool_with_membarrier(&conf_set, true);
}

#endif/*__FRAMAC__*/

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



/*@
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures \result == ((pkt->bmRequestType >> 5) & 0x3) ;
*/

#ifndef __FRAMAC__
static inline
#endif
usbctrl_req_type_t usbctrl_std_req_get_type(usbctrl_setup_pkt_t const * const pkt)
{
    /* bits 6..5 */
    return ((pkt->bmRequestType >> 5) & 0x3);
}

/*@
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures \result == ((pkt->bmRequestType) & 0x1F);
*/

#ifndef __FRAMAC__
static inline
#endif
usbctrl_req_recipient_t usbctrl_std_req_get_recipient(usbctrl_setup_pkt_t const * const pkt)
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

/*@
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures (\result == pkt->wValue >> 8) ;
*/

#ifndef __FRAMAC__
static inline
#endif
usbctrl_req_descriptor_type_t usbctrl_std_req_get_descriptor_type(usbctrl_setup_pkt_t const * const pkt)
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

/*@
    @ requires \valid_read(ctx);
    @ assigns \nothing ;

    @ behavior true :
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   ensures \result == \true ;

    @ behavior false :
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == \false ;

    @ complete behaviors;
    @ disjoint behaviors ;
*/


#ifndef __FRAMAC__
static inline
#endif
bool is_std_requests_allowed(usbctrl_context_t const * const ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_DEFAULT ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_ADDRESS ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {

        return true;
    }

    return false;
}

/*@
    @ requires \valid_read(ctx);
    @ assigns \nothing ;

    @ behavior true :
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   ensures \result == \true ;

    @ behavior false :
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == \false ;

    @ complete behaviors;
    @ disjoint behaviors ;
*/

#ifndef __FRAMAC__
static inline
#endif
bool is_vendor_requests_allowed(usbctrl_context_t const * const ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_DEFAULT ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_ADDRESS ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {

        return true;
    }


    return false;
}

/***********************************
 * About configuration set/unset utilities (used by set_configuration function)
 */

/*
 * Deactivate currently configured endpoints
 */

/*@
    @ requires \separated(ctx,&GHOST_opaque_drv_privates);
    @ assigns  *ctx , GHOST_opaque_drv_privates;
    @ ensures \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_NONE ;
 */
#ifndef __FRAMAC__
static inline
#endif
mbed_error_t usbctrl_unset_active_endpoints(usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    if (ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    uint8_t curr_cfg = ctx->curr_cfg;
    uint8_t max_iface = ctx->cfg[curr_cfg].interface_num ;

    /*@
        @ loop invariant 0 <= iface <= max_iface ;
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop assigns iface, errcode, *ctx, GHOST_opaque_drv_privates;
        @ loop variant (max_iface - iface);
        */

    for (uint8_t iface = 0; iface < max_iface; ++iface) {

        uint8_t max_ep = ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number ;

    /*@
        @ loop invariant 0 <= i <= max_ep ;
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces[iface].eps + (0..(max_ep-1))) ;
        @ loop invariant \separated(ctx);
        @ loop assigns i, errcode, *ctx, GHOST_opaque_drv_privates;
        @ loop variant (max_ep - i) ;
    */

        for (uint8_t i = 0; i < max_ep; ++i) {

            if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].configured == true) {
                errcode = usb_backend_drv_deconfigure_endpoint(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num);
                if (errcode != MBED_ERROR_NONE) {
                    log_printf("[USBCTRL] failure while deconfiguring EP %x\n",
                            usb_backend_drv_deconfigure_endpoint(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num));
                }
                set_bool_with_membarrier(&ctx->cfg[curr_cfg].interfaces[iface].eps[i].configured, false);
            }
        }
    }

err:
    return errcode;

}


/*@
    @ requires \separated(ctx);
    @ assigns *ctx ;
    @ assigns GHOST_in_eps[0 .. USB_BACKEND_DRV_MAX_IN_EP-1].state;
    @ assigns GHOST_out_eps[0 .. USB_BACKEND_DRV_MAX_OUT_EP-1].state;
    @ ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM || \result ≡ MBED_ERROR_NOSTORAGE ;
 */
/*
 * Active endpoint for current configuration
 */
#ifndef __FRAMAC__
static inline
#endif
mbed_error_t usbctrl_set_active_endpoints(usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    if (ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    uint8_t curr_cfg = ctx->curr_cfg;
    uint8_t max_iface = ctx->cfg[curr_cfg].interface_num ;

    /*@
        @ loop invariant 0 <= iface <= max_iface ;
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop assigns iface, errcode, *ctx, GHOST_in_eps[0 .. 6 - 1].state, GHOST_out_eps[0 .. 6 - 1].state;
        @ loop variant (max_iface - iface);
    */
    for (uint8_t iface = 0; iface < max_iface; ++iface) {

        uint8_t max_ep = ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number ;

    /*@
        @ loop invariant 0 <= i <= max_ep ;
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces[iface].eps + (0..(max_ep-1))) ;
        @ loop invariant \separated(ctx);
        @ loop assigns i, errcode, *ctx, GHOST_in_eps[0 .. 6 - 1].state, GHOST_out_eps[0 .. 6 - 1].state;
        @ loop variant (max_ep - i) ;
    */

        for (uint8_t i = 0; i < max_ep; ++i) {
            usb_backend_drv_ep_dir_t dir;
            usb_backend_drv_ep_type_t type;
            switch (ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir) {
                case USB_EP_DIR_OUT:
                    dir = USB_BACKEND_DRV_EP_DIR_OUT;
                    break;
                case USB_EP_DIR_IN:
                    dir = USB_BACKEND_DRV_EP_DIR_IN;
                    break;
                case USB_EP_DIR_BOTH:
                    dir = USB_BACKEND_DRV_EP_DIR_BOTH;
                    break;
                default:
                    log_printf("[USBCTRL] invalid EP dir !\n");
                    errcode = MBED_ERROR_INVPARAM;
                    goto err;
                    break;
            }
            switch (ctx->cfg[curr_cfg].interfaces[iface].eps[i].type) {
                case USB_EP_TYPE_CONTROL:
                    type = USB_BACKEND_DRV_EP_TYPE_CONTROL;
                    break;
                case USB_EP_TYPE_ISOCHRONOUS:
                    type = USB_BACKEND_DRV_EP_TYPE_ISOCHRONOUS;
                    break;
                case USB_EP_TYPE_BULK:
                    type = USB_BACKEND_DRV_EP_TYPE_BULK;
                    break;
                case USB_EP_TYPE_INTERRUPT:
                    type = USB_BACKEND_DRV_EP_TYPE_INT;
                    break;
                default:
                    log_printf("[USBCTRL] invalid EP type !\n");
                    errcode = MBED_ERROR_INVPARAM;
                    goto err;
                    break;
            }

           log_printf("[LIBCTRL] configure EP %d (dir %d)\n", ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num, dir);

           if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].type != USB_EP_TYPE_CONTROL) {
                errcode = usb_backend_drv_configure_endpoint(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num,
                        type,
                        dir,
                        ctx->cfg[curr_cfg].interfaces[iface].eps[i].pkt_maxsize,
                        USB_BACKEND_EP_ODDFRAME,
                        ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler);
                /*@ assert errcode == MBED_ERROR_INVSTATE || errcode == MBED_ERROR_NONE  || errcode == MBED_ERROR_NOSTORAGE ; */

                 if (errcode != MBED_ERROR_NONE) {
                    log_printf("[LIBCTRL] unable to configure EP %d (dir %d): err %d\n", ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num, dir, errcode);
                    goto err;
                }

            }
            set_bool_with_membarrier(&ctx->cfg[curr_cfg].interfaces[iface].eps[i].configured, true);
        }

    }
err:
    return errcode;

}

/*
 * About standard requests handling.
 *
 * All standard requests are not handled in any state. Current state automaton must
 * be checked.
 * The following functions handle one dedicated standard request.
 */

/*@
    @ requires \valid(ctx) ;
    @ requires \separated(ctx,pkt);
    @ assigns *pkt, *ctx ;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_clear_feature(usbctrl_setup_pkt_t const * const pkt __attribute__((unused)),
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

    /*request finish here */
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
err:
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid_read(pkt) ;
    @ requires \separated(ctx+(..),pkt,&GHOST_opaque_drv_privates);
    @ assigns *ctx, GHOST_opaque_drv_privates, GHOST_in_eps[0].state ;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior USB_DEVICE_STATE_DEFAULT:
    @   assumes ctx->state == USB_DEVICE_STATE_DEFAULT ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;

    @ behavior USB_DEVICE_STATE_ADDRESS_bad_recipient_bad_index:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes ((((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ||
             ((pkt->wIndex & 0xf) != 0)) ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_false:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !((((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ||
             ((pkt->wIndex & 0xf) != 0)) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_ENDPOINT) ;
    @   assumes ((pkt->wIndex & 0xf) != EP0) ;
    @   assumes !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0xf)) ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;


    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_true:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_ENDPOINT) ;
    @   assumes ((pkt->wIndex & 0xf) == EP0) || (\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0xf)) ;
    @   ensures \result == MBED_ERROR_NONE   ;

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_other :
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_get_status(const usbctrl_setup_pkt_t *pkt,
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
             * undefined. We can, for example, stall out. */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            /*request finish here */
            set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
            break;
        case USB_DEVICE_STATE_ADDRESS:
           if (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_ENDPOINT &&
                usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE)
            {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            if ((pkt->wIndex & 0xf) != 0) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
               usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            /* handling get_status() for other cases */

               switch (usbctrl_std_req_get_recipient(pkt)) {
                case USB_REQ_RECIPIENT_ENDPOINT: {
                    /*does requested EP exists ? */
                    uint8_t epnum = pkt->wIndex & 0xf;
                    if (!epnum != EP0) {
                        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                        /*request finish here */
                        set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                        goto err;
                    }
                    /* get back the EP direction from the wIndex value (MSB bit) */
                    bool dir_in = (pkt->wIndex >> 7) & 0x1;
                    usb_ep_dir_t epdir = usbctrl_get_endpoint_direction(ctx, epnum);
                    /* check that such an EP exists in current configuration */
                    if (dir_in && (epdir == USB_EP_DIR_OUT || USB_EP_DIR_NONE)) {
                        /* inexistant endpoint. These are not local invalid behavior but
                         * nominal NAK response to host */
                        usb_backend_drv_nak(0, USB_BACKEND_DRV_EP_DIR_OUT);
                        set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                        goto err;
                    }
                    /* FIXME: check EP direction too before returning status */
                    /* return the recipient status (2 bytes, or wLength if smaller) */
                    uint8_t resp[2] = { 0 };

                    usb_backend_drv_send_data((uint8_t *)&resp, (pkt->wLength >=  2 ? 2 : pkt->wLength), EP0);
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    /* std req finishes at the oepint rise */
                    break;
                }
                case USB_REQ_RECIPIENT_DEVICE: {
                    /* return the recipient status (2 bytes, or wLength if smaller) */
                    uint8_t resp[2] = { 0 };
                    /* FIXME: add remoteWakeup and selfPowered field setting to resp */

                    usb_backend_drv_send_data((uint8_t *)&resp, (pkt->wLength >=  2 ? 2 : pkt->wLength), EP0);
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    /* std req finishes at the oepint rise */
                    break;
                }

                default:
                    usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                    goto err;
            }

            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* check that the recipient exists */
            /* return the recipient status */
            switch (usbctrl_std_req_get_recipient(pkt)) {
                case USB_REQ_RECIPIENT_ENDPOINT: {
                    /*does requested EP exists ? */
                    uint8_t epnum = pkt->wIndex & 0xf;
                    if (!usbctrl_is_endpoint_exists(ctx, epnum)) {
                        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                        /*request finish here */
                        set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                        goto err;
                    }
                    /* get back the EP direction from the wIndex value (MSB bit) */
                    bool dir_in = (pkt->wIndex >> 7) & 0x1;
                    usb_ep_dir_t epdir = usbctrl_get_endpoint_direction(ctx, epnum);
                    /* check that such an EP exists in current configuration */
                    if (dir_in && (epdir == USB_EP_DIR_OUT || USB_EP_DIR_NONE)) {
                        /* inexistant endpoint. These are not local invalid behavior but
                         * nominal NAK response to host */
                        usb_backend_drv_nak(0, USB_BACKEND_DRV_EP_DIR_OUT);
                        set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                        goto err;
                    }
                    /* FIXME: check EP direction too before returning status */
                    /* return the recipient status (2 bytes, or wLength if smaller) */
                    uint8_t resp[2] = { 0 };

                    usb_backend_drv_send_data((uint8_t *)&resp, (pkt->wLength >=  2 ? 2 : pkt->wLength), EP0);
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    /* std req finishes at the oepint rise */
                    break;
                }
                case USB_REQ_RECIPIENT_DEVICE: {
                    /* return the recipient status (2 bytes, or wLength if smaller) */
                    uint8_t resp[2] = { 0 };
                    /* FIXME: add remoteWakeup and selfPowered field setting to resp */

                    usb_backend_drv_send_data((uint8_t *)&resp, (pkt->wLength >=  2 ? 2 : pkt->wLength), EP0);
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    /* std req finishes at the oepint rise */
                    break;
                }
                case USB_REQ_RECIPIENT_INTERFACE: {

                    /*does requested Iface exists ? */
                    uint8_t ifaceid = pkt->wIndex & 0xf;
                    if (!usbctrl_is_interface_exists(ctx, ifaceid)) {
                        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                        /*request finish here */
                        set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                        goto err;
                    }
                    /* return the recipient status (2 bytes, all reserved) */
                    uint8_t resp[2] = { 0 };

                    usb_backend_drv_send_data((uint8_t *)&resp, (pkt->wLength >=  2 ? 2 : pkt->wLength), EP0);
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    /* std req finishes at the oepint rise */
                    break;
                }

                default:
                    usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                    goto err;
            }


            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            /*request finish here */
            set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }
err:
    return errcode;
}

/*@
    @ requires \valid(ctx) ;
    @ requires \separated(ctx+ (..),pkt,&GHOST_opaque_drv_privates);
    @ assigns *ctx, GHOST_opaque_drv_privates ;
    @ ensures ctx->ctrl_req_processing == \false ;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior pktvalue_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes (pkt->wValue != 0) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior lenght_not_one:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue != 0) ;
    @   assumes (pkt->wLength != 1) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior no_interface:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue != 0) ;
    @   assumes !(pkt->wLength != 1) ;
    @   assumes   !( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior interface_ok_USB_DEVICE_STATE_DEFAULT:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue != 0) ;
    @   assumes !(pkt->wLength != 1) ;
    @   assumes   ( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes ctx->state == USB_DEVICE_STATE_DEFAULT ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior interface_ok_USB_DEVICE_STATE_ADDRESS:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue != 0) ;
    @   assumes !(pkt->wLength != 1) ;
    @   assumes   ( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior interface_ok_USB_DEVICE_STATE_CONFIGURED:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue != 0) ;
    @   assumes !(pkt->wLength != 1) ;
    @   assumes   ( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_get_interface(usbctrl_setup_pkt_t const * const pkt,
                                                         usbctrl_context_t *ctx)
{
    /* GET_INTERFACE request is used to request an alternate setting when using
     * interfaces in a same configuration that use mutually exclusive settings.
     * This is not yet implemented. By now, we stall.
     */
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: get iface\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request, get back needed values */
    uint8_t iface_id = (pkt->wIndex & 0x7f);
    uint16_t length = pkt->wLength;

    if (pkt->wValue != 0) {
        /* this field must be set to 0 */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
    }
    if (length != 1) {
        /* data length *must* be 1. When valid, the device returns the alternate
         * setting */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (usbctrl_is_interface_exists(ctx, iface_id) == false) {
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* let's respond to the request */
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }
err:
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
    return errcode;
}

/*@
    @ requires \valid(ctx) ;
    @ requires \separated(ctx+(..),pkt,&GHOST_opaque_drv_privates);
    @ assigns *ctx, GHOST_opaque_drv_privates;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_INVSTATE   ;

    @ behavior USB_DEVICE_STATE_DEFAULT_pktValue_not_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ;
    @   assumes (pkt->wValue != 0) ;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures ctx->state == USB_DEVICE_STATE_ADDRESS ;

    @ behavior USB_DEVICE_STATE_DEFAULT_pktValue_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ;
    @   assumes (pkt->wValue == 0) ;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS_pktValue_not_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_ADDRESS) ;
    @   assumes (pkt->wValue != 0) ;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS_pktValue_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_ADDRESS) ;
    @   assumes (pkt->wValue == 0) ;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE && ctx->state ==  USB_DEVICE_STATE_DEFAULT ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_set_address(usbctrl_setup_pkt_t const * const pkt,
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
                usbctrl_set_state(ctx, USB_DEVICE_STATE_ADDRESS);
                /*@ assert ctx->state == USB_DEVICE_STATE_ADDRESS ; */
                ctx->address = pkt->wValue;
                usb_backend_drv_set_address(ctx->address);
            }
            /* wValue set to 0 is *not* an error condition */
            usb_backend_drv_send_zlp(0);

            break;
        case USB_DEVICE_STATE_ADDRESS:
            if (pkt->wValue != 0) {
                /* simple update of address */
                ctx->address = pkt->wValue;
                usb_backend_drv_set_address(ctx->address);
            } else {
                /* going back to default state */
                usbctrl_set_state(ctx, USB_DEVICE_STATE_DEFAULT);
                /*@ assert ctx->state == USB_DEVICE_STATE_DEFAULT ; */
            }
            usb_backend_drv_send_zlp(0);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* This case is not forbidden by USB2.0 standard, but the behavior is
             * undefined. We can, for example, stall out. */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }

err:
    /*request finish here */
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
    return errcode;
}

/*@
    @ requires \valid(ctx) ;
    @ requires \separated(ctx, pkt, &GHOST_opaque_drv_privates, GHOST_in_eps+(0 .. USB_BACKEND_DRV_MAX_IN_EP-1));
    @ assigns *ctx, GHOST_opaque_drv_privates, GHOST_in_eps[0 .. USB_BACKEND_DRV_MAX_IN_EP-1].state;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior USB_DEVICE_STATE_DEFAULT:
    @   assumes ctx->state == USB_DEVICE_STATE_DEFAULT ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   ensures \result == MBED_ERROR_NONE ;


    @ complete behaviors ;
    @ disjoint behaviors ;

*/


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_get_configuration(usbctrl_setup_pkt_t const * const pkt __attribute__((unused)),
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
            usb_backend_drv_send_data((uint8_t *)&resp, 1, EP0);
            /* usb driver read status... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            resp[0] = 0;
            usb_backend_drv_send_data((uint8_t *)&resp, 1, EP0);
            /* usb driver read status... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            resp[0] = 1; /* should be bConfigurationValue of the current config */
            usb_backend_drv_send_data((uint8_t *)&resp, 1, EP0);
            /* usb driver read status... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            /*request finish here */
            ctx->ctrl_req_processing = false;
            break;
    }

err:
    return errcode;
}

/*@
    @ requires  \valid(ctx);
    @ requires \separated(ctx,pkt,&GHOST_opaque_drv_privates,GHOST_in_eps+(0 .. USB_BACKEND_DRV_MAX_IN_EP-1),GHOST_out_eps+(0 .. USB_BACKEND_DRV_MAX_OUT_EP-1));
    @ ensures ctx->ctrl_req_processing == \false;
    @ assigns conf_set, *ctx, GHOST_opaque_drv_privates ;
    @ assigns GHOST_in_eps[0 .. USB_BACKEND_DRV_MAX_IN_EP-1].state, GHOST_out_eps[0 .. USB_BACKEND_DRV_MAX_OUT_EP-1].state;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;


    @ behavior INVPARAM:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes ( (pkt->wValue & 0xff) == 0 || (pkt->wValue & 0xff) > ctx->num_cfg ) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   ensures ctx->state == USB_DEVICE_STATE_CONFIGURED ;

    @ behavior OK:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !( (pkt->wValue & 0xff) == 0 || (pkt->wValue & 0xff) > ctx->num_cfg ) ;
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE || \result == MBED_ERROR_INVPARAM ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
    TODO : be more precise with configure endpoint behavior result
*/


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_set_configuration(usbctrl_setup_pkt_t const * const pkt,
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
    /*@ assert ctx->state == USB_DEVICE_STATE_CONFIGURED ; */

    requested_configuration = (pkt->wValue & 0xff);
    /* sanity on requested configuration */
    if ((requested_configuration == 0) || (requested_configuration > ctx->num_cfg)) {
        log_printf("[USBCTRL] Invalid requested configuration!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /* deactivate previous EPs */
    errcode = usbctrl_unset_active_endpoints(ctx);
    if (errcode != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] failure while deactivating endpoints\n");
        goto err;
    }
    /* all previously configured endpoint are not unconfigured. */

    /* in USB standard, starting from 1, not 0. curr_cfg is a C table index */
    ctx->curr_cfg = requested_configuration - 1;

    /* activate endpoints... */
    errcode = usbctrl_set_active_endpoints(ctx);
    if (errcode != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] failure while activating endpoints\n");
        goto err;
    }

    usbctrl_configuration_set();
    usb_backend_drv_send_zlp(0);
    /* handling standard Request */

    /*request finish here */
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
    /*@ assert ctx->state == USB_DEVICE_STATE_CONFIGURED ; */
    /*@ assert errcode == MBED_ERROR_NONE ; */
    return errcode;

    err:
    usb_backend_drv_stall(0, USB_BACKEND_DRV_EP_DIR_OUT);
    /*request finish here */
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
    /*@ assert errcode == MBED_ERROR_INVSTATE || errcode == MBED_ERROR_NOSTORAGE || errcode == MBED_ERROR_INVPARAM ; */
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

/*@
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior null_length:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes pkt->wLength == 0 ;
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_index_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_DEVICE ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_index_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_DEVICE ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_CONFIGURATION_index_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_CONFIGURATION ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_CONFIGURATION_index_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_CONFIGURATION ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_STRING:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_STRING ;
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_INTERFACE_index_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_INTERFACE ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_INTERFACE_index_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_INTERFACE ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_ENDPOINT_index_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_ENDPOINT ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_ENDPOINT_index_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_ENDPOINT ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER_index_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER_index_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG_index_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG_index_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_INTERFACE_POWER_index_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_INTERFACE_POWER ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_INTERFACE_POWER_index_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_INTERFACE_POWER ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures is_valid_error(\result) ;

    @ behavior OTHER_DESCRIPTOR :
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_DEVICE)  && ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_INTERFACE_POWER) &&
                ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG)  && ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER) &&
                ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_ENDPOINT)  && ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_INTERFACE) &&
                ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_STRING)  && ((pkt->wValue >> 8) != USB_REQ_DESCRIPTOR_CONFIGURATION) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
    TODO :
        - be more precise for behavior (add ensures on ctx->ctrl_req_processing if needed ?)
        - assigns clause is impossible to validate (due to usbctrl_get_descriptor)
*/


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_get_descriptor(usbctrl_setup_pkt_t *pkt,
                                                          usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: get descriptor\n");
    usbctrl_req_descriptor_type_t desctype;
    uint16_t maxlength;
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
        /*request finish here */
        set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
        goto err;
    }

    uint8_t buf[MAX_DESCRIPTOR_LEN] = { 0 };
    uint32_t size = 0;

    switch (desctype) {
        case USB_REQ_DESCRIPTOR_DEVICE:
            log_printf("[USBCTRL] Std req: get device descriptor\n");
            if (pkt->wIndex != 0) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }

            if ((errcode = usbctrl_get_descriptor(USB_DESC_DEVICE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    log_printf("[USBCTRL] Failure while generating descriptor !!!\n");
                    /*request finish here */
                    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                    goto err;
            }
            log_printf("[USBCTRL] sending dev desc (%d bytes req, %d bytes needed)\n", maxlength, size);

            if (maxlength >= size) {
                errcode = usb_backend_drv_send_data(&(buf[0]), size, 0);
            } else {
                errcode = usb_backend_drv_send_data(&(buf[0]), maxlength, 0);
                if (errcode != MBED_ERROR_NONE) {
                    log_printf("[USBCTRL] Error while sending data\n");
                }
                /* should we not inform the host that there is not enough
                * space ? TODO: we should: sending NYET or NAK
                * XXX: check USB2.0 standard */
            }
            /* read status .... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_CONFIGURATION:
            log_printf("[USBCTRL] Std req: get configuration descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            if ((errcode = usbctrl_get_descriptor(USB_DESC_CONFIGURATION, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            usbctrl_set_state(ctx, USB_DEVICE_STATE_CONFIGURED);
            /*@ assert ctx->state == USB_DEVICE_STATE_CONFIGURED ; */
            if (maxlength > size) {
                errcode = usb_backend_drv_send_data(&(buf[0]), size, 0);
            } else {
                errcode = usb_backend_drv_send_data(&(buf[0]), maxlength, 0);
                /* should we not inform the host that there is not enough
                 * space ? Well no, the host, send again a new descriptor
                 * request with the correct size in it.
                 * XXX: check USB2.0 standard */
            }
            /* read status .... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);

            /* it is assumed by the USB standard that the returned configuration is now active.
             * From now on, the device is in CONFIGUED state, and the returned configuration is
             * the one currently active */
            break;
        case USB_REQ_DESCRIPTOR_STRING:
            log_printf("[USBCTRL] Std req: get string descriptor\n");
            if ((errcode = usbctrl_get_descriptor(USB_DESC_STRING, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
                if (maxlength > size) {
                    errcode = usb_backend_drv_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usb_backend_drv_send_data(&(buf[0]), maxlength, 0);
                    /* should we not inform the host that there is not enough
                     * space ?
                     * XXX: check USB2.0 standard */
                }
            /* read status .... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE:
            /* wIndex (language ID) should be zero */
            log_printf("[USBCTRL] Std req: get interface descriptor\n");
            if (pkt->wIndex != 0) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
                if ((errcode = usbctrl_get_descriptor(USB_DESC_INTERFACE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    /*request finish here */
                    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                    goto err;
                }
                if (maxlength > size) {
                    errcode = usb_backend_drv_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usb_backend_drv_send_data(&(buf[0]), maxlength, 0);
                    /* should we not inform the host that there is not enough
                     * space ?
                     * XXX: check USB2.0 standard */
                }
            /* read status .... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_ENDPOINT:
            log_printf("[USBCTRL] Std req: get EP descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            if ((errcode = usbctrl_get_descriptor(USB_DESC_ENDPOINT, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            if (maxlength > size) {
                errcode = usb_backend_drv_send_data(&(buf[0]), size, 0);
            } else {
                errcode = usb_backend_drv_send_data(&(buf[0]), maxlength, 0);
                /* should we not inform the host that there is not enough
                 * space ?
                 * XXX: check USB2.0 standard */
            }
            /* read status .... */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER:
            log_printf("[USBCTRL] Std req: get dev qualifier descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            /*TODO */
            /*request finish here */
            set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG:
            log_printf("[USBCTRL] Std req: get othspeed descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            /*TODO */
            /*request finish here */
            set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE_POWER:
            log_printf("[USBCTRL] Std req: get iface power descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
                goto err;
            }
            /*TODO */
            /*request finish here */
            set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            goto err;
            break;
    }

    return errcode;
err:
    usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
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

/*@
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt, &GHOST_opaque_drv_privates);
    @   assigns *pkt, *ctx, GHOST_opaque_drv_privates ;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE && ctx->ctrl_req_processing == \false ;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_NONE &&  ctx->ctrl_req_processing == \false ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_set_descriptor(usbctrl_setup_pkt_t * const pkt __attribute__((unused)),
                                                          usbctrl_context_t *ctx)
{
    /* TODO: this implementation is more complex.
     *  The goal of this request here is to handle the following:
     *  if there is more than one configuration in the context, the host can request
     *  a SetDescriptor, typically for the configuration descriptor. This requires for
     *  the device to switch from one configuration to another. In that case, previously
     *  mapped and activated endpoints (other than 0) must be deactivated, and the newly
     *  requested configuration interfaces and associated endpoints must be enabled.
     *
     *  This action can be done at ADDRESS and CONFIGURED state from the host.
     *  As the libxDCI handles potential multiple configurations, this request *must* be
     *  handled, at least for the SET_DESCRIPTOR(CONFIGURATION_DESCRIPTOR) request.
     */
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: set descriptor\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        /*request finish here */
        set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
        goto err;
    }
    /* handling standard Request */
    /* By now, we do not which to allow the host to set one of our descriptors.
     * As a consequence, we reply a request error to the host, meaning that this
     * behavior is not supported by the device.
     */

    usb_backend_drv_send_zlp(0);
    /*request finish here */
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
err:
    return errcode;
}

/*@
    @ requires \valid_read(pkt) && \valid(ctx);
    @ requires \separated(ctx+(..),pkt,&GHOST_opaque_drv_privates);
    @ assigns *ctx , GHOST_opaque_drv_privates;
    @ ensures ctx->ctrl_req_processing == \false;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;


    @ behavior length_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes (pkt->wLength != 0 ) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior USB_DEVICE_STATE_DEFAULT:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 0 ) ;
    @   assumes ctx->state == USB_DEVICE_STATE_DEFAULT ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 0 ) ;
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 0 ) ;
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   ensures \result == MBED_ERROR_NONE ;


    @ complete behaviors ;
    @ disjoint behaviors ;

*/


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_set_feature(usbctrl_setup_pkt_t * const pkt,
                                                       usbctrl_context_t *ctx)
{
    /* SET_FEATURE is made to activate device/interface and endpoint testing modes.
     * This is efficient for hardware-based devices stacks for which debugging is
     * made through the USB protocol only (no software debug is possible.
     * In our case, the USB control stack is a full software implementation, and
     * to avoid any vulnerability associated to a complex switch to a test mode of
     * the stack, we return an INVALID_REQUEST here.
     */
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: set feature\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request, get back needed values */
    uint16_t length = pkt->wLength;

    if (length != 0) {
        /* data length *must* be 0. There is no DATA stage after this SETUP stage */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* let's respond to the request */
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }
err:
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx+(..),pkt,&GHOST_opaque_drv_privates);
    @ assigns *ctx , GHOST_opaque_drv_privates;
    @ ensures ctx->ctrl_req_processing == \false ;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior lenght_not_null:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes (pkt->wLength != 0) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior no_interface:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 0) ;
    @   assumes   !( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior interface_ok_USB_DEVICE_STATE_DEFAULT:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 0) ;
    @   assumes   ( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes ctx->state == USB_DEVICE_STATE_DEFAULT ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior interface_ok_USB_DEVICE_STATE_ADDRESS:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 0) ;
    @   assumes   ( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior interface_ok_USB_DEVICE_STATE_CONFIGURED:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 0) ;
    @   assumes   ( (pkt->wIndex & 0x7f) < ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_set_interface(usbctrl_setup_pkt_t * const pkt,
                                                         usbctrl_context_t *ctx)
{
    /* This request permit to select interfaces of a same configuration which
     * are mutually exclusive.
     * This type of profile is not handled by the libxDCI, which, instead, handle
     * multiple configurations with mutually exclusive interfaces in it.
     * As a consequence, we return a STALL response to this request.
     * See SET_CONFIGURATION request instead. */
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: set interface\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request, get back needed values */
    uint8_t iface_id = (pkt->wIndex & 0x7f);
    uint16_t length = pkt->wLength;
    if (length != 0) {
        /* data length *must* be 0. There is no DATA stage after this SETUP stage */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (usbctrl_is_interface_exists(ctx, iface_id) == false) {
        /* if the targetted ep does not exist in the current configuration, this
         * request is invalid. */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /* let's respond to the request */
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            /* on DEFAULT state, USB 2.0 says 'undefined behavior', here, we stall */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            /* USB 2.0 says that we repond with a 'request error' */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* here, we supports only default settings for all our interfaces.
             * we respond a request error */
            /*
             * TODO: Idealy, we should be able to handle mutually exclusive interfaces in a same
             * configuration. In this case, here, the SetInterface should be used by the host
             * to specify which interface is to be activated.
             * This behavior differs from the Set_Configuration, which handle set of interfaces
             * switching.
             * By now, the libxDCI handles the Set_Configuration to manipulate mutually exclusive
             * interfaces, instead of Set_Interface().
             */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }
err:
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid_read(pkt) ;
    @ requires \separated(ctx+(..),pkt,&GHOST_opaque_drv_privates);
    @ assigns *ctx , GHOST_opaque_drv_privates;
    @ ensures ctx->ctrl_req_processing == \false ;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior lenght_not_twice:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes (pkt->wLength != 2) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior no_endpoint:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 2) ;
    @   assumes (((pkt->wIndex & 0x7f) != EP0) && !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0x7f))) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior endpoint_ok_USB_DEVICE_STATE_DEFAULT:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 2) ;
    @   assumes !(((pkt->wIndex & 0x7f) != EP0) && !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0x7f))) ;
    @   assumes ctx->state == USB_DEVICE_STATE_DEFAULT ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior endpoint_ok_USB_DEVICE_STATE_ADDRESS:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 2) ;
    @   assumes !(((pkt->wIndex & 0x7f) != EP0) && !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0x7f))) ;
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior endpoint_ok_USB_DEVICE_STATE_CONFIGURED:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength != 2) ;
    @   assumes !(((pkt->wIndex & 0x7f) != EP0) && !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0x7f))) ;
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_std_req_handle_synch_frame(usbctrl_setup_pkt_t * const pkt,
                                                       usbctrl_context_t *ctx)
{
    /* Set an endpoint syncrhonization frame
     *
     * When an endpoint supports isochronous transfers, the endpoint may also require
     * per-frame transfers to vary in size according to a specific pattern. The host
     * and the endpoint must agree on which frame the repeating pattern begins.
     * The number of the frame in which the pattern began is returned to the host.
     * If a high-speed device supports the Synch Frame request, it must internally
     * synchronize itself to the zeroth microframe and have a time notion of classic
     * frame. Only the frame number is used to synchronize and reported by the device
     * endpoint (i.e., no microframe number). The endpoint must synchronize to the
     * zeroth microframe.
     * This value is only used for isochronous data transfers using implicit pattern
     * synchronization. If wValue is non-zero or wLength is not two, then the behavior
     * of the device is not specified.
     * If the specified endpoint does not support this request, then the device will
     * respond with a Request Error.
     *
     * In the current implementation of the libxDCI, SYNC_FRAME is not supported as
     * there is no frame/micro-frame count (it requires a lot of CPU cycles).
     * This may be updated later using hardware-assisted calculation.
     * Thus, we implement the request sanitation.
     */
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: sync_frame\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request, get back needed values */
    /* ep_id is mapped on 7 lower bits are USB standard defines up to 127 endpoints */
    /* NOTE: Here Frama-C will have to accept that a binary mask ensure that the
     * resulted value can be set in a uint8_t type */
    uint8_t ep_id = (pkt->wIndex & 0x7f);
    uint16_t length = pkt->wLength;
    if (length != 2) {
        /* data length *must* be 2. The DATA packet received next should be of size 2 */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (usbctrl_is_endpoint_exists(ctx, ep_id) == false) {
        /* if the targetted ep does not exist in the current configuration, this
         * request is invalid. */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /* let's respond to the request */
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            /* on DEFAULT state, USB 2.0 says 'undefined behavior', here, we stall */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_ADDRESS:
            /* USB 2.0 says that we repond with a 'request error' */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* here, this is a valid request, but while we do not support SYNC_FRAME,
             * we respond a request error */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;

    }
err:
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
    return errcode;
}


/*
 * Standard requests must be supported by any devices and are handled here.
 * These requests handlers are written above and executed directly by the libusbctrl
 */

/*@
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(pkt, ctx + (..), &conf_set);

    @ behavior USB_REQ_GET_STATUS:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_STATUS ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;
    @   assigns *ctx, GHOST_opaque_drv_privates, GHOST_in_eps[0].state ;

    @ behavior USB_REQ_CLEAR_FEATURE:
    @   assumes  pkt->bRequest ==  USB_REQ_CLEAR_FEATURE ;
    @   assigns *pkt, *ctx ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;

    @ behavior USB_REQ_SET_FEATURE:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_FEATURE ;
    @   assigns *ctx, GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM ;

    @ behavior USB_REQ_SET_ADDRESS:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_ADDRESS ;
    @   assigns *ctx, GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;

    @ behavior USB_REQ_GET_DESCRIPTOR:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_DESCRIPTOR ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_SET_DESCRIPTOR:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_DESCRIPTOR ;
	@   assigns *pkt, *ctx, GHOST_opaque_drv_privates;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;

    @ behavior USB_REQ_GET_CONFIGURATION:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_CONFIGURATION ;
    @   assigns *ctx, GHOST_opaque_drv_privates, GHOST_in_eps[0 .. USB_BACKEND_DRV_MAX_IN_EP-1].state;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;

    @ behavior USB_REQ_SET_CONFIGURATION:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_CONFIGURATION ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_NOSTORAGE ;
    @   assigns conf_set, *ctx ;
    @   assigns GHOST_opaque_drv_privates ;
    @   assigns GHOST_in_eps[0 .. USB_BACKEND_DRV_MAX_IN_EP-1].state, GHOST_out_eps[0 .. USB_BACKEND_DRV_MAX_OUT_EP-1].state;

    @ behavior USB_REQ_GET_INTERFACE:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_INTERFACE ;
    @ 	assigns *ctx, GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM ;

    @ behavior USB_REQ_SET_INTERFACE:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_INTERFACE ;
    @ 	assigns *ctx, GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM ;

    @ behavior USB_REQ_SYNCH_FRAME:
    @   assumes  pkt->bRequest ==  USB_REQ_SYNCH_FRAME ;
    @ 	assigns *ctx, GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM ;

    @ behavior DEFAULT:
    @   assumes  !(pkt->bRequest ==  USB_REQ_GET_STATUS) && !(pkt->bRequest ==  USB_REQ_CLEAR_FEATURE) && !(pkt->bRequest ==  USB_REQ_SET_FEATURE) &&
                !(pkt->bRequest ==  USB_REQ_SET_ADDRESS) && !(pkt->bRequest ==  USB_REQ_GET_DESCRIPTOR) && !(pkt->bRequest ==  USB_REQ_SET_DESCRIPTOR) &&
                 !(pkt->bRequest ==  USB_REQ_GET_CONFIGURATION) && !(pkt->bRequest ==  USB_REQ_SET_CONFIGURATION) && !(pkt->bRequest ==  USB_REQ_GET_INTERFACE) &&
                 !(pkt->bRequest ==  USB_REQ_SET_INTERFACE) && !(pkt->bRequest ==  USB_REQ_SYNCH_FRAME)  ;
    @   ensures is_valid_error(\result);

    @ complete behaviors ;
    @ disjoint behaviors ;
*/


/*
    TODO :
        - be more precise for behavior
        - assigns clause is impossible to validate (due to usbctrl_get_descriptor)
*/

#ifndef __FRAMAC__
static inline
#endif
mbed_error_t usbctrl_handle_std_requests(usbctrl_setup_pkt_t *pkt,
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
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }
    return errcode;
}

/*
 * TODO: The previous usb_control implementation didn't support the vendor requests.
 * It would be great to implement properly these requests now.
 */

/*@
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt+(..));
    @   assigns *ctx ;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures ctx->ctrl_req_processing == \false;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

#ifndef __FRAMAC__
static inline
#endif
mbed_error_t usbctrl_handle_vendor_requests(usbctrl_setup_pkt_t * const pkt __attribute__((unused)),
                                            usbctrl_context_t   *ctx)

{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!is_vendor_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    /* request finish here */
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);
err:
    return errcode;
}

/*
 * Class requests targets interfaces (i.e. registered interfaces).
 * These requests are transfered to each upper pesonalities class request handlers
 * to find which one is able to respond to the current setup pkt.
 * this function is a dispatcher between the various registered personalities
 */



/*
 * Fallback. Here the requests is invalid, using a reserved value. an error is
 * returned.
 */

/*@
    @ requires \valid(pkt) && \valid(ctx) ;
    @ requires \separated(ctx,pkt);
    @ ensures \result == MBED_ERROR_UNKNOWN ;
    @ assigns GHOST_opaque_drv_privates ;
*/


#ifndef __FRAMAC__
static inline
#endif
mbed_error_t usbctrl_handle_unknown_requests(usbctrl_setup_pkt_t *const pkt __attribute__((unused)),
                                             usbctrl_context_t   *const ctx __attribute__((unused)))
{
    log_printf("[USBCTRL] Unknown Request type %d/%x\n", pkt->bmRequestType, pkt->bRequest);
    usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
    return MBED_ERROR_UNKNOWN;
}

/*
 * Global requests dispatcher. This function call the corresponding request handler, get back
 * its error code in return, release the EP0 receive FIFO lock and return the error code.
 *
 */

/*@
    @ requires \separated(pkt,&ctx_list[0..(GHOST_num_ctx-1)],&GHOST_idx_ctx) ;
    @ requires \valid(ctx_list + (0..(GHOST_num_ctx-1))) ;
    @ ensures \old(GHOST_num_ctx) == GHOST_num_ctx ;

    @ behavior bad_ctx:
    @   assumes \forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id ;
    @   assigns GHOST_idx_ctx, GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_UNKNOWN ;

    @ behavior bad_pkt:
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes pkt == \null ;
    @   assigns GHOST_idx_ctx, ctx_list[0..(GHOST_num_ctx-1)], GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior USB_REQ_TYPE_STD:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes ((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD ;
    @   ensures is_valid_error(\result) ;   // être plus précis quand la fonction usbctrl_handle_std_requests sera correctement spécifiée

    @ behavior USB_REQ_TYPE_VENDOR:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;
    @   ensures (\result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE) ;
    @   assigns ctx_list[0..(GHOST_num_ctx-1)], GHOST_idx_ctx ;

    @ behavior USB_REQ_TYPE_CLASS:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes ((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS ;
    @   ensures is_valid_error(\result) ;
    @   assigns GHOST_idx_ctx, ctx_list[0..(GHOST_num_ctx-1)], GHOST_opaque_drv_privates ;

    @ behavior UNKNOWN:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes ((pkt->bmRequestType >> 5) & 0x3) != USB_REQ_TYPE_CLASS ;
    @   assumes ((pkt->bmRequestType >> 5) & 0x3) != USB_REQ_TYPE_VENDOR ;
    @   assumes ((pkt->bmRequestType >> 5) & 0x3) != USB_REQ_TYPE_STD ;
    @   assigns GHOST_idx_ctx,ctx_list[0..(GHOST_num_ctx-1)],GHOST_opaque_drv_privates ;
    @   ensures \result == MBED_ERROR_UNKNOWN ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/


/*
TODO : update assigns and ensures clauses for USB_REQ_TYPE_STD behavior (need usbctrl_handle_std_requests to me more precise)
        these assigns need usbctrl_get_descriptor so... impossible for now
        be more precise for USB_REQ_TYPE_CLASS behavior (\result errcode)
*/

mbed_error_t usbctrl_handle_requests(usbctrl_setup_pkt_t *pkt,
                                     uint32_t             dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;

    /* Detect which context is assocated to current request and set local ctx */
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {
        /* trapped on oepint() from a device which is not handled here ! what ? */
        errcode = MBED_ERROR_UNKNOWN;
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_OUT);
        goto err_init;
    }
    /* Sanitation */
    if (pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_OUT);
        goto err;
    }
    /*@ assert \valid(pkt) ; */
    usbctrl_req_type_t type = usbctrl_std_req_get_type(pkt);

    switch(type){
        case USB_REQ_TYPE_STD:
            if(usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE){
                set_bool_with_membarrier(&(ctx->ctrl_req_processing), true);
                log_printf("[USBCTRL] std request for control (recipient = 0)\n");
                /* For current request of current context, is the current context is a standard
                * request ? If yes, handle localy */
                /*@ assert \separated(pkt, ctx + (..), &conf_set); */
                errcode = usbctrl_handle_std_requests(pkt, ctx);
            }else{
                log_printf("[USBCTRL] std request for iface/ep/other: %x\n", usbctrl_std_req_get_recipient(pkt));
                uint8_t curr_cfg = ctx->curr_cfg;
                mbed_error_t upper_stack_err = MBED_ERROR_INVPARAM;

            /*@
                @ loop invariant 0 <= i <= ctx->cfg[curr_cfg].interface_num ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(ctx->cfg[curr_cfg].interface_num-1))) ;
                @ loop assigns i, upper_stack_err ;
                @ loop variant (ctx->cfg[curr_cfg].interface_num - i);
            */
                for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interface_num; ++i) {
                    if (ctx->cfg[curr_cfg].interfaces[i].rqst_handler) {
                        log_printf("[USBCTRL] execute iface class handler\n");
                        uint32_t handler;
                        if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
                            log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
                            goto err ;
                        }

#ifndef __FRAMAC__
                        if (handler_sanity_check((physaddr_t)ctx->cfg[curr_cfg].interfaces[i].rqst_handler)) {
                            goto err;
                        }
#endif
                /*@ assert \separated(&handler,pkt,ctx_list + (0..(GHOST_num_ctx-1))) ; */
                /*@ assert ctx->cfg[curr_cfg].interfaces[i].rqst_handler ∈ {&class_rqst_handler}; */
                /*@ calls class_rqst_handler; */

                        if ((upper_stack_err = ctx->cfg[curr_cfg].interfaces[i].rqst_handler(handler, pkt)) == MBED_ERROR_NONE) {
                            /* upper class handler found, we can leave the loop */
                            break;
                        }
                    }
                }

                /* fallback if no upper stack class request handler was able to handle the received CLASS request */
                if (upper_stack_err != MBED_ERROR_NONE) {
                    usb_backend_drv_stall(0, USB_BACKEND_DRV_EP_DIR_OUT);
                }
                /* upgrade local errcode with upper stack errcode received */
                errcode = usbctrl_handle_unknown_requests(pkt, ctx);
            }
            break;
        case USB_REQ_TYPE_VENDOR:
            log_printf("[USBCTRL] vendor request\n");
            /* ... or, is the current request is a vendor request, then handle locally
            * for vendor */
            set_bool_with_membarrier(&(ctx->ctrl_req_processing), true);
            /*@ assert \separated(pkt, ctx + (..)); */
            errcode = usbctrl_handle_vendor_requests(pkt, ctx);
            break;
        case USB_REQ_TYPE_CLASS:
            if(usbctrl_std_req_get_recipient(pkt) == USB_REQ_RECIPIENT_INTERFACE){
                log_printf("[USBCTRL] class request for iface\n");
                //if(usbctrl_std_req_get_recipient(pkt) == USB_REQ_RECIPIENT_INTERFACE){
                log_printf("[USBCTRL] receiving class Request\n");
                /* ... or, is the current request is a class request or target a dedicated
                * interface, then handle in upper layer*/
                uint8_t curr_cfg = ctx->curr_cfg;
                mbed_error_t upper_stack_err = MBED_ERROR_INVPARAM;

            /*@
                @ loop invariant 0 <= i <= ctx->cfg[curr_cfg].interface_num ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(ctx->cfg[curr_cfg].interface_num-1))) ;
                @ loop assigns i, upper_stack_err ;
                @ loop variant (ctx->cfg[curr_cfg].interface_num - i);
            */
                for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interface_num; ++i) {
                    if (ctx->cfg[curr_cfg].interfaces[i].rqst_handler) {
                        log_printf("[USBCTRL] execute iface class handler\n");
                        uint32_t handler;
                        if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
                            log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
                            goto err ;
                        }

#ifndef __FRAMAC__
                        if (handler_sanity_check((physaddr_t)ctx->cfg[curr_cfg].interfaces[i].rqst_handler)) {
                            goto err;
                        }
#endif
                /*@ assert ctx->cfg[curr_cfg].interfaces[i].rqst_handler ∈ {&class_rqst_handler}; */
                /*@ calls class_rqst_handler; */

                        if ((upper_stack_err = ctx->cfg[curr_cfg].interfaces[i].rqst_handler(handler, pkt)) == MBED_ERROR_NONE) {
                            /* upper class handler found, we can leave the loop */
                            break;
                        }
                    }
                }

                /* fallback if no upper stack class request handler was able to handle the received CLASS request */
                if (upper_stack_err != MBED_ERROR_NONE) {
                    printf("[USBCTRL] error during iface class rqust handler exec: %d\n", upper_stack_err);
                    usb_backend_drv_stall(0, USB_BACKEND_DRV_EP_DIR_OUT);
                }
                /* upgrade local errcode with upper stack errcode received */
                errcode = upper_stack_err;
            }else{
                log_printf("[USBCTRL] class request for other(s)\n");
                errcode = usbctrl_handle_unknown_requests(pkt, ctx);
            }
            break;
        default:
            log_printf("[USBCTRL] unknown request\n");
            errcode = usbctrl_handle_unknown_requests(pkt, ctx);
            break;
    }

err:
    /* release EP0 recv FIFO */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
err_init:

    return errcode;
}
