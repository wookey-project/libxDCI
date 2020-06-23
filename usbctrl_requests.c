#include "api/libusbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl.h"
#include "usbctrl_descriptors.h"



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

#if defined(__FRAMAC__)
    bool conf_set = false;
#endif/*!__FRAMAC__*/


/*@
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures \result == ((pkt->bmRequestType >> 5) & 0x3) ;
*/

static inline usbctrl_req_type_t usbctrl_std_req_get_type(usbctrl_setup_pkt_t *pkt)
{
    /* bits 6..5 */
    return ((pkt->bmRequestType >> 5) & 0x3);
}

/*@
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures \result == ((pkt->bmRequestType >> 7) & 0x1);
*/

usbctrl_req_dir_t usbctrl_std_req_get_dir(usbctrl_setup_pkt_t *pkt)
//static inline usbctrl_req_dir_t usbctrl_std_req_get_dir(usbctrl_setup_pkt_t *pkt)
{
    /* bit 7 */
    return ((pkt->bmRequestType >> 7) & 0x1);
}

/*@
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures \result == ((pkt->bmRequestType) & 0x1F);
*/

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

/*@ predicate is_valid_req_descriptor_type(usbctrl_req_descriptor_type_t i) =
    i == USB_REQ_DESCRIPTOR_DEVICE ||
    i == USB_REQ_DESCRIPTOR_CONFIGURATION ||
    i == USB_REQ_DESCRIPTOR_STRING ||
    i == USB_REQ_DESCRIPTOR_INTERFACE ||
    i == USB_REQ_DESCRIPTOR_ENDPOINT ||
    i == USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER ||
    i == USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG ||
    i == USB_REQ_DESCRIPTOR_INTERFACE_POWER ;
*/


/*@
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures (\result == pkt->wValue >> 8) ;
*/

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


static inline bool is_std_requests_allowed(usbctrl_context_t *ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_DEFAULT ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_ADDRESS ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {
        /*@  assert ctx->state ==  USB_DEVICE_STATE_DEFAULT ||
                    ctx->state ==  USB_DEVICE_STATE_ADDRESS ||
                    ctx->state ==  USB_DEVICE_STATE_CONFIGURED ; */

        return true;
    }
        /*@  assert !(ctx->state ==  USB_DEVICE_STATE_DEFAULT ||
                    ctx->state ==  USB_DEVICE_STATE_ADDRESS ||
                    ctx->state ==  USB_DEVICE_STATE_CONFIGURED) ; */

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

static inline bool is_vendor_requests_allowed(usbctrl_context_t *ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_DEFAULT ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_ADDRESS ||
        usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {
        /*@  assert ctx->state ==  USB_DEVICE_STATE_DEFAULT ||
                    ctx->state ==  USB_DEVICE_STATE_ADDRESS ||
                    ctx->state ==  USB_DEVICE_STATE_CONFIGURED ; */
        return true;
    }
        /*@  assert !(ctx->state ==  USB_DEVICE_STATE_DEFAULT ||
                    ctx->state ==  USB_DEVICE_STATE_ADDRESS ||
                    ctx->state ==  USB_DEVICE_STATE_CONFIGURED) ; */

    return false;
}


/*@
    @ requires \valid_read(ctx);
    @ requires ctx != \null ;
    @ assigns \nothing ;
    @ ensures (ctx->state == USB_DEVICE_STATE_CONFIGURED) ==> \result == \true ;
    @ ensures !(ctx->state == USB_DEVICE_STATE_CONFIGURED) ==> \result == \false ;

*/

bool is_class_requests_allowed(usbctrl_context_t *ctx)
//static inline bool is_class_requests_allowed(usbctrl_context_t *ctx)
{
    
    if ( usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {
        /* @  assert ctx->state ==  USB_DEVICE_STATE_CONFIGURED ; */
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

/*@
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns *pkt, *ctx ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   // Cyril :  ne marche pas si ctx->ctrl_req_processing est déclaré en volatile bool

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

static mbed_error_t usbctrl_std_req_handle_clear_feature(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: clear feature\n");
    if (!is_std_requests_allowed(ctx)) {

/*@
    assert !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
*/

        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */

/*@
    assert ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
*/

    pkt = pkt;
    ctx = ctx;
    /*request finish here */
    ctx->ctrl_req_processing = false;
    /*@ assert ctx->ctrl_req_processing == \false; */   // Cyril :  ne marche pas si ctx->ctrl_req_processing est déclaré en volatile bool
err:
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior USB_DEVICE_STATE_DEFAULT:
    @   assumes ctx->state == USB_DEVICE_STATE_DEFAULT ;
    @   assigns *ctx ;    
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ; 
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   

    @ behavior USB_DEVICE_STATE_ADDRESS_bad_recipient_bad_index:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes ((((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ||
             ((pkt->wIndex & 0xf) != 0)) ;
    @   assigns *ctx ;    
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
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
    @   assigns *ctx ;    
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_true:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_ENDPOINT) ;
    @   assumes ((pkt->wIndex & 0xf) == EP0) || (\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0xf)) ;
    @   ensures \result == MBED_ERROR_NONE   ; 
    @   assigns usbotghs_ctx, *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(EP0) ,*r_CORTEX_M_USBOTG_HS_DOEPTSIZ(EP0), *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), 
                *r_CORTEX_M_USBOTG_HS_GINTMSK, *USBOTG_HS_DEVICE_FIFO(usbotghs_ctx.in_eps[EP0].id), usbotghs_ctx.in_eps[EP0],
                 usbotghs_ctx.in_eps[EP0].fifo[usbotghs_ctx.in_eps[EP0].fifo_idx] ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(0) ;

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_other :
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT) ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
    FIXME : le assigns de USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_true ne passe pas à cause de l'appel à send_data (qui n'est pas complet)


pour behavior USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_true : je dois ajouter un ensures pour : return the recipient status (2 bytes, or wLength if smaller) ?
*/

// cyril : question pour eva pour faire un test sur des fonctions static?
mbed_error_t usbctrl_std_req_handle_get_status(usbctrl_setup_pkt_t *pkt,
                                                      usbctrl_context_t *ctx)
//static mbed_error_t usbctrl_std_req_handle_get_status(usbctrl_setup_pkt_t *pkt,
//                                                      usbctrl_context_t *ctx)
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
            /*@ assert \separated(ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            /*request finish here */
            ctx->ctrl_req_processing = false;
            break;
        case USB_DEVICE_STATE_ADDRESS: 
            /*@ assert \separated(pkt,ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */

    #if defined(__FRAMAC__)
            if((((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE))
                //FIXME : voir pq l'appel aux fonctions fait que le assign ne passe pas
    #else
            if (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_ENDPOINT &&
                usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE) 
    #endif/*!__FRAMAC__*/ 
            {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN); 
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }        
            if ((pkt->wIndex & 0xf) != 0) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                /*@ assert \separated(ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
                usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            /* handling get_status() for other cases */
            //
    #if defined(__FRAMAC__)          
              switch((pkt->bmRequestType) & 0x1F){
    #else
              switch (usbctrl_std_req_get_recipient(pkt)) {
    #endif/*!__FRAMAC__*/   
                case USB_REQ_RECIPIENT_ENDPOINT: {
                    /*does requested EP exists ? */
                    uint8_t epnum = pkt->wIndex & 0xf;
                    if (!usbctrl_is_endpoint_exists(ctx, epnum)) { 
                        /*@ assert \separated(ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
                        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                        /*request finish here */
                        ctx->ctrl_req_processing = false;
                        goto err;
                    }
                    /* FIXME: check EP direction too before returning status */
                    //bool dir_in = (pkt->wIndex >> 7) & 0x1;
                    /* return the recipient status (2 bytes, or wLength if smaller) */
                    uint8_t resp[2] = { 0 };

                    usb_backend_drv_send_data((uint8_t *)&resp, (pkt->wLength >=  2 ? 2 : pkt->wLength), EP0);
                    
                    /*@  assert \separated(ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(0),r_CORTEX_M_USBOTG_HS_DOEPCTL(0))   ;    */
                    usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
                    /* std req finishes at the oepint rise */
                    break;
                }
                default:
                    /*@ assert \separated(ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
                    usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                    goto err;
            }

            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* check that the recipient exists */
            /* return the recipient status */
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            /*request finish here */
            ctx->ctrl_req_processing = false;
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }
err:
    return errcode;
}

/*
    spec qui sera à mettre à jour avec l'évolution de la fonction qui n'est pas encore définie lorsque les états sont OK
*/

/*@
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);
    @ assigns *ctx ;
    @ assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
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

static mbed_error_t usbctrl_std_req_handle_get_interface(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t *ctx)
{
    /* GET_INTERFACE request is used to request an alternate setting when using
     * interfaces in a same configuration that use mutually exclusive settings.
     * This is not our case, as we used differenciated configurations instead.
     * As a consequence, we return INVALID_REQUEST here.
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
    ctx->ctrl_req_processing = false;
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns *ctx;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_INVSTATE   ;

    @ behavior USB_DEVICE_STATE_DEFAULT_pktValue_not_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ;
    @   assumes (pkt->wValue != 0) ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DCFG, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   assigns *ctx;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures ctx->state == USB_DEVICE_STATE_ADDRESS ; 

    @ behavior USB_DEVICE_STATE_DEFAULT_pktValue_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ;
    @   assumes (pkt->wValue == 0) ;
    @   assigns *ctx;
    @   ensures ctx->ctrl_req_processing == false ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS_pktValue_not_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_ADDRESS) ;
    @   assumes (pkt->wValue != 0) ;
    @   assigns *ctx;
    @   ensures ctx->ctrl_req_processing == false ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DCFG, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS_pktValue_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_ADDRESS) ;
    @   assumes (pkt->wValue == 0) ;
    @   assigns *ctx;
    @   ensures ctx->ctrl_req_processing == false ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE && ctx->state ==  USB_DEVICE_STATE_DEFAULT ; 

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   assigns *ctx;
    @   ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/


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

    #if defined(__FRAMAC__)
    //ctx->state = Frama_C_interval(6,8);
    #endif/*__FRAMAC__*/


    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_DEFAULT:
            if (pkt->wValue != 0) {
                usbctrl_set_state(ctx, USB_DEVICE_STATE_ADDRESS);  // Cyril : pas prouvé par wp à cause du frama-c interval pour pkt->value
                /*@ assert ctx->state == USB_DEVICE_STATE_ADDRESS ; */
                ctx->address = pkt->wValue;
                /*@ assert \separated(ctx, r_CORTEX_M_USBOTG_HS_DCFG, r_CORTEX_M_USBOTG_HS_DTXFSTS(0), r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), r_CORTEX_M_USBOTG_HS_DSTS, r_CORTEX_M_USBOTG_HS_DIEPCTL(0)) ; */
                usb_backend_drv_set_address(ctx->address);
            /*@  assert ctx->address == pkt->wValue ;  */  
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
            /*@ assert \separated(ctx, r_CORTEX_M_USBOTG_HS_DTXFSTS(0), r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), r_CORTEX_M_USBOTG_HS_DSTS, r_CORTEX_M_USBOTG_HS_DIEPCTL(0)); */
            usb_backend_drv_send_zlp(0);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* This case is not forbidden by USB2.0 standard, but the behavior is
             * undefined. We can, for example, stall out. (FIXME) */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);   // Cyril : manque la gestion d'erreur
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }

err:
    /*request finish here */
    ctx->ctrl_req_processing = false;
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns \nothing ;
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

/*
    TODO : les assigns ( mettre à jour quand les assigns seront mis dans send_data)
    FIXME: quel degré de détail pour ce que font les fonctions du driver?
*/

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
            ctx->ctrl_req_processing = false; // Cyril : je n'arrive jamais là, donc je ne peux pas assigner req_processing
            break;
    }
    pkt = pkt;

err:
    return errcode;
}

/*@
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);
    @ ensures ctx->ctrl_req_processing == \false;

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior INVPARAM:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes (pkt->wValue == 0 || pkt->wValue > ctx->num_cfg ) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior OK:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue == 0 || pkt->wValue > ctx->num_cfg ) ;
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVSTATE ;  // Cyril :  l'éltat invstate est pas facile à atteindre, il faut que ctx (variable local) soit null... dans le driver

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
   
ctx->cfg[curr_cfg].interfaces[iface].eps[i].type != USB_EP_TYPE_CONTROL
    il manque ctx->cfg[curr_cfg].interfaces[i].eps[j].configured == \true  pour behavior NOT_USB_EP_TYPE_CONTROL et USB_EP_TYPE_CONTROL

    @   assumes !(\forall integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num &&
                0 <= j <= ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number && ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].type != USB_EP_TYPE_CONTROL);

        @   ensures (ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].configured == \true) ==> (\forall integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j <= ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number)
                ==> (ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].type == USB_EP_TYPE_CONTROL)  ;

                patch de la fonction usbotghs_configure_endpoint pour que ça passe, à cause de *r_CORTEX_M_USBOTG_HS_DOEPCTL(ep) :
                comment faire un assigns de ça avec ep qui varie???

             assigns   *r_CORTEX_M_USBOTG_HS_DTXFSTS(ep_id), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(ep_id), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id) ;
*/

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
    /*@ assert ctx->state == USB_DEVICE_STATE_CONFIGURED ; */

    /* deactivate previous EPs */
    /* FIXME: for previous potential configuration & interface, deconfigure EPs */
    /* this should be done by detecting any configured EP of any registered iface that is set
     * 'configured' just now */


#if defined(__FRAMAC__)
    //requested_configuration = pkt->wValue;  

    /*
        FIXME : RTE between uint16_t (pkt->wValue) et uint8_t (requested_configuration)
    */

    /* sanity on requested configuration */   // cyril : j'ai remplacé requested_configuration par par pkt->wValue, parce qu'il y a un bug entre uint8 et uint16
    if ((pkt->wValue == 0) || (pkt->wValue > ctx->num_cfg)) {
        log_printf("[USBCTRL] Invalid requested configuration!\n");
        /*@ assert ctx->state == USB_DEVICE_STATE_CONFIGURED ; */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    ctx->curr_cfg = pkt->wValue - 1;

#else

    requested_configuration = pkt->wValue; 
    /* sanity on requested configuration */   
    if ((requested_configuration == 0) || (requested_configuration > ctx->num_cfg)) {
        log_printf("[USBCTRL] Invalid requested configuration!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    ctx->curr_cfg = requested_configuration - 1;

#endif/*!__FRAMAC__*/ 


    uint8_t curr_cfg = ctx->curr_cfg;
    uint8_t max_iface = ctx->cfg[curr_cfg].interface_num ; // cyril : ajout pour passer le variant de la boucle alors que je fais assigns *ctx
    

    /* activate endpoints... */


    /*@
        @ loop invariant 0 <= iface <= max_iface ;
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1))) ;
        @ loop assigns iface, *ctx, errcode, usbotghs_ctx, *r_CORTEX_M_USBOTG_HS_GINTMSK, *r_CORTEX_M_USBOTG_HS_DAINTMSK;
        @ loop variant  (max_iface - iface);
    */

    for (uint8_t iface = 0; iface < max_iface; ++iface) {

        uint8_t max_ep = ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number ;  // cyril : meme chose que pour max_iface, wp passe maintenant

    /*@
        @ loop invariant 0 <= i <= max_ep ;
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces +(0..(max_iface-1)));
        @ loop invariant \valid(ctx->cfg[curr_cfg].interfaces[iface].eps + (0..(max_ep-1))) ;
        @ loop invariant \separated(pkt,ctx->cfg[curr_cfg].interfaces + (0..(max_iface-1)),
                             &usbotghs_ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num),
                             r_CORTEX_M_USBOTG_HS_GINTMSK, r_CORTEX_M_USBOTG_HS_DAINTMSK, 
                             r_CORTEX_M_USBOTG_HS_DOEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num)  ) ;
        @ loop assigns i, *ctx, errcode, usbotghs_ctx, *r_CORTEX_M_USBOTG_HS_GINTMSK, *r_CORTEX_M_USBOTG_HS_DAINTMSK;
        @ loop variant (max_ep - i) ;

    */

        /*
        
        TODO : completer le loop assign avec des adresses du registre
                *r_CORTEX_M_USBOTG_HS_DIEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num), 
                *r_CORTEX_M_USBOTG_HS_DOEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num)

                comment dire que toute une plage de mémoire est assign? (i varie, au max de 0 à 255)

                La fonction usbotghs_configure_endpoint a été patchée pour ne plus utiliser r_CORTEX_M_USBOTG_HS_DOEPCTL(ep) et r_CORTEX_M_USBOTG_HS_DIEPCTL(ep)
                tant que le probleme d'assigner des plages entières d'adresse mémoire n'a été résolu

        */


        for (uint8_t i = 0; i < max_ep; ++i) {
            usb_backend_drv_ep_dir_t dir;
            if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir == USB_EP_DIR_OUT) {
                dir = USB_BACKEND_DRV_EP_DIR_OUT;
            } else {
                dir = USB_BACKEND_DRV_EP_DIR_IN;
            }
            log_printf("[LIBCTRL] configure EP %d (dir %d)\n", ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num, dir);

            if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].type != USB_EP_TYPE_CONTROL) {          
            //      Cyril : pour avoir errcode == MBED_ERROR_NONE, il faut que usbotghs_context_t *ctx = usbotghs_get_context() soit null
            //      Cyril : ce qui est important c'est d'avoir écrit dans des registres, mais je n'ai pas fait des ensures sur ça dans la fonction  usb_backend_drv_configure_endpoint   
                errcode = usb_backend_drv_configure_endpoint(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num,
                        ctx->cfg[curr_cfg].interfaces[iface].eps[i].type,
                        dir,
                        ctx->cfg[curr_cfg].interfaces[iface].eps[i].pkt_maxsize,
                        USB_BACKEND_EP_ODDFRAME,
                        ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler);
            
                 if (errcode != MBED_ERROR_NONE) {
                    log_printf("[LIBCTRL] unable to configure EP %d (dir %d): err %d\n", ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num, dir, errcode);
                    goto err;
                }
            }
            ctx->cfg[curr_cfg].interfaces[iface].eps[i].configured = true ;
        }

    }


    usbctrl_configuration_set();  // Cyril : la fonction usbctrl_configuration_set() est définie dans un main.c, elle assigne conf_set à true
    usb_backend_drv_send_zlp(0);   // Cyril : il ne faut pas un errcode?
    /* handling standard Request */
    pkt = pkt;
    /*request finish here */
    ctx->ctrl_req_processing = false;
    /*@ assert ctx->state == USB_DEVICE_STATE_CONFIGURED ; */
    /*@ assert errcode == MBED_ERROR_NONE ;  */
    return errcode;
    err:
    usb_backend_drv_stall(0, USB_EP_DIR_OUT);
    /*request finish here */
    ctx->ctrl_req_processing = false;
    /*@ assert errcode == MBED_ERROR_INVPARAM || errcode == MBED_ERROR_INVSTATE ; */
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

/* @
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
    FIXME : 
        - quel degré de détail pour les comportement? Il y a un test sur le retour de la fonction 
            usbctrl_get_descriptor, puis sur maxlength >= size. faut-il faire d'autres behavior pour considérer ces différents cas? (sachant que la fonction send_data est de plus 
            appelée...) + usb_backend_drv_ack

        - de manière générale, quel ensure mettre? ctx->ctrl_req_processing == \false est-il pertinent? et quand je fais appel aux fonctions du driver, est-ce que le résultat de ces fonctions
            doit être spécifié à l'aide d'ensures?

    TODO : les assigns

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
        /*request finish here */
        ctx->ctrl_req_processing = false;
        /*@ assert ctx->ctrl_req_processing == \false ; */
        goto err;
    }
    /* FIXME: we should calculate the maximum descriptor we can genrate and compare
     * to current buffer */

    uint8_t buf[MAX_DESCRIPTOR_LEN] = { 0 };  // Cyril : buf doit être initialisé (bug eva)
    uint32_t size = 0;

    switch (desctype) {
        case USB_REQ_DESCRIPTOR_DEVICE:
            log_printf("[USBCTRL] Std req: get device descriptor\n");
            if (pkt->wIndex != 0) {  
                /*request finish here */
                ctx->ctrl_req_processing = false;  //
                goto err;
            }
            if (maxlength == 0) {  // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch (test if ligne 1946)
                errcode = usb_backend_drv_send_zlp(0);   // Cyril : code mort du coup, confirmé par EVA
                /*request finish here */
                ctx->ctrl_req_processing = false;
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_DEVICE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    log_printf("[USBCTRL] Failure while generating descriptor !!!\n");
                    /*request finish here */
                    ctx->ctrl_req_processing = false;  // cyril : comment arriver ici avec EVA ?
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
            }
            /* read status .... */
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(0), r_CORTEX_M_USBOTG_HS_DOEPCTL(0)) ; */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_CONFIGURATION:
            log_printf("[USBCTRL] Std req: get configuration descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false ; */
                goto err;
            }
            if (maxlength == 0) {  // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch (test if ligne 1946)
                errcode = usb_backend_drv_send_zlp(0);
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_CONFIGURATION, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    /*request finish here */
                    ctx->ctrl_req_processing = false;
                    /*@ assert ctx->ctrl_req_processing == false; */
                    goto err;
                }
                usbctrl_set_state(ctx, USB_DEVICE_STATE_CONFIGURED);
                if (maxlength > size) {
                    errcode = usb_backend_drv_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usb_backend_drv_send_data(&(buf[0]), maxlength, 0);
                    /* should we not inform the host that there is not enough
                     * space ? Well no, the host, send again a new descriptor
                     * request with the correct size in it.
                     * XXX: check USB2.0 standard */
                }
            }
            /* read status .... */
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(0), r_CORTEX_M_USBOTG_HS_DOEPCTL(0)) ; */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);

            /* it is assumed by the USB standard that the returned configuration is now active.
             * From now on, the device is in CONFIGUED state, and the returned configuration is
             * the one currently active */
            break;
        case USB_REQ_DESCRIPTOR_STRING:  // cyril : pas de test sur l'index?
            log_printf("[USBCTRL] Std req: get string descriptor\n");
            if ((errcode = usbctrl_get_descriptor(USB_DESC_STRING, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
                goto err;
            }
            if (maxlength == 0) {    // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch (test if ligne 1946)
                errcode = usb_backend_drv_send_zlp(0);
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
            } else {
                if (maxlength > size) {
                    errcode = usb_backend_drv_send_data(&(buf[0]), size, 0);
                } else {
                    errcode = usb_backend_drv_send_data(&(buf[0]), maxlength, 0);
                    /* should we not inform the host that there is not enough
                     * space ?
                     * XXX: check USB2.0 standard */
                }
            }
            /* read status .... */
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(0), r_CORTEX_M_USBOTG_HS_DOEPCTL(0)) ; */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE:
            /* wIndex (language ID) should be zero */
            log_printf("[USBCTRL] Std req: get interface descriptor\n");
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
                goto err;
            }
            if (maxlength == 0) {     // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch (test if ligne 1946)
                errcode = usb_backend_drv_send_zlp(0);
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_INTERFACE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    // Cyril : comme on est dans le cas USB_DESC_INTERFACE, size == 0, donc on n'entrera jamais dans le test ligne 2074 (else) ; code non atteignable par EVA
                    /*request finish here */
                    ctx->ctrl_req_processing = false;
                    /*@ assert ctx->ctrl_req_processing == \false; */
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
            }
            /* read status .... */
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(0), r_CORTEX_M_USBOTG_HS_DOEPCTL(0)) ; */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_ENDPOINT:
            log_printf("[USBCTRL] Std req: get EP descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
                goto err;
            }
            if ((errcode = usbctrl_get_descriptor(USB_DESC_ENDPOINT, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                // Cyril : comme on est dans le cas USB_DESC_ENDPOINT, size == 0, donc on n'entrera jamais dans le test ligne 2074 (else) ; code non atteignable par EVA
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
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
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_DEVICE_QUALIFIER:
            log_printf("[USBCTRL] Std req: get dev qualifier descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
                goto err;
            }
            /*TODO */
            /*request finish here */
            ctx->ctrl_req_processing = false;
            /*@ assert ctx->ctrl_req_processing == \false; */
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_REQ_DESCRIPTOR_OTHER_SPEED_CFG:
            log_printf("[USBCTRL] Std req: get othspeed descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
                goto err;
            }
            /*TODO */
            /*request finish here */
            ctx->ctrl_req_processing = false;
            /*@ assert ctx->ctrl_req_processing == \false; */
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE_POWER:
            log_printf("[USBCTRL] Std req: get iface power descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                /*@ assert ctx->ctrl_req_processing == \false; */
                goto err;
            }
            /*TODO */
            /*request finish here */
            ctx->ctrl_req_processing = false;
            /*@ assert ctx->ctrl_req_processing == \false; */
            /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            goto err;
            break;
    }

    return errcode;
err:
    /*@ assert \separated(ctx,pkt, r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
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
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns *ctx ;
    @   ensures \result == MBED_ERROR_INVSTATE && ctx->ctrl_req_processing == \false ;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns *pkt, *ctx, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE &&  ctx->ctrl_req_processing == \false ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/


static mbed_error_t usbctrl_std_req_handle_set_descriptor(usbctrl_setup_pkt_t *pkt __attribute__((unused)),
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
        ctx->ctrl_req_processing = false;
        goto err;
    }
    /* handling standard Request */
    /* By now, we do not which to allow the host to set one of our descriptors.
     * As a consequence, we reply a request error to the host, meaning that this
     * behavior is not supported by the device.
     */

    usb_backend_drv_send_zlp(0);
    /*request finish here */
    ctx->ctrl_req_processing = false;
err:
    return errcode;
}

/*@
    @ requires \valid_read(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);
    @ assigns *ctx ;
    @ assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
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

/*
    TODO : les assigns de trop bas niveaux

*/

static mbed_error_t usbctrl_std_req_handle_set_feature(usbctrl_setup_pkt_t *pkt,
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
    ctx->ctrl_req_processing = false;
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);
    @ assigns *ctx ;
    @ assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
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

static mbed_error_t usbctrl_std_req_handle_set_interface(usbctrl_setup_pkt_t *pkt,
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
    if (usbctrl_is_interface_exists(ctx, iface_id) == false) {     // Cyril : EP ou iface?
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
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        default:
            /* this should never be reached with the is_std_requests_allowed() function */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
    }
err:
    ctx->ctrl_req_processing = false;
    return errcode;
}

/*@
    @ requires \valid(ctx) && \valid_read(pkt) ;
    @ requires \separated(ctx,pkt);
    @ assigns *ctx ;
    @ assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
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

static mbed_error_t usbctrl_std_req_handle_synch_frame(usbctrl_setup_pkt_t *pkt,
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
    ctx->ctrl_req_processing = false;
    return errcode;
}


/*
 * Standard requests must be supported by any devices and are handled here.
 * These requests handlers are written above and executed directly by the libusbctrl
 */

/* @
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);

    @ behavior USB_REQ_GET_STATUS:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_STATUS ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_CLEAR_FEATURE:
    @   assumes  pkt->bRequest ==  USB_REQ_CLEAR_FEATURE ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_SET_FEATURE:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_FEATURE ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_SET_ADDRESS:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_ADDRESS ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_GET_DESCRIPTOR:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_DESCRIPTOR ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_SET_DESCRIPTOR:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_DESCRIPTOR ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_GET_CONFIGURATION:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_CONFIGURATION ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_SET_CONFIGURATION:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_CONFIGURATION ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_GET_INTERFACE:
    @   assumes  pkt->bRequest ==  USB_REQ_GET_INTERFACE ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_SET_INTERFACE:
    @   assumes  pkt->bRequest ==  USB_REQ_SET_INTERFACE ;
    @   ensures is_valid_error(\result);

    @ behavior USB_REQ_SYNCH_FRAME:
    @   assumes  pkt->bRequest ==  USB_REQ_SYNCH_FRAME ;
    @   ensures is_valid_error(\result);

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
    FIXME : quel niveau de détail dans les ensures et dans les comportements? spécifier pour chaque fonction les différents comportements possibles? (ce qui revient à copier toutes les spec
            des fonctions non ?)

    TODO : les assigns, mais ça sera fait à la fin quand les assigns de toutes les fonctions seront faits
            il reste : 
                    - 

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
            log_printf("[USBCTRL] Unknown std request %d\n", pkt->bRequest);   // cyril : si on arrive ici, on a quand meme MBED_ERROR_NONE. Est-ce que c'est le comportement attendu?
            /*@ assert \separated(ctx,pkt,&usbotghs_ctx);  */
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
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns *ctx, *pkt ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures ctx->ctrl_req_processing == \false;  

    @ complete behaviors ;
    @ disjoint behaviors ;

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

    /* request finish here */
    ctx->ctrl_req_processing = false;
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
    @ assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(ep_id), *r_CORTEX_M_USBOTG_HS_DOEPCTL(ep_id) ;
    @ ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_INVPARAM || \result == MBED_ERROR_NONE ||  \result == MBED_ERROR_BUSY ;

*/

/*@
    
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);
    @ ensures GHOST_num_ctx == \old(GHOST_num_ctx) ;

    @ behavior std_requests_not_allowed:
    @   assumes !(ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior no_iface:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assumes (((pkt->wIndex) & 0xff) - 1 ) >= ctx->cfg[ctx->curr_cfg].interface_num ;  // condition pour is_interface_exists : iface_idx >= ctx->cfg[ctx->curr_cfg].interface_num
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_NOTFOUND || \result == MBED_ERROR_UNKNOWN ; 

    @ behavior handler_not_found :
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assumes !((((pkt->wIndex) & 0xff) - 1) >= ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes \forall integer i ; 0 <= i < GHOST_num_ctx ==> &(ctx_list[i]) != ctx ;
    @   assigns \nothing ;  
    @   ensures \result == MBED_ERROR_NOTFOUND || \result == MBED_ERROR_INVPARAM ;  

    @ behavior handler_found :
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assumes !((((pkt->wIndex) & 0xff) - 1) >= ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && &(ctx_list[i]) == ctx ;
    @   assigns \nothing ;  
    @   ensures is_valid_error(\result) ;    

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
    CYRIL : cette fonction est une fonction static inline, mais elle n'est appelée par aucune autre fonction...
    comment faire pour l'utiliser alors?
    ici se trouve handle_class_requests

*/

mbed_error_t usbctrl_handle_class_requests(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t   *ctx)
{
    /* @ assert GHOST_num_ctx == num_ctx ; */
    /* @ assert \separated(&GHOST_num_ctx, &num_ctx) ; */
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t iface_idx = 0;
    usbctrl_interface_t* iface = NULL;

    if (!is_class_requests_allowed(ctx)) {
        /* error handling, invalid state */
        /*@ assert ctx->state != USB_DEVICE_STATE_CONFIGURED ; */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* @ assert GHOST_num_ctx == num_ctx ; */
    /* when sending a class request, this should be to a specific interface.
     * Interfaces are identified by their cell number in the interfaces[] table,
     * and declared to the host through the descriptors, through which
     * interfaces are sent in the interfaces[] table order.
     *
     * This permit to delect which interface is targeted by the current
     * request
     * Nota Bene: USB interfaces index start with 1, cells with 0 */
    
    /*
        Cyril : Ajout de ce test (defense en profondeur) pour éviter ce cas lors du calcul de iface_idx
                normalement, cas impossible (interdit dans les specs)

    */

    if((((pkt->wIndex) & 0xff)) == 0 ){   
        /*@ assert ((pkt->wIndex) & 0xff) == 0 ; */ 
        errcode = MBED_ERROR_INVPARAM ;
        goto err ;
    }
    /*@ assert ((pkt->wIndex) & 0xff) != 0 ; */ 
    /*@ assert ((pkt->wIndex) & 0xff) > 0 ; */ 

    iface_idx = (((pkt->wIndex) & 0xff) -1 );  // Cyril : iface_idx : problème d'uint8_t >=0 (rte downcast). 0xff joue le rôle d'un masque, les 8 premiers bits de index sont mis à 0 donc <= 255 ça marche
 /* @ assert GHOST_num_ctx == num_ctx ; */
     if (!usbctrl_is_interface_exists(ctx, iface_idx)) {
        //errcode = MBED_ERROR_NOTFOUND;
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_NOTFOUND;
        goto err;
    }
    /* @ assert GHOST_num_ctx == num_ctx ; */
    if ((iface = usbctrl_get_interface(ctx, iface_idx)) == NULL) {   // je ne peux pas arriver ici après le passage dans usbctrl_is_interface_exists si ça c'est bien passé
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }
    /* interface found, call its dedicated request handler */
    uint32_t handler ;  
    
    /*@ assert \at(GHOST_num_ctx,Here) == \at(GHOST_num_ctx,Pre) ; */
    /* @ assert GHOST_num_ctx == num_ctx ; */
    
    if ((errcode = usbctrl_get_handler(ctx, &handler)) != MBED_ERROR_NONE) {
        /*@ assert \at(GHOST_num_ctx,Here) == \at(GHOST_num_ctx,Pre) ; */
        /*@ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> &(ctx_list[i]) != ctx ; */
        /*@ assert errcode == MBED_ERROR_NOTFOUND || errcode == MBED_ERROR_INVPARAM ;  */
        log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
        goto err ;  // Cyril : ajout pour avoir un retour d'erreur et pour initialiser handler avant d'entrer dans le pointeur de fonction
    }
    /*@ assert \at(GHOST_num_ctx,Here) == \at(GHOST_num_ctx,Pre) ; */
    /*@ assert \exists integer i ; 0 <= i < GHOST_num_ctx && &(ctx_list[i]) == ctx ; */
    if (iface->rqst_handler != NULL) {   // Cyril : ajout d'un test sur la valeur du pointeur de fonction
 
#ifndef __FRAMAC__
    if (handler_sanity_check_with_panic((physaddr_t)iface->rqst_handler)) {
        goto err;
    }
#endif

    /*@ assert iface->rqst_handler ∈ {class_rqst_handler}; */   // Cyril : ne passe pas avec EVA : il manque un test sur le pointeur de fonction : null ou pas...
    /*@ calls class_rqst_handler; */  // Cyril : problem assert Eva: initialization: \initialized(&handler);  à creuser...

    errcode = iface->rqst_handler(handler, pkt); 
    }
err:
    return errcode;
}



/*
 * Fallback. Here the requests is invalid, using a reserved value. an error is
 * returned.
 */

/*@
    @ requires \valid(pkt) && \valid(ctx) ;
    @ requires \separated(ctx,pkt);
    @ assigns *ctx, *pkt, *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @ ensures \result == MBED_ERROR_UNKNOWN ;
*/

static inline mbed_error_t usbctrl_handle_unknown_requests(usbctrl_setup_pkt_t *pkt,
                                                           usbctrl_context_t   *ctx)
{
    ctx = ctx;
    pkt = pkt;
    log_printf("[USBCTRL] Unknown Request type %d/%x\n", pkt->bmRequestType, pkt->bRequest);
    /*@ assert \separated(pkt,ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0),r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)); */
    usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
    return MBED_ERROR_UNKNOWN;
}

/*
 * Global requests dispatcher. This function call the corresponding request handler, get back
 * its error code in return, release the EP0 receive FIFO lock and return the error code.
 *
 */

/* @
    @ behavior bad_pkt:
    @   assumes pkt == \null ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior bad_ctx:
    @   assumes pkt != \null ;
    @   assumes \forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_UNKNOWN ;

    @ behavior USB_REQ_TYPE_STD:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   ensures is_valid_error(\result) ;   // être plus précis quand la fonction usbctrl_handle_std_requests sera correctement spécifiée
    @   assigns ctx_list[0..(GHOST_num_ctx-1)];

    @ behavior USB_REQ_TYPE_VENDOR:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;
    @   ensures (\result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE) ;

    @ behavior USB_REQ_TYPE_CLASS:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;   
    @   assumes ((((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS) || (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE)) ;
    @   ensures is_valid_error(\result) ;   // Cyril : dans l'attente de discuter avec Philippe de errcode et upperstack

    @ behavior UNKNOWN:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) ;
    @   assumes !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;    
    @   assumes !((((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS) || (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE)) ; 
    @   assigns *pkt, ctx_list[0..(GHOST_num_ctx-1)] ;  // cyril : je dois laisser ctx_list[0..(num_ctx-1)], *ctx_list n'est pas validé par WP
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;  
    @   ensures \result == MBED_ERROR_UNKNOWN ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/


/*        

TODO : assigns de std, vendor et class encore à faire (pas validé pour le moment) : je pense que c'est à cause de usbctrl_std_req_get_type et usbctrl_std_req_get_recipient
       gérer le static num_ctx

*/

mbed_error_t usbctrl_handle_requests(usbctrl_setup_pkt_t *pkt,
                                     uint32_t             dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;

    /* Sanitation */
    if (pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        usb_backend_drv_stall(EP0, USB_EP_DIR_OUT);
        goto err;
    }
    /* Detect which context is assocated to current request and set local ctx */
        if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {  
        /* trapped on oepint() from a device which is not handled here ! what ? */
        /*@ assert \separated(pkt,ctx_list + (0..(GHOST_num_ctx-1)),r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
        errcode = MBED_ERROR_UNKNOWN;
        usb_backend_drv_stall(EP0, USB_EP_DIR_OUT);
        /*@ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id ; */  
        goto err;
    }

  /*@ assert \exists integer i; 0 ≤ i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id; */
  /*@ assert \exists integer i; 0 ≤ i < GHOST_num_ctx && ctx == &ctx_list[i]; */ ;

#if defined(__FRAMAC__)
    if ((((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) && (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE)   )  {
#else
    if (   (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_STD)
        && (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE)) {
#endif/*!__FRAMAC__*/

    /*@   assert (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) ;  */
    /*@   assert (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;  */

        //ctx->ctrl_req_processing = true;
        /* For current request of current context, is the current context is a standard
         * request ? If yes, handle localy */
        errcode = usbctrl_handle_std_requests(pkt, ctx);
    } 
    else if (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_VENDOR) {
        /* ... or, is the current request is a vendor request, then handle locally
         * for vendor */
        /*@ assert (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;  */
        ctx->ctrl_req_processing = true;
        /* @ assert \separated(pkt,ctx_list + (0..(num_ctx-1))) ; */
        errcode = usbctrl_handle_vendor_requests(pkt, ctx);
        
        /*@ assert (errcode == MBED_ERROR_INVSTATE || errcode == MBED_ERROR_NONE) ; */

    } else if (   (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_CLASS) || (usbctrl_std_req_get_recipient(pkt) == USB_REQ_RECIPIENT_INTERFACE)) {

    /*@   assert (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS) || (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE) ;  */

        log_printf("[USBCTRL] receiving class Request\n");
        /* ... or, is the current request is a class request or target a dedicated
         * interface, then handle in upper layer*/
        uint8_t curr_cfg = ctx->curr_cfg;
        mbed_error_t upper_stack_err = MBED_ERROR_INVPARAM;  // Cyril c'est errcode qui est important non pour savoir si tout se termine bien?

        /*@
            @ loop invariant 0 <= i <= ctx->cfg[curr_cfg].interface_num ;
            @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(ctx->cfg[curr_cfg].interface_num-1))) ;
            @ loop assigns i, upper_stack_err ;  // Cyril : supposition forte ici que le pointeur de fonction n'a pas d'effet de bord (assigns \nothing)
            @ loop variant (ctx->cfg[curr_cfg].interface_num - i);
        */
        for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interface_num; ++i) {

            if (ctx->cfg[curr_cfg].interfaces[i].rqst_handler) {
                log_printf("[USBCTRL] execute iface class handler\n");
                uint32_t handler;
                if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {  // cyril : il manque pas un break ici aussi? : ajout d'un goto err, sinon pb d'initialisation pour rqst_handler
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

                if ((upper_stack_err = ctx->cfg[curr_cfg].interfaces[i].rqst_handler(handler, pkt)) == MBED_ERROR_NONE) {  // Cyril : mais que devient errcode? c'est lui qui est return à la fin
                    /* upper class handler found, we can leave the loop */
                    break;
                }
            }
        }
        /* fallback if no upper stack class request handler was able to handle the received CLASS request */
        if (upper_stack_err != MBED_ERROR_NONE) {
            /* @ assert \separated(pkt,ctx_list + (0..(num_ctx-1)),r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
            usb_backend_drv_stall(0, USB_EP_DIR_OUT);
        }
    } 
    else {
         //... or unknown, return an error
        /*@ assert ((((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) && (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE) ) ||
         (!(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) && !(((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE) &&
          !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) && !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS)   ) ;   */

        errcode = usbctrl_handle_unknown_requests(pkt, ctx);
        /*@ assert errcode == MBED_ERROR_UNKNOWN ; */
    }
err:
    /* release EP0 recv FIFO */

#if defined(__FRAMAC__)
    //ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;  
/*
    FIXME : RTE car on peut y arriver avec ctx non défini (donc accès mémoire invalide)
*/
#else
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
#endif/*!__FRAMAC__*/

    return errcode;
}