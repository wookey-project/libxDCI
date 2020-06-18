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

static inline usbctrl_req_dir_t usbctrl_std_req_get_dir(usbctrl_setup_pkt_t *pkt)
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

/* @
    @ requires \valid_read(pkt);
    @ assigns \nothing ;
    @ ensures (\result == pkt->wValue >> 8) && is_valid_req_descriptor_type(\result) ;
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
    @ assigns \nothing ;

    @ behavior true :
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   ensures \result == \true ;

    @ behavior false :
    @   assumes !(ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   ensures \result == \false ;

    @ complete behaviors;
    @ disjoint behaviors ;
*/


static inline bool is_class_requests_allowed(usbctrl_context_t *ctx)
{
    if (usbctrl_get_state(ctx) == USB_DEVICE_STATE_CONFIGURED)
    {
        /*@  assert ctx->state ==  USB_DEVICE_STATE_CONFIGURED ; */
        return true;
    }
    /*@ assert ctx->state !=  USB_DEVICE_STATE_CONFIGURED ; */
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
    @   ensures ctx->ctrl_req_processing == \false;   // Cyril :  ne marche pas parce que ctx->ctrl_req_processing est déclaré en volatile bool

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
    /*@ assert ctx->ctrl_req_processing == \false; */   // Cyril :  ne marche pas parce que ctx->ctrl_req_processing est déclaré en volatile bool
err:
    return errcode;
}

/*
    problèmes de cette spec :
        - volatile bool ctrl_req_processing, donc impossible de vérifier un ensure sur ctx->ctrl_req_processing
        - appel à des fonctions backend, qui renvoient à une fonction où je lis ou écris dans des registres dont l'adresse mémoire est fixée : ne passe pas pour Frama
        (peut meme faire planter Frama). Choix de commenter la lecture ou l'écriture dans des registres, mais l'appel aux fonctions backend empechent les assigns d'être
        vérifiés (frama pense que tout est modifié...).
        - ces fonctions backend renvoient un code d'erreur, mais ce n'est pas pris en compte dans la fonction. Cela nécessitera d'être pris en compte dans la spec (ensure \result
         == .... || ...)
        - le state configured n'est pas encore codé
        - conclusion: pour avoir une spec valide, il faut : changer volatile bool en bool, commenter l'appel aux fonctions backend...

*/

/* @
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
    @   assigns *ctx ;    // Cyril : n'est pas prouvé à cause de l'appel à usb_backend_drv_stall
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   // Cyril :  ne marche pas parce que ctx->ctrl_req_processing est déclaré en volatile bool

    @ behavior USB_DEVICE_STATE_ADDRESS_bad_recipient:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assigns *ctx ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   // Cyril :  ne marche pas parce que ctx->ctrl_req_processing est déclaré en volatile bool

    @ behavior USB_DEVICE_STATE_ADDRESS_bad_index:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes ((pkt->wIndex & 0xf) != 0) ;
    @   assigns *ctx ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   // Cyril :  ne marche pas parce que ctx->ctrl_req_processing est déclaré en volatile bool

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_false:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_ENDPOINT) ;
    @   assumes ((pkt->wIndex & 0xf) != EP0) ;
    @   assumes !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0xf)) ;
    @   assigns *ctx ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   // Cyril :  ne marche pas parce que ctx->ctrl_req_processing est déclaré en volatile bool

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_true:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_ENDPOINT) ;
    @   assumes ((pkt->wIndex & 0xf) == EP0) || (\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == (pkt->wIndex & 0xf)) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NONE   ; // je dois ajouter un ensures pour : return the recipient status (2 bytes, or wLength if smaller)

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_other :
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/


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
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            /*request finish here */
            ctx->ctrl_req_processing = false;
            break;
        case USB_DEVICE_STATE_ADDRESS:  // Cyril : comment arriver à cet état ?
            if (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_ENDPOINT &&
                usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);  // j'écris dans des registres...(qui dépendent de DIR_IN ou DIR_OUT). Comment le spécifier avec Frama?
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            if ((pkt->wIndex & 0xf) != 0) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            /* handling get_status() for other cases */
            switch (usbctrl_std_req_get_recipient(pkt)) {
                case USB_REQ_RECIPIENT_ENDPOINT: {
                    /*does requested EP exists ? */
                    uint8_t epnum = pkt->wIndex & 0xf;
                    if (!usbctrl_is_endpoint_exists(ctx, epnum)) {
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
    @ ensures ctx->ctrl_req_processing == \false ;

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

/* @
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @	assigns *ctx;
    @	ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_INVSTATE   ;

    @ behavior USB_DEVICE_STATE_DEFAULT_pktValue_not_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ;
    @   assumes (pkt->wValue != 0) ;
   	@	assigns *r_CORTEX_M_USBOTG_HS_DCFG, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @	assigns *ctx;
    @	ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;
    @	ensures ctx->state == USB_DEVICE_STATE_ADDRESS ;  // non prouvé par wp car pkt->wValue varie entre 0 et 65535...(avec framaC interval)

    @ behavior USB_DEVICE_STATE_DEFAULT_pktValue_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_DEFAULT) ;
    @   assumes (pkt->wValue == 0) ;
    @	assigns *ctx;
    @	ensures ctx->ctrl_req_processing == false ;
   	@	assigns *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS_pktValue_not_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_ADDRESS) ;
    @   assumes (pkt->wValue != 0) ;
    @	assigns *ctx;
    @	ensures ctx->ctrl_req_processing == false ;
   	@	assigns *r_CORTEX_M_USBOTG_HS_DCFG, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS_pktValue_null:
    @   assumes (ctx->state == USB_DEVICE_STATE_ADDRESS) ;
    @   assumes (pkt->wValue == 0) ;
    @	assigns *ctx;
    @	ensures ctx->ctrl_req_processing == false ;
   	@	assigns *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE && ctx->state ==  USB_DEVICE_STATE_DEFAULT ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
   	@	assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
   	@	assigns *ctx;
    @	ensures ctx->ctrl_req_processing == false ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/


// Probleme du framaC interval sur pkt->wValue

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
                ctx->address = pkt->wValue;
                usb_backend_drv_set_address(ctx->address);
            /* @  assert ctx->address == pkt->wValue ;  */   // Cyril : pas prouvé par wp à cause du frama-c interval
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
            }
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

/* @
    @ requires \valid(ctx) && \valid(pkt) ;
    @ requires \separated(ctx,pkt);
    @ assigns \nothing ;

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

// besoin de correctement spécifier send_data, ce que je ne peux pas faire sans correctement spécifier les boucles while

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
    @ assigns *ctx ;
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
    @   ensures ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior configured_false:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue == 0 || pkt->wValue > ctx->num_cfg ) ;
    @   ensures  \result != MBED_ERROR_NONE ==> (\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num &&
                0 <= j <= ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number && ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].type != USB_EP_TYPE_CONTROL) ;
    @   ensures is_valid_error(\result) ;

    @ behavior configured_true:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wValue == 0 || pkt->wValue > ctx->num_cfg ) ;
    @   assumes !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num &&
                0 <= j <= ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number && ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].type != USB_EP_TYPE_CONTROL) ;

    @   ensures \result == MBED_ERROR_NONE ;


    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
    il manque ctx->cfg[curr_cfg].interfaces[i].eps[j].configured == \true  pour behavior NOT_USB_EP_TYPE_CONTROL et USB_EP_TYPE_CONTROL

        @   ensures (ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].configured == \true) ==> (\forall integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j <= ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number)
                ==> (ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].type == USB_EP_TYPE_CONTROL)  ;
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
    /* deactivate previous EPs */
    /* FIXME: for previous potential configuration & interface, deconfigure EPs */
    /* this should be done by detecting any configured EP of any registered iface that is set
     * 'configured' just now */

    //requested_configuration = pkt->wValue;  //Cyril : Problème ici: pkt->wValue est un uint16_t, alors que requested_configuration est un uint8_t

    requested_configuration = 1 ;

    /* sanity on requested configuration */
    if ((requested_configuration == 0) || (requested_configuration > ctx->num_cfg)) {
        log_printf("[USBCTRL] Invalid requested configuration!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    ctx->curr_cfg = requested_configuration - 1;
    uint8_t curr_cfg = ctx->curr_cfg;
    /* activate endpoints... */

    /*@
        @ loop invariant 0 <= iface <= ctx->cfg[curr_cfg].interface_num ;
        @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces +(0..(ctx->cfg[curr_cfg].interface_num-1)));
        @ loop assigns iface, *ctx, errcode ;
        @ loop variant (ctx->cfg[curr_cfg].interface_num - iface) ;
    */

    for (uint8_t iface = 0; iface < ctx->cfg[curr_cfg].interface_num; ++iface) {

    /*@
        @ loop invariant 0 <= i <= ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number ;
        @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number - 1 ))) ;
        @ loop assigns i, *ctx, errcode , *r_CORTEX_M_USBOTG_HS_DIEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num),
        				*r_CORTEX_M_USBOTG_HS_GINTMSK, *r_CORTEX_M_USBOTG_HS_DAINTMSK,
        				*r_CORTEX_M_USBOTG_HS_DOEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num)  ;
        @ loop variant (ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number - i) ;
    */

        for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number; ++i) {
            usb_backend_drv_ep_dir_t dir;
            if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir == USB_EP_DIR_OUT) {
                dir = USB_BACKEND_DRV_EP_DIR_OUT;
            } else {
                dir = USB_BACKEND_DRV_EP_DIR_IN;
            }
            log_printf("[LIBCTRL] configure EP %d (dir %d)\n", ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num, dir);

            if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].type != USB_EP_TYPE_CONTROL) {

                //errcode = MBED_ERROR_NONE ;
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
    usb_backend_drv_send_zlp(0);
    /* handling standard Request */
    pkt = pkt;
    /*request finish here */
    ctx->ctrl_req_processing = false;
    return errcode;
    err:
    usb_backend_drv_stall(0, USB_EP_DIR_OUT);
    /*request finish here */
    ctx->ctrl_req_processing = false;
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
    @ assigns *ctx ;

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

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_bad_index:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_DEVICE ;
    @   assumes (pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_null_length:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_DEVICE ;
    @   assumes !(pkt->wIndex != 0);
    @   assumes pkt->wLength == 0 ;
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_length_not_null:  // en fait il y a un test sur les descripteurs, mais je ne sais pas le spécifier. Donc ce behavior englobe tout
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_DEVICE ;
    @   assumes !(pkt->wIndex != 0);
    @   assumes pkt->wLength != 0 ;
    @   ensures is_valid_error(\result) ;

    @ behavior USB_REQ_DESCRIPTOR_CONFIGURATION_bad_index:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_CONFIGURATION ;
    @   assumes !(pkt->wIndex != 0);
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_null_length:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_CONFIGURATION ;
    @   assumes !(pkt->wIndex != 0);
    @   assumes pkt->wLength == 0 ;
    @   ensures ctx->ctrl_req_processing == \false;
    @   ensures is_valid_error(\result) ;

    @ behavior DESCTYPE_USB_REQ_DESCRIPTOR_DEVICE_length_not_null:  // en fait il y a un test sur les descripteurs, mais je ne sais pas le spécifier. Donc ce behavior englobe tout
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes !(pkt->wLength == 0) ;
    @   assumes (pkt->wValue >> 8) == USB_REQ_DESCRIPTOR_CONFIGURATION ;
    @   assumes !(pkt->wIndex != 0);
    @   assumes pkt->wLength != 0 ;
    @   ensures is_valid_error(\result) ;


    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
Cyril : manque behavior si get_descriptor foire (je ne sais pas comment le dire)
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
                ctx->ctrl_req_processing = false;
                goto err;
            }
            if (maxlength == 0) {  // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch
                errcode = usb_backend_drv_send_zlp(0);   // jamais atteint du coup
                /*request finish here */
                ctx->ctrl_req_processing = false;
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_DEVICE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    log_printf("[USBCTRL] Failure while generating descriptor !!!\n");
                    /*request finish here */
                    ctx->ctrl_req_processing = false;
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
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_CONFIGURATION:
            log_printf("[USBCTRL] Std req: get configuration descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            if (maxlength == 0) {
                errcode = usb_backend_drv_send_zlp(0);
                /*request finish here */
                ctx->ctrl_req_processing = false;
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_CONFIGURATION, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    /*request finish here */
                    ctx->ctrl_req_processing = false;
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
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);

            /* it is assumed by the USB standard that the returned configuration is now active.
             * From now on, the device is in CONFIGUED state, and the returned configuration is
             * the one currently active */
            break;
        case USB_REQ_DESCRIPTOR_STRING:
            log_printf("[USBCTRL] Std req: get string descriptor\n");
            if ((errcode = usbctrl_get_descriptor(USB_DESC_STRING, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            if (maxlength == 0) {
                errcode = usb_backend_drv_send_zlp(0);
                /*request finish here */
                ctx->ctrl_req_processing = false;
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
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE:
            /* wIndex (language ID) should be zero */
            log_printf("[USBCTRL] Std req: get interface descriptor\n");
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            if (maxlength == 0) {
                errcode = usb_backend_drv_send_zlp(0);
                /*request finish here */
                ctx->ctrl_req_processing = false;
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_INTERFACE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    /*request finish here */
                    ctx->ctrl_req_processing = false;
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
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_REQ_DESCRIPTOR_ENDPOINT:
            log_printf("[USBCTRL] Std req: get EP descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            if ((errcode = usbctrl_get_descriptor(USB_DESC_ENDPOINT, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
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
                ctx->ctrl_req_processing = false;
                goto err;
            }
            /*TODO */
            /*request finish here */
            ctx->ctrl_req_processing = false;
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
            ctx->ctrl_req_processing = false;
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            break;
        case USB_REQ_DESCRIPTOR_INTERFACE_POWER:
            log_printf("[USBCTRL] Std req: get iface power descriptor\n");
            /* wIndex (language ID) should be zero */
            if (pkt->wIndex != 0) {
                /*request finish here */
                ctx->ctrl_req_processing = false;
                goto err;
            }
            /*TODO */
            /*request finish here */
            ctx->ctrl_req_processing = false;
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
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @	assigns *ctx ;
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
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);


    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   ensures \result == MBED_ERROR_INVSTATE ;
    @ 	ensures ctx->ctrl_req_processing == \false;
    @ 	assigns *ctx ;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns *pkt, *ctx, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE && ctx->ctrl_req_processing == \false;

    @ complete behaviors ;
    @ disjoint behaviors ;

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
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);

    @ behavior std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @	assigns *ctx;
    @   ensures \result == MBED_ERROR_INVSTATE && ctx->ctrl_req_processing == \false;

    @ behavior std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assigns *pkt, *ctx, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
    @   ensures \result == MBED_ERROR_NONE && ctx->ctrl_req_processing == \false;

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
    @   assigns *pkt, *r_CORTEX_M_USBOTG_HS_DTXFSTS(0), *r_CORTEX_M_USBOTG_HS_DIEPTSIZ(0), *r_CORTEX_M_USBOTG_HS_DSTS, *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) ;
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

/*@
    @ requires \valid(pkt) && \valid(ctx);
    @ requires \separated(ctx,pkt);
    @ assigns *ctx, *pkt ;

    @ behavior USB_REQ_GET_STATUS_std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes  pkt->bRequest ==  USB_REQ_GET_STATUS ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior USB_REQ_GET_STATUS_std_requests_allowed:
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes  pkt->bRequest ==  USB_REQ_GET_STATUS ;
    @   ensures \result == MBED_ERROR_NONE ; // dans status, certains ensures ne sont pas spécifiés, et je pense qu'ils sont importants et doivent être reportés ici

    @ behavior USB_REQ_CLEAR_FEATURE_std_requests_not_allowed:
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes  pkt->bRequest ==  USB_REQ_CLEAR_FEATURE ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior USB_REQ_CLEAR_FEATURE_std_requests_allowed :
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes pkt->bRequest ==  USB_REQ_CLEAR_FEATURE ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_REQ_SET_FEATURE_std_requests_not_allowed :
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes pkt->bRequest ==  USB_REQ_SET_FEATURE ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior USB_REQ_SET_FEATURE_std_requests_allowed :
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes pkt->bRequest ==  USB_REQ_SET_FEATURE ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_REQ_SET_ADDRESS_std_requests_not_allowed :
    @   assumes !((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes pkt->bRequest ==  USB_REQ_SET_ADDRESS ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior USB_REQ_SET_ADDRESS_std_requests_allowed :
    @   assumes ((ctx->state == USB_DEVICE_STATE_DEFAULT) ||
                (ctx->state == USB_DEVICE_STATE_ADDRESS) ||
                (ctx->state == USB_DEVICE_STATE_CONFIGURED)) ;
    @   assumes pkt->bRequest ==  USB_REQ_SET_ADDRESS ;
    @   ensures \result == MBED_ERROR_NONE ;


    @ complete behaviors ;
    @ disjoint behaviors ;

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
    @   ensures ctx->ctrl_req_processing == \false;  // Cyril : ne passe pas à cause du volatile

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


    @ behavior std_requests_not_allowed:
    @   assumes !(ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior no_iface:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assumes (((pkt->wIndex) & 0xff) - 1) >= ctx->cfg[ctx->curr_cfg].interface_num ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_NOTFOUND || \result == MBED_ERROR_UNKNOWN ;  // Cyril : je ne comprends pas pq invstate...

    @ behavior handler:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assumes !((((pkt->wIndex) & 0xff) - 1) >= ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assigns *pkt;
    @   ensures is_valid_error(\result) ;  // errcode = iface->rqst_handler(handler, pkt); ça je ne sais pas ce que ça fait...

    @ complete behaviors ;
    @ disjoint behaviors ;

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
        //errcode = MBED_ERROR_NOTFOUND;
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_NOTFOUND;
        goto err;
    }
    if ((iface = usbctrl_get_interface(ctx, iface_idx)) == NULL) {   // je ne peux pas arriver ici après le passage dans usbctrl_is_interface_exists si ça c'est bien passé
        //errcode = MBED_ERROR_UNKNOWN;
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }
    /* interface found, call its dedicated request handler */
    uint32_t handler;
    if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
        log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
    }
#ifndef __FRAMAC__
    if (handler_sanity_check_with_panic((physaddr_t)iface->rqst_handler)) {
        goto err;
    }
#endif
    errcode = iface->rqst_handler(handler, pkt);
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
    //usbotghs_endpoint_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
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
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior bad_ctx:
    @   assumes pkt != \null ;
    @   assumes \forall integer i ; i <= 0 < num_ctx ==> ctx_list[i].dev_id != dev_id ;  // là je suis bloqué, je ne sais pas comment faire référence à ctx_list
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_UNKNOWN ;

    @ behavior USB_REQ_TYPE_STD:
    @   assumes pkt != \null ;
    @   assumes \exists integer i ; i <= 0 < num_ctx && ctx_list[i].dev_id != dev_id ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assigns *ctx ;  // plutot ctx_list...
    @   ensures ctx->ctrl_req_processing == \true ;
    @   ensures is_valid_error(\result) ;   // être plus précis quand la fonction usbctrl_handle_std_requests sera correctement spécifiée

    @ behavior USB_REQ_TYPE_VENDOR:
    @   assumes pkt != \null ;
    @   assumes \exists integer i ; i <= 0 < num_ctx && ctx_list[i].dev_id != dev_id ;
    @   assumes !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;
    @   assigns *ctx ; // plutot ctx_list...
    @   ensures ctx->ctrl_req_processing == \true ;
    @   ensures \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE ;

    @ behavior USB_REQ_TYPE_CLASS:
    @   assumes pkt != \null ;
    @   assumes \exists integer i ; i <= 0 < num_ctx && ctx_list[i].dev_id != dev_id ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS && ((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE) ;
    @   assigns *pkt ;
        // il manque le reste, comment gérer le pointeur de fonction...

    @ complete behaviors ;
    @ disjoint behaviors ;
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
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {  //Cyril (note à moi) soit ctx null : cas pas possible là..., soit dev_id not found : reprendre les conditions de get_context
        /* trapped on oepint() from a device which is not handled here ! what ? */
        errcode = MBED_ERROR_UNKNOWN;
        usb_backend_drv_stall(EP0, USB_EP_DIR_OUT);
        goto err;
    }

    if (   (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_STD)
        && (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE)) {
        ctx->ctrl_req_processing = true;
        /* For current request of current context, is the current context is a standard
         * request ? If yes, handle localy */
        errcode = usbctrl_handle_std_requests(pkt, ctx);
    } else if (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_VENDOR) {
        ctx->ctrl_req_processing = true;
        /* ... or, is the current request is a vendor request, then handle locally
         * for vendor */
        errcode = usbctrl_handle_vendor_requests(pkt, ctx);
    } else if (   (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_CLASS)
               || (usbctrl_std_req_get_recipient(pkt) == USB_REQ_RECIPIENT_INTERFACE)) {

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

// il manque \forall integer prei ; 0 <= prei < i ==> ctx->cfg[curr_cfg].interfaces[prei].rqst_handler(handler, pkt)) != MBED_ERROR_NONE

        for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interface_num; ++i) {
            if (ctx->cfg[curr_cfg].interfaces[i].rqst_handler) {
                log_printf("[USBCTRL] execute iface class handler\n");
                uint32_t handler;
                if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
                    log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
                }
#ifndef __FRAMAC__
                if (handler_sanity_check((physaddr_t)ctx->cfg[curr_cfg].interfaces[i].rqst_handler)) {
                    goto err;
                }
#endif
                if ((upper_stack_err = ctx->cfg[curr_cfg].interfaces[i].rqst_handler(handler, pkt)) == MBED_ERROR_NONE) {
                    /* upper class handler found, we can leave the loop */
                    break;
                }
            }
        }
        /* fallback if no upper stack class request handler was able to handle the received CLASS request */
        if (upper_stack_err != MBED_ERROR_NONE) {
            usb_backend_drv_stall(0, USB_EP_DIR_OUT);
        }
    } else {
        // ... or unknown, return an error
        errcode = usbctrl_handle_unknown_requests(pkt, ctx);
    }
err:
    /* release EP0 recv FIFO */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;   // Cyril : probleme ici, on peut y arriver avec ctx non défini (donc accès mémoire invalide)
    return errcode;
}
