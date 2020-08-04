/*
 *
 * Copyright 2019 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published
 * the Free Software Foundation; either version 3 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */

#include "generated/devlist.h"
#include "api/libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
#include "usbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl_handlers.h"
#include "usbctrl_requests.h"
#include "usbctrl_descriptors.h"

/*
 * by now, the libusbctrl handle upto 2 USB Ctrl context,
 * which means that an application can handle up to 2 USB blocks
 * with 2 dedicated context that may completely differ.
 *
 */



#if defined(__FRAMAC__)
static   uint8_t num_ctx = 0;

#define MAX_EPx_PKT_SIZE 512
#define RAND_UINT_32 65535
#else
#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX
static volatile uint8_t num_ctx = 0;
volatile usbctrl_context_t    ctx_list[MAX_USB_CTRL_CTX] = { 0 };
#endif/*!__FRAMAC__*/

/*@
    @ requires \separated(&usbotghs_ctx,ctxh+(..));
    @ ensures GHOST_num_ctx == num_ctx ;

    @ behavior bad_ctxh:
    @   assumes ctxh == \null;
    @   assigns GHOST_num_ctx ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @
    @ behavior bad_num_ctx:
    @   assumes num_ctx >= MAX_USB_CTRL_CTX ;
    @   assumes ctxh != \null  ;
    @   assigns GHOST_num_ctx ;
    @   ensures \result == MBED_ERROR_NOMEM ;
    @
    @ behavior bad_dev_id:
    @   assumes num_ctx < MAX_USB_CTRL_CTX ;
    @   assumes ctxh != \null  ;
    @   assumes dev_id != USB_OTG_HS_ID && dev_id != USB_OTG_FS_ID ;
    @   assigns GHOST_num_ctx ;
    @   ensures \result == MBED_ERROR_NOBACKEND ;
    @
    @ behavior ok:
    @   assumes (dev_id == USB_OTG_HS_ID || dev_id == USB_OTG_FS_ID) ;
    @   assumes num_ctx < MAX_USB_CTRL_CTX ;
    @   assumes ctxh != \null ;
    @   assigns *ctxh, num_ctx, usbotghs_ctx, GHOST_num_ctx, ctx_list[\old(num_ctx)]   ;
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_UNKNOWN ;
    @   ensures *ctxh == \old(GHOST_num_ctx) ;
    @   ensures GHOST_num_ctx == \old(GHOST_num_ctx) +1 ;
    @   ensures ctx_list[\old(GHOST_num_ctx)].dev_id == dev_id ;
    @   ensures ctx_list[\at(GHOST_num_ctx,Pre)] == ctx_list[\at(num_ctx,Pre)] ;

    @ complete behaviors;
    @ disjoint behaviors;
*/

mbed_error_t usbctrl_declare(uint32_t dev_id, uint32_t *ctxh)
{
    log_printf("[USBCTRL] declaring USB backend\n");
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t i = 0;

    //@ ghost GHOST_num_ctx = num_ctx ;

    /* sanitiation */
    if (ctxh == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (num_ctx >= MAX_USB_CTRL_CTX) {  // Cyril : == avant, je pense qu'on peut mettre >=
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }

    switch (dev_id) {
        case USB_OTG_HS_ID:
            /*@ assert \separated(&usbotghs_ctx,ctx_list + (0..(GHOST_num_ctx-1))); */
            errcode = usb_backend_drv_declare() ; // Cyril : usbotghs_declare : assigns usbotghs_ctx
            break;
        case USB_OTG_FS_ID:
            /*@ assert \separated(&usbotghs_ctx,ctx_list + (0..(GHOST_num_ctx-1))); */
            errcode = usb_backend_drv_declare() ;
            break;
        default:
            errcode = MBED_ERROR_NOBACKEND;
            goto err;
            break;  // Cyril : jamais atteint à cause du goto
    }


    /*@ assert ctx_list[GHOST_num_ctx] == ctx_list[num_ctx] ; */
    ctx_list[num_ctx].dev_id = dev_id;
    *ctxh = num_ctx;

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
        /*@ assert ctx == &(ctx_list[GHOST_num_ctx]); */
    #else
        volatile usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
    #endif/*!__FRAMAC__*/

    /*@ assert \valid(ctx_list + (0..(GHOST_num_ctx))) ;  */

    num_ctx++;

    //@ ghost GHOST_num_ctx++  ;
    /*@ assert \at(GHOST_num_ctx,Here) == \at(GHOST_num_ctx,Pre)+1 ; */

    /*@ assert \valid(ctx_list + (0..(GHOST_num_ctx-1))) ; */

    /* initialize context */
    ctx->num_cfg = 1;


    /*@
        @ loop invariant 0 <= i <= CONFIG_USBCTRL_MAX_CFG;
        @ loop invariant \valid(ctx->cfg + (0..(CONFIG_USBCTRL_MAX_CFG-1))) ;
        @ loop invariant \valid(ctx_list + (0..(GHOST_num_ctx-1))) ;
        @ loop assigns i , ctx->cfg[0..(CONFIG_USBCTRL_MAX_CFG-1)] ;
        @ loop variant (CONFIG_USBCTRL_MAX_CFG - i);
    */

    for (i = 0; i < CONFIG_USBCTRL_MAX_CFG; ++i) {
        ctx->cfg[i].interface_num = 0;
        ctx->cfg[i].first_free_epid = 1;
    }


    ctx->curr_cfg = 0;

    /*@ assert ctx_list[\at(GHOST_num_ctx,Pre)] == ctx_list[\at(num_ctx,Pre)] ; */
    /*@ assert *ctxh == GHOST_num_ctx-1 ; */   // Cyril : ajout de ces 2 assert pour que les ensures soient prouvés par WP
    /*@ assert ctx_list[GHOST_num_ctx-1].dev_id == dev_id ; */
    /*@ assert \valid(ctx_list + (0..(GHOST_num_ctx-1))) ; */

err:
    return errcode;
}
/*
 * basics for now
 */


/*@
    @ requires 0 <= ctxh < MAX_USB_CTRL_CTX ;
    @ requires GHOST_num_ctx == num_ctx ;
    @ requires \valid(ctx_list + (0..(GHOST_num_ctx-1))) ;

    @ behavior bad_ctxh :
    @   assumes ctxh >= GHOST_num_ctx ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior ok:
    @   assumes ctxh < GHOST_num_ctx ;
    @   assigns ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interfaces[0..(MAX_INTERFACES_PER_DEVICE-1)] ;
    @   assigns ctx_list[ctxh];
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM ;
    @   ensures ctx_list[ctxh].state == USB_DEVICE_STATE_POWERED ;
    @
    @ complete behaviors;
    @ disjoint behaviors;
*/


mbed_error_t usbctrl_initialize(uint32_t ctxh)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }

    /*@ assert \valid(ctx_list + (0..(GHOST_num_ctx-1))) ; */

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #else
        volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/


    //printf("[USBCTRL] initializing automaton\n");

/*
 TODO FRAMA-c : spécifier memset et memcpy...
*/

        /*
            initialisation des struct interface à la main, car frama-c a quelques difficultés avec memset (avec void *)
        */

        /*@
            @ loop invariant 0 <= i <= MAX_INTERFACES_PER_DEVICE ;
            @ loop invariant \valid(ctx->cfg[ctx->curr_cfg].interfaces + (0..(MAX_INTERFACES_PER_DEVICE-1))) ;
            @ loop assigns i, ctx->cfg[ctx->curr_cfg].interfaces[0..(MAX_INTERFACES_PER_DEVICE-1)] ;
            @ loop variant (MAX_INTERFACES_PER_DEVICE - i) ;
        */
        for (uint8_t i = 0; i < MAX_INTERFACES_PER_DEVICE ; ++i ){
            ctx->cfg[ctx->curr_cfg].interfaces[i].id = 0;
            ctx->cfg[ctx->curr_cfg].interfaces[i].usb_class = 0 ;
            ctx->cfg[ctx->curr_cfg].interfaces[i].usb_subclass = 0 ;
            ctx->cfg[ctx->curr_cfg].interfaces[i].usb_protocol = 0 ;
            ctx->cfg[ctx->curr_cfg].interfaces[i].dedicated = false ;
            ctx->cfg[ctx->curr_cfg].interfaces[i].rqst_handler = 0 ;
            ctx->cfg[ctx->curr_cfg].interfaces[i].class_desc_handler = 0 ;
            ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number = 0 ;
            /*@
              @ loop invariant 0 <= j <= MAX_EP_PER_INTERFACE ;
              @ loop invariant \valid(ctx->cfg[ctx->curr_cfg].interfaces[i].eps + (0..(MAX_EP_PER_INTERFACE-1))) ;
              @ loop assigns j, ctx->cfg[ctx->curr_cfg].interfaces[i].eps[0..(MAX_EP_PER_INTERFACE-1)] ;
              @ loop variant (MAX_EP_PER_INTERFACE - j) ;
              */
            for (uint8_t j = 0; j < MAX_EP_PER_INTERFACE; ++j) {
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].type = 0;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].dir = 0;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].attr = 0;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].usage = 0;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].pkt_maxsize = 0;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].handler = NULL;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num = 0;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].poll_interval = 0;
               ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].configured = false;
            }
        }


    /* receive FIFO is not set in the driver. Wait for USB reset */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_NOSTORAGE;
    /* initialize with POWERED. We wait for the first reset event */

    errcode = usbctrl_set_state(ctx, USB_DEVICE_STATE_POWERED); // ajout du errcode =
    /*@ assert ctx->state == USB_DEVICE_STATE_POWERED ; */
    /*@ assert ctx_list[ctxh].state == USB_DEVICE_STATE_POWERED ; */

    /* control pipe recv FIFO is ready to be used */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
    ctx->ctrl_req_processing = false;

    /* default config is 0. In it, first free EP id is 1 */
    ctx->cfg[0].first_free_epid = 1;


end:
    return errcode;
}

/*@
    @ requires \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ;
    @ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),handler,&GHOST_num_ctx);
    @ requires GHOST_num_ctx == num_ctx ;
    @ assigns *handler ;

    @ behavior bad_pointer :
    @   assumes (ctx == \null || handler == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior not_found :
    @   assumes ctx != \null && handler != \null ;
    @   assumes \forall integer i ; 0 <= i < GHOST_num_ctx ==> &(ctx_list[i]) != ctx ;
    @   ensures \result == MBED_ERROR_NOTFOUND ;

    @ behavior found :
    @   assumes ctx != \null && handler != \null ;
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && &(ctx_list[i]) == ctx ;
    @   ensures \result == MBED_ERROR_NONE  ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

mbed_error_t usbctrl_get_handler(usbctrl_context_t *ctx,
                                uint32_t *handler)
{

    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctx == NULL || handler == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }
    /* search */

/*@
        @ loop invariant 0 <= i <= GHOST_num_ctx;
        @ loop invariant \valid_read(ctx) ;
        @ loop invariant \valid(handler);
        @ loop invariant \forall integer prei; 0<=prei<i ==> &(ctx_list[prei]) != ctx;
        @ loop invariant \at(handler,LoopEntry) == \at(handler,LoopCurrent) ;
        @ loop assigns i  ;
        @ loop variant (GHOST_num_ctx - i);
*/

    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (&(ctx_list[i]) == ctx) {
            *handler = i;
            /*@ assert \exists integer i ; 0 <= i < GHOST_num_ctx && &(ctx_list[i]) == ctx ; */
            goto end;
        }
    }

   /*@ assert \at(handler,Here) == \at(handler,Pre) ; */
    /* @ assert \separated(&ctx_list + (0..(GHOST_num_ctx-1)),ctx,handler); */
    /*@ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> &(ctx_list[i]) != ctx ; */

    /*@ assert \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ; */

    errcode = MBED_ERROR_NOTFOUND;
end:
    return errcode;
}


/* @
   	@ requires GHOST_num_ctx == num_ctx ;
   	@ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx,ctx);
    @ requires \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ;
   	@ assigns *ctx, GHOST_idx_ctx;

    @ behavior bad_pointer :
    @   assumes ctx == \null ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior not_found :
    @   assumes ctx != \null ;
    @   assumes !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id) ;
    @   ensures \result == MBED_ERROR_NOTFOUND ;
    @	ensures !(\exists integer i ; 0 <= i < GHOST_num_ctx && *ctx == &ctx_list[i] && GHOST_idx_ctx == i ) ;


    @ behavior found :
    @   assumes ctx != \null ;
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures (\exists integer i ; 0 <= i < GHOST_num_ctx && *ctx == &ctx_list[i] && GHOST_idx_ctx == i ) ;
    @	ensures *ctx == &ctx_list[GHOST_idx_ctx];

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*@
    @ requires GHOST_num_ctx == num_ctx ;
    @ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx);
    @ requires \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ;
    @ assigns *ctx, GHOST_idx_ctx;

    @ behavior bad_pointer :
    @   assumes ctx == \null ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior not_found :
    @   assumes ctx != \null ;
    @   assumes !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id) ;
    @   ensures \result == MBED_ERROR_NOTFOUND ;

    @ behavior found :
    @   assumes ctx != \null ;
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id ;
    @   ensures \exists integer i ; 0 <= i < GHOST_num_ctx && \old(ctx_list[i].dev_id) == device_id && GHOST_idx_ctx==i ;
    @   ensures \result == MBED_ERROR_NONE ;
    @	ensures *ctx == &ctx_list[GHOST_idx_ctx];

    @ complete behaviors ;
    @ disjoint behaviors ;
*/
/* ou ensures ctx_list[GHOST_idx_ctx].dev_id == device_id */

mbed_error_t usbctrl_get_context(uint32_t device_id,
                                 usbctrl_context_t **ctx)
{

    /*@ assert GHOST_num_ctx == num_ctx ; */
    /*@ ghost GHOST_idx_ctx = MAX_USB_CTRL_CTX ; */

    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }
    /* search */


    /*@
        @ loop invariant 0 <= i <= GHOST_num_ctx;
        @ loop invariant \separated(&ctx_list + (0..(GHOST_num_ctx-1)),*ctx,&GHOST_num_ctx);
        @ loop invariant \valid(ctx) ;
        @ loop invariant \forall integer prei; 0<=prei<i ==> ctx_list[prei].dev_id != device_id   ;
        @ loop invariant \at(ctx,LoopEntry) == \at(ctx,LoopCurrent) ;
	    @ loop invariant GHOST_idx_ctx == MAX_USB_CTRL_CTX;
        @ loop assigns i ;
        @ loop variant (GHOST_num_ctx - i);
    */

    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (ctx_list[i].dev_id == device_id) {
            *ctx = (usbctrl_context_t*)&(ctx_list[i]);
            /*@ assert  \exists integer i ; 0 <= i < GHOST_num_ctx && *ctx == &ctx_list[i]; */
            /*@ assert *ctx == &ctx_list[i]; */
            /*@ ghost GHOST_idx_ctx = i ; */
            /*@ assert *ctx == &ctx_list[GHOST_idx_ctx]; */
            goto end;
        }
    }

   /*@ assert \at(ctx,Here) == \at(ctx,Pre) ; */
    /*@ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != device_id ; */
    /*@ assert \separated(&ctx_list + (0..(GHOST_num_ctx-1)),*ctx); */
    /*@ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> &ctx_list[i] != *ctx ; */
    errcode = MBED_ERROR_NOTFOUND;

end:
    return errcode;
}

/*@
    @ requires 0 <= ep <= 255 ;
    @ assigns \nothing ;

    @ behavior bad_ctx:
    @   assumes ctx == \null ;
    @   ensures \result == \false ;

    @ behavior EP_not_found:
    @   assumes ctx != \null ;
    @   assumes ep != EP0 ;
    @   assumes !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep) ;
    @   ensures \result == \false;

    @ behavior EP_found:
    @   assumes ctx != \null ;
    @   assumes (\exists  integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                     ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep) || ep == EP0 ;
    @   ensures \result == \true ;

    @ complete behaviors;
    @ disjoint behaviors;
*/

bool usbctrl_is_endpoint_exists(usbctrl_context_t *ctx, uint8_t ep)
{
    uint8_t i = 0 ;
    uint8_t j = 0 ;

    /*@ assert GHOST_num_ctx == num_ctx ; */

    /* sanitize */
    if (ctx == NULL) {
        return false;
    }

    if (ep == EP0) {
        return true;
    }

/*@
        @ loop invariant 0 <= i <= ctx->cfg[ctx->curr_cfg].interface_num ;
        @ loop invariant \valid_read(ctx->cfg[ctx->curr_cfg].interfaces + (0..(ctx->cfg[ctx->curr_cfg].interface_num-1))) ;
        @ loop invariant \valid_read(ctx->cfg[ctx->curr_cfg].interfaces[i].eps + (0..(ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number-1))) ;
        @ loop invariant (\forall integer prei; 0<=prei<i ==>(\forall integer jj;
            0 <= jj < ctx->cfg[ctx->curr_cfg].interfaces[prei].usb_ep_number ==>  ctx->cfg[ctx->curr_cfg].interfaces[prei].eps[jj].ep_num != ep));
        @ loop assigns i, j ;
        @ loop variant (ctx->cfg[ctx->curr_cfg].interface_num - i);
*/

    for (i = 0; i < ctx->cfg[ctx->curr_cfg].interface_num; ++i) {

/*@
        @ loop invariant 0 <= j <= ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number ;
        @ loop invariant \valid_read(ctx->cfg[ctx->curr_cfg].interfaces + (0..(ctx->cfg[ctx->curr_cfg].interface_num-1))) ;
        @ loop invariant \valid_read(ctx->cfg[ctx->curr_cfg].interfaces[i].eps + (0..(ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number-1))) ;
        @ loop invariant (\forall integer prej ; 0<=prej<j ==> ctx->cfg[ctx->curr_cfg].interfaces[i].eps[prej].ep_num != ep) ;
        @ loop assigns j ;
        @ loop variant (ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number - j);
*/

        for ( j = 0; j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number; ++j) {
            if (ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep) {
                return true;
            }
        }
    }
    /*@ assert GHOST_num_ctx == num_ctx ; */
    return false;
}


/*@
    @ requires 0 <= iface <= 255 ;
    @ assigns \nothing ;

    @ behavior bad_ctx:
    @   assumes ctx == \null ;
    @   ensures \result == \false ;

    @ behavior iface_false:
    @   assumes ctx != \null ;
    @   assumes iface >= ctx->cfg[ctx->curr_cfg].interface_num ;
    @   ensures \result == \false ;

    @ behavior true :
    @   assumes ctx != \null ;
    @   assumes !(iface >= ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   ensures \result == \true ;

    @ complete behaviors;
    @ disjoint behaviors;
*/


bool usbctrl_is_interface_exists(usbctrl_context_t *ctx, uint8_t iface)
{

	//@ assert GHOST_num_ctx == num_ctx ;
    /* sanitize */
    if (ctx == NULL) {
        return false;
    }

    if (iface < ctx->cfg[ctx->curr_cfg].interface_num) {
        return true;
    }
    return false;
}

/*@
    @ requires 0 <= iface <= 255 ;
    @ assigns \nothing ;

    @ behavior bad_ctx:
    @   assumes ctx == \null ;
    @   ensures \result == \null ;

    @ behavior iface_null:
    @   assumes ctx != \null ;
    @   assumes iface >= ctx->cfg[ctx->curr_cfg].interface_num ;
    @   ensures \result == \null ;

    @ behavior iface_ok :
    @   assumes ctx != \null ;
    @   assumes !(iface >= ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   ensures \result == &(ctx->cfg[ctx->curr_cfg].interfaces[iface]) ;

    @ complete behaviors;
    @ disjoint behaviors;
*/

usbctrl_interface_t* usbctrl_get_interface(usbctrl_context_t *ctx, uint8_t iface)
{
    /* sanitize */
    //@ assert GHOST_num_ctx == num_ctx ;
    if (ctx == NULL) {
        return NULL;
    }

    if (iface < ctx->cfg[ctx->curr_cfg].interface_num) {
        return &(ctx->cfg[ctx->curr_cfg].interfaces[iface]);
    }
    return NULL;
}

/*
 * Here we declare a new USB interface for the given context.
 */

/*@
    @ requires \separated(&usbotghs_ctx,iface+(..));
    @ requires 0 <= ctxh ;
    @ requires GHOST_num_ctx == num_ctx ;
    @ ensures GHOST_num_ctx == num_ctx ;

    @ behavior bad_ctxh :
    @   assumes ctxh >= num_ctx ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior invalid_iface :
    @   assumes iface == \null ;
    @   assumes ctxh < num_ctx ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior too_many_interfaces :
    @   assumes ctxh < num_ctx ;
    @   assumes iface != \null ;
    @   assumes ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NOMEM ;

    @ behavior too_many_config :
    @   assumes ctxh < num_ctx ;
    @   assumes iface != \null;
    @   assumes !(ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) ;
    @   assumes (iface->dedicated  == true) && (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num != 0 ) ;
    @   assumes (ctx_list[ctxh].num_cfg +1 ) > (CONFIG_USBCTRL_MAX_CFG-1) ;
    @   assigns ctx_list[ctxh] ;
    @   ensures \result == MBED_ERROR_NOMEM ;

    @ behavior ok :
    @   assumes ctxh < num_ctx ;
    @   assumes iface != \null ;
    @   assumes !(ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) ;
    @   assumes (iface->dedicated  == true) && (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num != 0 ) && (ctx_list[ctxh].num_cfg < (MAX_USB_CTRL_CTX-1))
                ||(iface->dedicated  != true) || (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num == 0 )  ;
    @   assigns *iface, ctx_list[ctxh] ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors;
    @ disjoint behaviors;

*/

mbed_error_t usbctrl_declare_interface(__in     uint32_t ctxh,
                                       __out    usbctrl_interface_t  *iface)
{
    uint8_t iface_config = 0;
    uint8_t i = 0 ;
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t drv_ep_mpsize ;

//@ assert GHOST_num_ctx == num_ctx ;

    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (iface == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;               // Cyril : ajout du goto
    }

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #else
        volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/

    /* check space */
    if (ctx->cfg[ctx->curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) {   // Cyril : modif par rapport à avant ==
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }

    if (iface->dedicated == true && ctx->cfg[ctx->curr_cfg].interface_num != 0) {
            /*
                Cyril : ajout d'un test sur le nombre de config max :
                check space
            */

    	ctx->num_cfg++;

        if(ctx->num_cfg > (CONFIG_USBCTRL_MAX_CFG - 1)){
            errcode = MBED_ERROR_NOMEM;
            goto err;
        }

        iface_config = ctx->num_cfg;    // Cyril : je ne peux pas arriver ici avec CONFIG_USBCTRL_MAX_CFG == 2
        ctx->cfg[iface_config].first_free_epid = 1;
    } else {
        iface_config = ctx->curr_cfg;
    }


    /*
    Cyril : code mort selon moi : soit iface_config = ctx->num_cfg +1 , qui est < MAX_USB_CTRL_CTX d'après le test précédent
                                  soit iface_config = ctx->curr_cfg, qui est forcément < MAX_USB_CTRL_CTX

    if (iface_config >= MAX_USB_CTRL_CTX) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    */

    /* iface identifier in target configuration */
    uint8_t iface_num = ctx->cfg[iface_config].interface_num;

    /* let's register */
   //log_printf("declaring new interface class %x, %d EPs in Cfg %d/%d\n", iface->usb_class, iface->usb_ep_number, iface_config, iface_num);
   /* 1) make a copy of interface. The interface identifier is its cell number  */

    #if defined(__FRAMAC__)
    /*
        en attendant de définir correctement memcpy avec frama-c, je copie manuellement la struct iface dans ctx->cfg[iface_config].interfaces[iface_num]
        les paramètres copiés sont ceux définis dans la struct iface dans le main... (donc c'est un exemple pour passer le code à frama-c)
    */
       ctx->cfg[iface_config].interfaces[iface_num].usb_class = iface->usb_class ;
       ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number = iface->usb_ep_number ;
       ctx->cfg[iface_config].interfaces[iface_num].dedicated = iface->dedicated ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].type = iface->eps[0].type ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].dir = iface->eps[0].dir ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].pkt_maxsize = iface->eps[0].pkt_maxsize ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].handler = iface->eps[0].handler ;
       ctx->cfg[iface_config].interfaces[iface_num].rqst_handler = iface->rqst_handler ;
       ctx->cfg[iface_config].interfaces[iface_num].class_desc_handler = iface->class_desc_handler ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].poll_interval = iface->eps[0].poll_interval ;

    #else
        memcpy((void*)&(ctx->cfg[iface_config].interfaces[iface_num]), (void*)iface, sizeof(usbctrl_interface_t));
    #endif/*!__FRAMAC__*/

   /* 2) set the interface identifier */
   ctx->cfg[iface_config].interfaces[iface_num].id = iface_num;
   iface->id = iface_num;
   uint8_t max_ep = ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number ;  // cyril : ajout de la variable
   /* 3) or, depending on the interface flags, add it to current config or to a new config */
   /* at declaration time, all interface EPs are disabled  and calculate EP identifier for the interface */


/*@
    @ loop invariant 0 <= i <= max_ep ;
    @ loop invariant \valid(ctx->cfg[iface_config].interfaces[iface_num].eps +(0..(max_ep-1))) ;
    @ loop invariant \valid(iface->eps+(0..(max_ep-1))) ;
    @ loop invariant \separated(ctx->cfg[iface_config].interfaces[iface_num].eps +(0..(max_ep-1)),iface->eps+(0..(ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number-1)));
    @ loop assigns i, *iface, drv_ep_mpsize, ctx_list[ctxh] ;
    @ loop variant (max_ep - i) ;
*/

   for (i = 0; i < max_ep; ++i) {

    #if defined(__FRAMAC__)

    // Cyril : je n'utilise pas usb_ep_infos_t *ep = &(ctx->cfg[iface_config].interfaces[iface_num].eps[i]) ; parce que wp ne valide pas le assigns de la fonction
    // je ne sais pas pq...
        ctx->cfg[iface_config].interfaces[iface_num].eps[i].configured = false ;
        /* @ assert ctx_list[ctxh].cfg[iface_config].interfaces[iface_num].eps[i].configured == \false ; */

       if (ctx->cfg[iface_config].interfaces[iface_num].eps[i].type == USB_EP_TYPE_CONTROL) {
           printf("declare EP (control) id 0\n");
           ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num = 0;
           iface->eps[i].ep_num = 0;
       } else {
        ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num = ctx->cfg[iface_config].first_free_epid;
           iface->eps[i].ep_num = ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num;
           printf("declare EP (not control) id %d\n", ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num);
           ctx->cfg[iface_config].first_free_epid++;
           /* FIXME: max EP num must be compared to the MAX supported EP num at driver level */
           /* check that declared ep mpsize is compatible with backend driver */

           /*@ assert \separated(iface,ctx,&usbotghs_ctx); */
           drv_ep_mpsize = usb_backend_get_ep_mpsize();

           if (ctx->cfg[iface_config].interfaces[iface_num].eps[i].pkt_maxsize > drv_ep_mpsize) {
               log_printf("truncating EP max packet size to backend driver EP max pktsize\n");
               ctx->cfg[iface_config].interfaces[iface_num].eps[i].pkt_maxsize = drv_ep_mpsize;
           }
       }

    #else
        volatile usb_ep_infos_t *ep = &(ctx->cfg[iface_config].interfaces[iface_num].eps[i]) ;
        ep->configured = false;

       if (ep->type == USB_EP_TYPE_CONTROL) {
           printf("declare EP (control) id 0\n");
           ep->ep_num = 0;
           iface->eps[i].ep_num = 0;
       } else {
        ep->ep_num = ctx->cfg[iface_config].first_free_epid;
           iface->eps[i].ep_num = ep->ep_num;
           printf("declare EP (not control) id %d\n", ep->ep_num);
           ctx->cfg[iface_config].first_free_epid++;
           /* FIXME: max EP num must be compared to the MAX supported EP num at driver level */
           /* check that declared ep mpsize is compatible with backend driver */

           drv_ep_mpsize = usb_backend_get_ep_mpsize();

           if (ep->pkt_maxsize > drv_ep_mpsize) {
               log_printf("truncating EP max packet size to backend driver EP max pktsize\n");
               ep->pkt_maxsize = drv_ep_mpsize;
           }
       }

    #endif/*!__FRAMAC__*/

   }

   /* 4) now that everything is Okay, consider iface registered */
   ctx->cfg[iface_config].interface_num++;
   /* 5) iface EPs should be configured when receiving setConfiguration or SetInterface */
err:
   return errcode;
}

/*
 * Libctrl is a device-side control plane, the device is configured in device mode
 */

/*@
    @ requires GHOST_num_ctx == num_ctx ;
    @ ensures GHOST_num_ctx == num_ctx ;

    @ behavior bad_ctxh :
    @   assumes ctxh >= GHOST_num_ctx ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior other :
    @   assumes ctxh < GHOST_num_ctx ;
    @	assigns usbotghs_ctx ;
    @	assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), ctx_list[ctxh] ;
    @   ensures is_valid_error(\result) ;

    @ complete behaviors ;
    @ disjoint behaviors ;


*/

/*
    TODO : specifier plus en détail avec configure et set_recv_fifo
            problème : la spec de usbotghs_configure est pas très précise, car usbotghs_ulpi_reset, usbotghs_initialize_core, usbotghs_initialize_host et usbotghs_initialize_device
            Question : est-ce que ça vaut le coup de spécifier le driver à fond?

*/

mbed_error_t usbctrl_start_device(uint32_t ctxh)
{


    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }

    #if defined(__FRAMAC__)
    usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #else
     volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/


#ifndef __FRAMAC__
    ADD_LOC_HANDLER(usbctrl_handle_inepevent)
    ADD_LOC_HANDLER(usbctrl_handle_outepevent)
#endif


    log_printf("[USBCTRL] configuring backend driver\n");
    //PMO
    /* @ assert usbotghs_ctx.in_eps[0].mpsize ==0 ;*/

    if ((errcode = usb_backend_drv_configure(USB_BACKEND_DRV_MODE_DEVICE, usbctrl_handle_inepevent, usbctrl_handle_outepevent)) != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] failed while initializing backend: err=%d\n", errcode);
        usbctrl_set_state(ctx, USB_DEVICE_STATE_INVALID);
        goto end;
    }


    /* Initialize EP0 with first FIFO. Should be reconfigued at Reset time */
    if ((errcode = usb_backend_drv_set_recv_fifo((uint8_t*)&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0)) != MBED_ERROR_NONE) {
        printf("[USBCTRL] failed to initialize EP0 FIFO!\n");
        goto end;
    }


end:

    return errcode;
}

/*@
    @ requires GHOST_num_ctx == num_ctx ;
    @ ensures GHOST_num_ctx == num_ctx ;

    @ ensures (ctxh >= GHOST_num_ctx)  ==> (\result == MBED_ERROR_INVPARAM) ;
    @ ensures (ctxh < GHOST_num_ctx) ==> (\result == MBED_ERROR_NONE) ;
    @ assigns ctx_list[ctxh];
*/

mbed_error_t usbctrl_stop_device(uint32_t ctxh)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    #if defined(__FRAMAC__)
    usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #else
    volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/

    ctx = ctx;
    /* FIXME: TODO */
err:
    return errcode;
}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


/* Implémentation des fonctions et du main permettant d'exécuter FRAMA-C sur les fonctions définies dans usbctrl.c */


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


#if defined(__FRAMAC__)
/*
 * Support for Frama-C testing
 */

//@ assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
void Frama_C_update_entropy_8(void) {
  Frama_C_entropy_source_8 = Frama_C_entropy_source_8;
}

//@ assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
void Frama_C_update_entropy_16(void) {
  Frama_C_entropy_source_16 = Frama_C_entropy_source_16;
}

//@ assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
void Frama_C_update_entropy_32(void) {
  Frama_C_entropy_source_32 = Frama_C_entropy_source_32;
}

/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */

uint8_t Frama_C_interval_8(uint8_t min, uint8_t max)
{
  uint8_t r,aux;
  Frama_C_update_entropy_8();
  aux = Frama_C_entropy_source_8;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */

uint16_t Frama_C_interval_16(uint16_t min, uint16_t max)
{
  uint16_t r,aux;
  Frama_C_update_entropy_16();
  aux = Frama_C_entropy_source_16;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */

uint32_t Frama_C_interval_32(uint32_t min, uint32_t max)
{
  uint32_t r,aux;
  Frama_C_update_entropy_32();
  aux = Frama_C_entropy_source_32;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*

 test_fcn_usbctrl : test des fonctons définies dans usbctrl.c avec leurs paramètres
 					correctement définis (pas de débordement de tableaux, pointeurs valides...)

*/

void test_fcn_usbctrl(){


    uint32_t dev_id = (uint32_t)Frama_C_interval_32(0,4294967295) ;
    uint32_t size = Frama_C_interval_32(0,4294967295) ;
    uint32_t handler ;
    uint8_t ep = Frama_C_interval_8(0,255);
    uint8_t iface = Frama_C_interval_8(0,MAX_INTERFACES_PER_DEVICE-1);
    uint8_t ep_number = Frama_C_interval_8(0,MAX_EP_PER_INTERFACE);
    uint8_t EP_type = Frama_C_interval_8(0,3);
    uint8_t EP_dir = Frama_C_interval_8(0,1);
    uint8_t USB_class = Frama_C_interval_8(0,17);
    uint32_t USBdci_handler = Frama_C_interval_32(0,4294967295) ;
    usb_device_trans_t transition = Frama_C_interval_8(0,MAX_TRANSITION_STATE-1) ;
    usb_device_state_t current_state = Frama_C_interval_8(0,9);
    usbctrl_request_code_t request = Frama_C_interval_8(0x0,0xc);
    uint8_t interval = Frama_C_interval_8(0,255);
    //uint8_t class_descriptor_size = Frama_C_interval_8(0,255);




/*
    def d'une nouvelle interface pour test de la fonction usbctrl_declare_interface
    Déclaration d'une structure usb_rqst_handler_t utilisée dans les interfaces, qui nécessite aussi une structure usbctrl_setup_pkt_t
*/

    uint8_t RequestType = Frama_C_interval_8(0,255);
    uint8_t Request = Frama_C_interval_8(0,0xd);
    uint16_t Value = Frama_C_interval_16(0,65535);
    uint16_t Index = Frama_C_interval_16(0,65535);
    uint16_t Length = Frama_C_interval_16(0,65535);

    usbctrl_interface_t iface_1 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep, .eps[0].poll_interval = interval ,
                                  .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor};

    usbctrl_interface_t iface_2 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep, .eps[0].poll_interval = interval ,
                                  .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor};

    usbctrl_interface_t iface_3 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = false,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep, .eps[0].poll_interval = interval};

    usbctrl_setup_pkt_t pkt = { .bmRequestType = RequestType, .bRequest = Request, .wValue = Value, .wIndex = Index, .wLength = Length };
    usbctrl_context_t *ctx1 = NULL;
    usbctrl_context_t *ctx2 = NULL;

    uint32_t ctxh1=0;
    uint32_t ctxh2=0;



    ///////////////////////////////////////////////////
    //        premier context
    ///////////////////////////////////////////////////

    usbctrl_declare(6, &ctxh1);
    //@ assert GHOST_num_ctx == num_ctx ;
    /*@ assert num_ctx == 1 ; */
    /*@ assert ctxh1 == 0 ; */
    usbctrl_initialize(ctxh1);
    /*@ assert ctxh1 == 0 ; */
    //@ assert GHOST_num_ctx == num_ctx ;
    usbctrl_get_context(6, &ctx1);

    //usbctrl_get_context(dev_id, &ctx1);

    usbctrl_declare_interface(ctxh1, &iface_1) ;
    usbctrl_declare_interface(ctxh1, &iface_2);
    //usbctrl_declare_interface(ctxh1, &iface_3);  // Cyril : le temps de calcul augmente exponentiellement avec une 3ème interface, à cause de la fonction usbctrl_get_descriptor (toutes les boucles...)
    usbctrl_get_interface(ctx1, iface);
    usbctrl_get_handler(ctx1, &handler);
    usbctrl_is_interface_exists(ctx1, iface);
    usbctrl_is_endpoint_exists(ctx1, ep);
    //@ assert GHOST_num_ctx == num_ctx ;
    usbctrl_start_device(ctxh1) ;
    //@ assert GHOST_num_ctx == num_ctx ;
    usbctrl_stop_device(ctxh1) ;
    //@ assert GHOST_num_ctx == num_ctx ;

    if(ctx1 != NULL){
        ctx1->state = Frama_C_interval_8(0,9); // pour EVA, pour avoir tous les états possibles
            usbctrl_is_valid_transition(ctx1->state,transition,ctx1);
            usbctrl_handle_class_requests(&pkt,ctx1) ;
    }


    ///////////////////////////////////////////////////
    //        2nd context
    ///////////////////////////////////////////////////

    usbctrl_declare(7, &ctxh2);
    usbctrl_initialize(ctxh2);
    //@ assert GHOST_num_ctx == num_ctx ;
    usbctrl_get_context(7, &ctx2);
    usbctrl_get_handler(ctx2, &handler);
    usbctrl_declare_interface(ctxh2, &iface_1) ;
    usbctrl_declare_interface(ctxh2, &iface_2);
    //usbctrl_declare_interface(ctxh2, &iface_3);
    usbctrl_get_interface(ctx2, iface);

    usbctrl_is_interface_exists(ctx2, iface);
    usbctrl_is_endpoint_exists(ctx2, ep);
    // @ assert GHOST_num_ctx == num_ctx ;
    usbctrl_start_device(ctxh2) ;
    // @ assert GHOST_num_ctx == num_ctx ;

    /*@ assert ctx2 != 0 ; */
     usb_device_state_t state = usbctrl_get_state(ctx2);
     /*@ assert state == ctx2->state ; */

    usbctrl_stop_device(ctxh2) ;

    if(ctx2 != NULL){
        ctx2->state = Frama_C_interval_8(0,9); // pour EVA, pour avoir tous les états possibles
        usbctrl_is_valid_transition(ctx2->state,transition,ctx2);
        usbctrl_handle_class_requests(&pkt,ctx2) ;
    }

    //////////////////////////////////////////////////////////////////////////////
    //        fonctions qui vont utiliser les deux contextes (inepevent et outepevent)
    //////////////////////////////////////////////////////////////////////////////

    ctx_list[0].ctrl_req_processing = true;  // pour atteindre un cas avec EVA
    usbctrl_handle_inepevent(dev_id, size, ep);

    usbotghs_ctx.out_eps[0].state = Frama_C_interval_8(0,9); // pour EVA, pour avoir tous les états possibles, mais que pour les ep pour lesquels il n'y a pas de RTE dans  usbotghs_ctx.out_eps[ep]
    usbctrl_handle_outepevent(dev_id, size, ep);
    usbctrl_handle_earlysuspend(dev_id) ;
    usbctrl_handle_usbsuspend(dev_id);
    usbctrl_handle_wakeup(dev_id) ;
    usbctrl_std_req_get_dir(&pkt) ;
    usbctrl_handle_reset(dev_id);

    usbctrl_next_state(current_state,request);  // requires is_valid_state && is_valid_request : pas de test d'erreur sur les entrées du coup
    //usbctrl_handle_requests(&pkt, dev_id) ;
    //SIZE_DESC_FIXED = 100 ;
    usbctrl_handle_requests(&pkt, dev_id) ;  // fonction qui appelle bcp de fonction, EVA prend bcp de temps du coup
   	// c'est l'appel à usbctrl_handle_std_requests qui appelle notamment usbctrl_std_req_handle_get_descriptor qui augmente le temps de calcul (x10...)
   	// car usbctrl_std_req_handle_get_descriptor est appelé 5 fois...donc 2 contexte, ça fait 10 fois en tout, et il y a 12000 états dans get descriptor
}

/*

 test_fcn_erreur : test des fonctons définies dans usbctrl.c afin d'atteindre les portions de code défensif
                    (pointeurs nulls, débordement de tableaux...)

*/

void test_fcn_usbctrl_erreur(){

    uint32_t dev_id =(uint32_t) Frama_C_interval_32(0,4294967295) ;
    uint32_t size = Frama_C_interval_32(0,4294967295) ;
    uint32_t ctxh = Frama_C_interval_32(0,4294967295);
    uint32_t handler = Frama_C_interval_32(0,4294967295);
    uint8_t ep = Frama_C_interval_8(0,255);
    uint8_t iface = Frama_C_interval_8(0,MAX_INTERFACES_PER_DEVICE-1);
    uint8_t ep_number = Frama_C_interval_8(0,MAX_EP_PER_INTERFACE);
    uint8_t EP_type = Frama_C_interval_8(0,3);
    uint8_t EP_dir = Frama_C_interval_8(0,1);
    uint8_t  USB_class = Frama_C_interval_8(0,17);
    uint32_t USBdci_handler = Frama_C_interval_32(0,4294967295) ;

/*
    def d'une nouvelle interface pour test de la fonction usbctrl_declare_interface
    Déclaration d'une structure usb_rqst_handler_t utilisée dans les interfaces, qui nécessite aussi une structure usbctrl_setup_pkt_t
*/

    uint8_t RequestType = Frama_C_interval_8(0,255);
    uint8_t Request = Frama_C_interval_8(0,255);
    uint16_t Value = Frama_C_interval_16(0,65535);
    uint16_t Index = Frama_C_interval_16(0,65535);
    uint16_t Length = Frama_C_interval_16(0,65535);

    usbctrl_setup_pkt_t pkt = { .bmRequestType = RequestType, .bRequest = Request, .wValue = Value, .wIndex = Index, .wLength = Length };
    usbctrl_interface_t iface_1 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = NULL,
                                  .rqst_handler = NULL, .class_desc_handler = NULL};
    usbctrl_interface_t iface_2 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = NULL,
                                   .rqst_handler = NULL, .class_desc_handler = NULL};

/*
    ctx_test : context different de ctx_list, pour trigger certains cas dans get_handler
*/
    usbctrl_context_t ctx_test = { .dev_id = 8, .address= 2};

    /*
        usbctrl_declare : cas d'erreur - pointeur ctxh null
                                       - num_ctx >= 2
                        deux appels à la fonction pour tester ces cas d'erreur
    */

    uint32_t *bad_ctxh = NULL;
    usbctrl_declare(dev_id, bad_ctxh);

    ctxh = 1 ;
    num_ctx = 2;
    //@ ghost GHOST_num_ctx = num_ctx ;
    usbctrl_declare(dev_id, &ctxh);



    /*
        usbctrl_declare : cas d'erreur : ctxh >= num_ctx
    */

    ctxh = 0 ;
    num_ctx = 1 ;
    //@ ghost  GHOST_num_ctx = num_ctx ;
    usbctrl_initialize(ctxh);


    ctxh = 1 ;
    num_ctx = 0 ;
    //@ ghost  GHOST_num_ctx = num_ctx ;
    usbctrl_declare(8, &ctxh);  // pour tester dev_id !=6 et != 7
    usbctrl_initialize(ctxh);

    /*
        usbctrl_declare_interface : cas d'erreur - ctxh >= num_ctx
                                                 - pointeur iface == null
                                                 - interface_num >= MAX_INTERFACES_PER_DEVICE
                                                 - pkt_maxsize > usbotghs_get_ep_mpsize()
        Dans le cas nominal, avec le test sur 2 interfaces, num_cfg >= MAX_USB_CTRL_CTX-1 donc une partie du code n'est pas atteinte. Cas traité ci-dessous, quand on rajoute
        une interface de contrôle
    */


    ctxh = 2 ;
    num_ctx = 1 ;
    //@ ghost  GHOST_num_ctx = num_ctx ;
    usbctrl_declare_interface(ctxh, &iface_1) ;

    ctxh = 0 ;
    num_ctx = 1 ;
    usbctrl_interface_t *iface_null = NULL ;
    usbctrl_declare_interface(ctxh, iface_null) ;

    usbctrl_interface_t iface_3 = {.usb_class = 0, .usb_ep_number = 2, .dedicated = true, .eps[0].type = 3, .eps[0].pkt_maxsize = MAX_EPx_PKT_SIZE + 1 };
    ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE ;
    usbctrl_declare_interface(ctxh, &iface_3) ;

    usbctrl_interface_t iface_4 = {.usb_class = 0, .usb_ep_number = 2, .dedicated = false, .eps[0].type = 3, .eps[0].pkt_maxsize = MAX_EPx_PKT_SIZE + 1 };
    ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE - 1 ;
    //ctx_list[ctxh].cfg[0].interfaces[0].eps[0].pkt_maxsize = MAX_EPx_PKT_SIZE + 1 ;
    usbctrl_declare_interface(ctxh, &iface_4) ;

    //ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE - 1 ;
    //ctx_list[ctxh].num_cfg < MAX_USB_CTRL_CTX -1  ;
    //usbctrl_declare_interface(ctxh, &iface_3) ;



    /*
        usbctrl_get_interface : cas d'erreur - pointeur ctx null
        cas iface < ctx->cfg[ctx->curr_cfg].interface_num pas atteint dans le cas nominal
    */
    usbctrl_context_t *bad_ctx = NULL ;
    usbctrl_get_interface(bad_ctx, iface);

    ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE ;
    usbctrl_get_interface((usbctrl_context_t *)&(ctx_list[ctxh]), iface);

    /*
        usbctrl_get_handler: cas d'erreur - pointeur ctx null
                                           - pointeur handler null
        comme num_ctx < MAX_USB_CTRL_CTX pour ne pas avoir de débordement de tableau, la boucle n'est parcourue qu'une fois dans la fonction
    */

    usbctrl_get_handler(bad_ctx, &handler);
    usbctrl_get_handler(&ctx_test, &handler);  // pour tester behavior not_found


    /*
        usbctrl_get_context, usbctrl_is_endpoint_exists &&  usbctrl_is_interface_exists  : cas d'erreur - pointeur ctx null
    */

    usbctrl_get_context(dev_id,     NULL);
    usbctrl_is_endpoint_exists(bad_ctx, ep);
    usbctrl_is_interface_exists(bad_ctx, iface);

    /*
        test erreur avec un numéro de ctx >= num_ctx (qui vaut 1 au max dans mon cas, avec un max de cfg de 2)
    */

    usbctrl_start_device(4) ;
    usbctrl_stop_device(4) ;

    /*
        test erreur sur get_descriptor : parcourir tous les types possibles, incluant un faux type
                                         pointeurs null
                                         ctx != ctx_list[i] pour error_not_found dans get_handler
                                         class_get_descriptor : error_none forcément, donc je ne rentre pas dans errcode != error_none (modifier la fonction class_get_descriptor?)
                                         while( poll ..) : je ne rentre qu'une fois dans la boucle
                                         cfg->bInterval = poll : pas atteint car driver high speed dans la config actuelle
    */

    uint8_t buf[255] = {0} ;
    uint32_t desc_size = 0 ;
    usbctrl_context_t ctx1 = {1} ;

    usbctrl_get_descriptor(9,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(USB_DESC_DEV_QUALIFIER,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(USB_DESC_OTHER_SPEED_CFG,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(USB_DESC_IFACE_POWER,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(1,NULL,&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(1,&buf[0],NULL,&ctx1, &pkt);
    usbctrl_get_descriptor(1,&buf[0],&desc_size,NULL, &pkt);
    usbctrl_get_descriptor(1,&buf[0],&desc_size,&ctx1, NULL);



/*
    test des fonctions de usbctrl_state avec pointeur null ou état invalide (>= 10)
*/

    usbctrl_get_state(NULL) ;
    usbctrl_set_state(&ctx1,10);
    usbctrl_set_state(NULL,10);


/*
    usbctrl_handle_class_requests : test avec get_handler qui renvoie error not found (donc un contexte différent de ctx_list )
*/
usbctrl_context_t ctx2 = ctx_list[0] ;
ctx2.state = Frama_C_interval_8(0,9);
usbctrl_handle_class_requests(&pkt, &ctx2);

usbctrl_handle_requests(NULL, dev_id);  // pointeur null, les autres erreurs ne sont pas atteignables..

/*
    usbctrl_std_req_handle_get_descriptor : je n'arrive pas à aller dans tous les cas d'erreur (maxlength == 0 ou get_descriptor != error_none )
    usbctrl_std_req_handle_get_status : un cas avec endpoint_exists qui doit retourner false, mais comme je rentre avec ep == EP0, je renvoie true
                                        je ne sais pas comment rentrer dans is_endpoint_exists avec ep != EP0
*/


}

void test_fcn_driver_eva(){

    uint8_t ep_id = Frama_C_interval_8(0,255);
    uint8_t ep_num = Frama_C_interval_8(0,255);
    uint8_t dir8 = Frama_C_interval_8(0,255);
    uint8_t dst = Frama_C_interval_8(0,255);
    uint32_t size = Frama_C_interval_32(0,4294967295);
    uint8_t fifo = Frama_C_interval_8(0,255);
    uint32_t fifo_idx = Frama_C_interval_32(0,4294967295);
    uint32_t fifo_size = Frama_C_interval_32(0,4294967295);
    usbotghs_epx_mpsize_t size_ep = Frama_C_interval_8(0,3);

    uint8_t src = 1 ;

    usbotghs_ep_dir_t dir = Frama_C_interval_8(0,1);
    usbotghs_ep_type_t type = Frama_C_interval_8(0,3);
    usbotghs_ep_state_t state = Frama_C_interval_8(0,9) ;
    usbotghs_dev_mode_t mode = Frama_C_interval_8(0,1);

    usbotghs_global_stall() ;
    usbotghs_endpoint_set_nak(ep_id, dir) ;
    usbotghs_global_stall_clear();
    usbotghs_endpoint_stall_clear(ep_id, dir);
    usbotghs_deconfigure_endpoint(ep_id);
    usbotghs_activate_endpoint(dir8,dir);
    usbotghs_deactivate_endpoint( ep_id,dir);
    usbotghs_enpoint_nak( ep_id);
    usbotghs_enpoint_nak_clear( ep_id);
    usbotghs_endpoint_disable( ep_id,     dir);
    usbotghs_endpoint_enable( ep_id,     dir);
    usbotghs_endpoint_clear_nak(ep_id, dir) ;
    usbotghs_endpoint_stall(ep_id, dir) ;
    usbotghs_get_ep_state(ep_id, dir) ;



    usbotghs_ctx.in_eps[EP0].mpsize = Frama_C_interval_16(0,65535); // tentative pour entrer dans while(residual_size >= size), mais à revoir
    uint8_t resp[1024] = { 0 };
    usbotghs_ctx.in_eps[EP0].fifo_lck = 1 ; // pour avoir une erreur dans xmit_fifo dans send_data
    usb_backend_drv_send_data((uint8_t *)&resp, size, EP0);
    usbotghs_ctx.in_eps[EP0].fifo_lck = 0 ;
    usb_backend_drv_send_data((uint8_t *)&resp, 513, EP0);  // pour rentrer dans la boucle residual_size >= fifo_size
    usbotghs_ctx.in_eps[4].mpsize = Frama_C_interval_16(0,65535);
    usbotghs_ctx.in_eps[4].id = 4 ;  // memory problem for write_core_fifo
    usbotghs_ctx.in_eps[4].fifo_lck = 0 ;
    usbotghs_ctx.in_eps[4].configured = 1 ;
    usb_backend_drv_send_data((uint8_t *)&resp, size, 4);
    usb_backend_drv_send_data((uint8_t *)&resp, size, 8);   // pour entrer dans un cas d'erreur (je n'arrive pas à généraliser ep)
    usbotghs_send_zlp(ep_id);
    usbotghs_txfifo_flush(ep_id);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,64,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,128,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,512,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,1024,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_configure(mode, & usbctrl_handle_inepevent,& usbctrl_handle_outepevent);
    usbotghs_set_recv_fifo((uint8_t *)&resp, size, 0);
    usbotghs_set_recv_fifo((uint8_t *)&resp, size, 1);  //Cyril : erreur dans set_reg_value (integer unsigned downcast, fausse alarme je pense)

}

int main(void)
{

    test_fcn_usbctrl() ;
    test_fcn_usbctrl_erreur() ;
    test_fcn_driver_eva() ;

}
#endif/*!__FRAMAC__*/
