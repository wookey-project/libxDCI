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
#include "libc/sync.h"
//#include <string.h>
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
#else
#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX
#define MAX_USB_CTRL_CFG CONFIG_USBCTRL_MAX_CFG
static uint8_t num_ctx = 0;
//PTH volatile usbctrl_context_t    ctx_list[MAX_USB_CTRL_CTX] = { 0 };
usbctrl_context_t ctx_list[MAX_USB_CTRL_CTX] = { 0 };
#endif/*!__FRAMAC__*/

/*@
    @ requires \separated(&usbotghs_ctx,ctxh+(..), ctx_list+ (..));
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
    @   assigns *ctxh, num_ctx, usbotghs_ctx, GHOST_num_ctx, ctx_list[\old(num_ctx)] ;
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_UNKNOWN ;
    @   ensures *ctxh == \old(GHOST_num_ctx) ;
    @   ensures GHOST_num_ctx == \old(GHOST_num_ctx) +1 ;
    @   ensures ctx_list[\old(num_ctx)].dev_id == dev_id ;
    @   ensures ctx_list[GHOST_num_ctx-1] == ctx_list[num_ctx-1] ;

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
    if (num_ctx >= MAX_USB_CTRL_CTX) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }

    switch (dev_id){
        case USB_OTG_HS_ID:
            errcode = usb_backend_drv_declare() ;
            break;
        case USB_OTG_FS_ID:
            errcode = usb_backend_drv_declare() ;
            break;
        default:
            errcode = MBED_ERROR_NOBACKEND;
            goto err;
            break;
    }

    /* @ assert ctx_list[GHOST_num_ctx] == ctx_list[num_ctx] ; */
    set_u32_with_memsync(&(ctx_list[num_ctx].dev_id), dev_id);
    //PTH ctx_list[num_ctx].dev_id = dev_id;
    *ctxh = num_ctx;

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
        /* @ assert ctx == &(ctx_list[GHOST_num_ctx]); */
    #else
        usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
        //PTH volatile usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
    #endif/*!__FRAMAC__*/

    /* @ assert \valid(ctx_list + (0..(GHOST_num_ctx))) ;  */

    num_ctx++;

    //@ ghost GHOST_num_ctx++  ;


    /* initialize context */
    ctx->num_cfg = 1;

    /* @ assert ctx_list[GHOST_num_ctx-1] == ctx_list[GHOST_num_ctx-1] ; */
    /* @ assert \valid(ctx_list + (0..(GHOST_num_ctx-1))) ; */

    /*@
        @ loop invariant 0 <= i <= CONFIG_USBCTRL_MAX_CFG;
        @ loop invariant \valid(ctx->cfg + (0..(CONFIG_USBCTRL_MAX_CFG-1))) ;
        @ loop invariant \valid(ctx_list + (0..(num_ctx-1))) ;
        @ loop assigns i , ctx_list[num_ctx-1] ;
        @ loop variant (CONFIG_USBCTRL_MAX_CFG - i);
    */

    for (i = 0; i < CONFIG_USBCTRL_MAX_CFG; ++i) {
        ctx->cfg[i].interface_num = 0;
        ctx->cfg[i].first_free_epid = 1;
    }


    ctx->curr_cfg = 0;

    /* @ assert GHOST_num_ctx == num_ctx ; */
    /* @ assert ctx_list[GHOST_num_ctx-1] == ctx_list[GHOST_num_ctx-1] ; */
    /* @ assert *ctxh == GHOST_num_ctx-1 ; */
    /* @ assert ctx_list[GHOST_num_ctx-1].dev_id == dev_id ; */
    /* @ assert \valid(ctx_list + (0..(GHOST_num_ctx-1))) ; */

err:
    return errcode;
}
/*
 * basics for now
 */


/*@
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
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures ctx_list[ctxh].state == USB_DEVICE_STATE_POWERED ;

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

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #else
        volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/


    printf("[USBCTRL] initializing automaton\n");

/*
 TODO FRAMA-c : memcpy
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

    usbctrl_set_state(ctx, USB_DEVICE_STATE_POWERED);

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
    @   ensures \result == MBED_ERROR_NONE ;

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
        @ loop invariant  \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ;
        @ loop invariant \forall integer prei; 0<=prei<i ==> &(ctx_list[prei]) != ctx;
        @ loop assigns i ;
        @ loop variant (GHOST_num_ctx - i);
*/

    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (&(ctx_list[i]) == ctx) {
            *handler = i;
            /* @ assert \exists integer i ; 0 <= i < GHOST_num_ctx && &(ctx_list[i]) == ctx ; */
            goto end;
        }
    }

    /* @ assert \at(handler,Here) == \at(handler,Pre) ; */
    /* @ assert \separated(&ctx_list + (0..(GHOST_num_ctx-1)),ctx,handler); */
    /* @ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> &(ctx_list[i]) != ctx ; */
    /* @ assert \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ; */

    errcode = MBED_ERROR_NOTFOUND;
end:
    return errcode;
}


/*@
    @ requires GHOST_num_ctx == num_ctx ;
    @ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx);
    @ requires \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ;
    @ assigns *ctx, GHOST_idx_ctx;

    @ behavior bad_pointer :
    @   assumes ctx == \null ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   ensures GHOST_idx_ctx == MAX_USB_CTRL_CTX ;

    @ behavior not_found :
    @   assumes ctx != \null ;
    @   assumes !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id) ;
    @   ensures \result == MBED_ERROR_NOTFOUND ;
    @   ensures GHOST_idx_ctx == MAX_USB_CTRL_CTX ;

    @ behavior found :
    @   assumes ctx != \null ;
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id ;
    @   ensures \exists integer i ; 0 <= i < GHOST_num_ctx && \old(ctx_list[i].dev_id) == device_id && GHOST_idx_ctx==i ;
    @   ensures 0 <= GHOST_idx_ctx < GHOST_num_ctx ;
    @   ensures \result == MBED_ERROR_NONE ;
    @	ensures *ctx == &ctx_list[GHOST_idx_ctx];

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

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
        @ loop invariant \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ;
        @ loop invariant \forall integer prei; 0<=prei<i ==> ctx_list[prei].dev_id != device_id   ;
        @ loop invariant \at(ctx,LoopEntry) == \at(ctx,LoopCurrent) ;
	    @ loop invariant GHOST_idx_ctx == MAX_USB_CTRL_CTX;
        @ loop assigns i ;
        @ loop variant (GHOST_num_ctx - i);
    */

    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (ctx_list[i].dev_id == device_id) {
            *ctx = (usbctrl_context_t*)&(ctx_list[i]);
            /*@ ghost GHOST_idx_ctx = i ; */

            /* @ assert  \exists integer i ; 0 <= i < GHOST_num_ctx && *ctx == &ctx_list[i]; */
            /* @ assert *ctx == &ctx_list[i]; */
            /* @ assert *ctx == &ctx_list[GHOST_idx_ctx]; */
            goto end;
        }
    }

   /* @ assert \at(ctx,Here) == \at(ctx,Pre) ; */
    /* @ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != device_id ; */
    /* @ assert \forall integer i ; 0 <= i < GHOST_num_ctx ==> &ctx_list[i] != *ctx ; */
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

    @ behavior too_many_ctrl_config :
    @   assumes ctxh < num_ctx ;
    @   assumes iface != \null ;
    @   assumes !(ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) ;
    @   assumes ((iface->dedicated  == true) && (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num != 0 ) && !((ctx_list[ctxh].num_cfg +1 ) > (CONFIG_USBCTRL_MAX_CFG-1))
                && ((ctx_list[ctxh].num_cfg +1) >= MAX_USB_CTRL_CFG ))
                ||  (( (iface->dedicated  != true) || (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num == 0 ) ) && ctx_list[ctxh].curr_cfg >= MAX_USB_CTRL_CFG ) ;
    @   assigns ctx_list[ctxh] ;
    @   ensures \result == MBED_ERROR_NOMEM ;

    @ behavior ok :
    @   assumes ctxh < num_ctx ;
    @   assumes iface != \null ;
    @   assumes !(ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) ;
    @   assumes ((iface->dedicated  == true) && (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num != 0 ) && !((ctx_list[ctxh].num_cfg +1 ) > (CONFIG_USBCTRL_MAX_CFG-1))
                && ((ctx_list[ctxh].num_cfg +1) < MAX_USB_CTRL_CFG ))
                ||  (( (iface->dedicated  != true) || (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num == 0 ) ) && ctx_list[ctxh].curr_cfg < MAX_USB_CTRL_CFG ) ;
    @   assigns *iface, ctx_list[ctxh] ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors;
    @ disjoint behaviors;

*/

/*
    TODO : test spec with greater value for CONFIG_USBCTRL_MAX_CFG & MAX_USB_CTRL_CFG : dead code with value == 2
*/

mbed_error_t usbctrl_declare_interface(__in     uint32_t ctxh,
                                       __out    usbctrl_interface_t  *iface)
{
    uint8_t iface_config = 0;
    uint8_t i = 0 ;
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t drv_ep_mpsize ;

// @ assert GHOST_num_ctx == num_ctx ;

    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (iface == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #else
        volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/

    /* check space */
    if (ctx->cfg[ctx->curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) {   // RTE : Cyril : == before
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }

    if (iface->dedicated == true && ctx->cfg[ctx->curr_cfg].interface_num != 0) {
            /*
                Cyril : ajout d'un test sur le nombre de config max :
                check space
            */

    	ctx->num_cfg++;   // RTE before, this line was moved (and no test on ctx->num_cfg before)

        if(ctx->num_cfg > (CONFIG_USBCTRL_MAX_CFG - 1)){
            errcode = MBED_ERROR_NOMEM;
            goto err;
        }

        iface_config = ctx->num_cfg;    // Cyril : je ne peux pas arriver ici avec CONFIG_USBCTRL_MAX_CFG == 2
        ctx->cfg[iface_config].first_free_epid = 1;
    } else {
        iface_config = ctx->curr_cfg;
    }


    if (iface_config >= MAX_USB_CTRL_CFG) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }


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

        ctx->cfg[iface_config].interfaces[iface_num].eps[i].configured = false ;

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
    @ ensures (ctxh >= GHOST_num_ctx)  <==> (\result == MBED_ERROR_INVPARAM) ;
    @ ensures (ctxh < GHOST_num_ctx) <==> (\result == MBED_ERROR_NONE) ;
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
