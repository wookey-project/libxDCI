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



#ifndef __FRAMAC__

#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX
#define MAX_USB_CTRL_CFG CONFIG_USBCTRL_MAX_CFG
static uint8_t num_ctx = 0;
usbctrl_context_t ctx_list[MAX_USB_CTRL_CTX] = { 0 };

#endif/*!__FRAMAC__*/


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
#if defined(CONFIG_STM32F439)
        case USB_OTG_HS_ID:
            errcode = usb_backend_drv_declare() ;
            break;
#endif
        case USB_OTG_FS_ID:
            errcode = usb_backend_drv_declare() ;
            break;
        default:
            errcode = MBED_ERROR_NOBACKEND;
            goto err;
            break;
    }

    /*  assert ctx_list[GHOST_num_ctx] == ctx_list[num_ctx] ; */
    set_u32_with_membarrier(&(ctx_list[num_ctx].dev_id), dev_id);
    *ctxh = num_ctx;

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
        /*  assert ctx == &(ctx_list[GHOST_num_ctx]); */
    #else
        usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
    #endif/*!__FRAMAC__*/

    /*  assert \valid(ctx_list + (0..(GHOST_num_ctx))) ;  */

    num_ctx++;

    //@ ghost GHOST_num_ctx++  ;


    /* initialize context */
    ctx->num_cfg = 1;

    /*  assert ctx_list[GHOST_num_ctx-1] == ctx_list[GHOST_num_ctx-1] ; */
    /*  assert \valid(ctx_list + (0..(GHOST_num_ctx-1))) ; */

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

    /*  assert GHOST_num_ctx == num_ctx ; */
    /*  assert ctx_list[GHOST_num_ctx-1] == ctx_list[GHOST_num_ctx-1] ; */
    /*  assert *ctxh == GHOST_num_ctx-1 ; */
    /*  assert ctx_list[GHOST_num_ctx-1].dev_id == dev_id ; */
    /*  assert \valid(ctx_list + (0..(GHOST_num_ctx-1))) ; */

err:
    return errcode;
}
/*
 * basics for now
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
        usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/


    log_printf("[USBCTRL] initializing automaton\n");

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

    /* control pipe recv FIFO is ready to be used */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
    set_bool_with_membarrier(&(ctx->ctrl_req_processing), false);

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
            goto end;
        }
    }


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
            *ctx = &(ctx_list[i]);
            /*@ ghost GHOST_idx_ctx = i ; */
            goto end;
        }
    }

    errcode = MBED_ERROR_NOTFOUND;

end:
    return errcode;
}

/*@
    @ requires 0 <= ep <= 255 ;
    @ assigns \nothing ;

    @ behavior bad_ctx:
    @   assumes ctx == \null ;
    @   ensures \result == USB_EP_DIR_NONE ;

    @ behavior EP_not_found:
    @   assumes ctx != \null ;
    @   assumes ep != EP0 ;
    @   assumes !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep) ;
    @   ensures \result == USB_EP_DIR_NONE;

    @ behavior EP0_found:
    @   assumes ctx != \null ;
    @   assumes ep == EP0 ;
    @   ensures \result == USB_EP_DIR_BOTH ;

    @ behavior EPx_found:
    @   assumes ctx != \null ;
    @   assumes ep != EP0 ;
    @   assumes (\exists  integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
                     ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep) ;
    @   ensures (\result == USB_EP_DIR_IN || \result == USB_EP_DIR_OUT || \result == USB_EP_DIR_BOTH || \result == USB_EP_DIR_NONE ) ;

    @ complete behaviors;
    @ disjoint behaviors;
*/

usb_ep_dir_t usbctrl_get_endpoint_direction(usbctrl_context_t *ctx, uint8_t ep)
{
    uint8_t i = 0 ;
    uint8_t j = 0 ;
    usb_ep_dir_t dir = USB_EP_DIR_NONE;


    /* sanitize */
    if (ctx == NULL) {
        /*@ assert dir == USB_EP_DIR_NONE; */
        goto err;
    }

    if (ep == EP0) {
        dir = USB_EP_DIR_BOTH;
        /*@ assert dir == USB_EP_DIR_BOTH; */
        goto err;
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
                dir = ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].dir;
                if (dir != USB_EP_DIR_IN && dir != USB_EP_DIR_OUT && dir != USB_EP_DIR_BOTH) {
                    /* this should not happen, this means that the EP is not correctly defined */
                    dir = USB_EP_DIR_NONE;
                }
                goto err;
            }
        }
    }

err:
    return dir;
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

/*
    TODO : test spec with greater value for CONFIG_USBCTRL_MAX_CFG & MAX_USB_CTRL_CFG : dead code with value == 2
*/

mbed_error_t usbctrl_declare_interface(__in     uint32_t ctxh,
                                       __out    usbctrl_interface_t  *iface)
{
    uint8_t iface_config = 0;
    uint8_t i = 0 ;
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint16_t drv_ep_mpsize ;

//  assert GHOST_num_ctx == num_ctx ;

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
        usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/

    /* check space */
    if (ctx->cfg[ctx->curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }

    if (iface->dedicated == true && ctx->cfg[ctx->curr_cfg].interface_num != 0) {
            /*
                check space
            */

    	ctx->num_cfg++;

        if(ctx->num_cfg > (CONFIG_USBCTRL_MAX_CFG - 1)){
            errcode = MBED_ERROR_NOMEM;
            goto err;
        }

        iface_config = ctx->num_cfg;
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
            TODO FRAMA-c : memcpy with instantiate
        */

       ctx->cfg[iface_config].interfaces[iface_num].usb_class = iface->usb_class ;
       ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number = iface->usb_ep_number ;
       ctx->cfg[iface_config].interfaces[iface_num].dedicated = iface->dedicated ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].type = iface->eps[0].type ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].dir = iface->eps[0].dir ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].pkt_maxsize = iface->eps[0].pkt_maxsize ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].handler = iface->eps[0].handler ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[1].handler = iface->eps[1].handler ;
       ctx->cfg[iface_config].interfaces[iface_num].rqst_handler = iface->rqst_handler ;
       ctx->cfg[iface_config].interfaces[iface_num].class_desc_handler = iface->class_desc_handler ;
       ctx->cfg[iface_config].interfaces[iface_num].eps[0].poll_interval = iface->eps[0].poll_interval ;
       ctx->cfg[iface_config].interfaces[iface_num].composite_function = iface->composite_function ;
       ctx->cfg[iface_config].interfaces[iface_num].composite_function_id = iface->composite_function_id ;

    #else
        memcpy((void*)&(ctx->cfg[iface_config].interfaces[iface_num]), (void*)iface, sizeof(usbctrl_interface_t));
    #endif/*!__FRAMAC__*/

   /* 2) set the interface identifier */
   ctx->cfg[iface_config].interfaces[iface_num].id = iface_num;
   iface->id = iface_num;
   uint8_t max_ep = ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number ;
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

    /* No variable change for framac, to validate global assigns  */

        ctx->cfg[iface_config].interfaces[iface_num].eps[i].configured = false ;

       if (ctx->cfg[iface_config].interfaces[iface_num].eps[i].type == USB_EP_TYPE_CONTROL) {
           log_printf("declare EP (control) id 0\n");
           ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num = 0;
           iface->eps[i].ep_num = 0;
       } else {
        ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num = ctx->cfg[iface_config].first_free_epid;
           iface->eps[i].ep_num = ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num;
           log_printf("[USBCTRL] declare EP (not control) id %d\n", ctx->cfg[iface_config].interfaces[iface_num].eps[i].ep_num);
           if (iface->eps[i].dir == USB_EP_DIR_BOTH) {
               log_printf("[USBCTRL] EP set as full duplex\n");
           }
           ctx->cfg[iface_config].first_free_epid++;
           /* FIXME: max EP num must be compared to the MAX supported EP num at driver level */
           /* check that declared ep mpsize is compatible with backend driver */

           drv_ep_mpsize = usb_backend_drv_get_ep_mpsize(ctx->cfg[iface_config].interfaces[iface_num].eps[i].type);

           if (ctx->cfg[iface_config].interfaces[iface_num].eps[i].pkt_maxsize > drv_ep_mpsize) {
               log_printf("truncating EP max packet size to backend driver EP max pktsize\n");
               ctx->cfg[iface_config].interfaces[iface_num].eps[i].pkt_maxsize = drv_ep_mpsize;
           }
       }

    #else
        usb_ep_infos_t *ep = &(ctx->cfg[iface_config].interfaces[iface_num].eps[i]) ;
        ep->configured = false;

       if (ep->type == USB_EP_TYPE_CONTROL) {
           log_printf("declare EP (control) id 0\n");
           ep->ep_num = 0;
           iface->eps[i].ep_num = 0;
       } else {
           ep->ep_num = ctx->cfg[iface_config].first_free_epid;
           iface->eps[i].ep_num = ep->ep_num;
           log_printf("declare EP (not control) id %d\n", ep->ep_num);
           if (iface->eps[i].dir == USB_EP_DIR_BOTH) {
               log_printf("[USBCTRL] EP set as full duplex\n");
           }
           ctx->cfg[iface_config].first_free_epid++;
           /* max supported EP by device driver is handled at set_configuration time, as the
            * configure_endpoint will fail. This is not the usbctrl responsability to handle
            * the max number of hardware EP. Thus, the device driver should pretty print
            * that there is no more space to help debugging this behavior. */

           drv_ep_mpsize = usb_backend_drv_get_ep_mpsize((usb_backend_drv_ep_type_t)ep->type);

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

/*
    TODO : be more precise with configure and set_recv_fifo behavior
*/

mbed_error_t usbctrl_start_device(uint32_t ctxh)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }
    usbctrl_context_t *ctx = &(ctx_list[ctxh]);


#ifndef __FRAMAC__
    ADD_LOC_HANDLER(usbctrl_handle_inepevent)
    ADD_LOC_HANDLER(usbctrl_handle_outepevent)
#endif


    /* initialize with POWERED. We wait for the first reset event */
    usbctrl_set_state(ctx, USB_DEVICE_STATE_POWERED);

    log_printf("[USBCTRL] configuring backend driver\n");

    if ((errcode = usb_backend_drv_configure(USB_BACKEND_DRV_MODE_DEVICE, usbctrl_handle_inepevent, usbctrl_handle_outepevent)) != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] failed while initializing backend: err=%d\n", errcode);
        goto end;
    }

    /* Initialize EP0 with first FIFO. Should be reconfigued at Reset time */
    if ((errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0)) != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] failed to initialize EP0 FIFO!\n");
        goto end;
    }

end:
    return errcode;
}

mbed_error_t usbctrl_stop_device(uint32_t ctxh)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
err:
    return errcode;
}
