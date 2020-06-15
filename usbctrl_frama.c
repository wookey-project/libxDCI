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

#if defined(__FRAMAC__)

#include "driver_api/usbotghs_frama.h"
#include "socs/stm32f439/usbotghs_fifos.h"
#include "socs/stm32f439/devlist.h"

#else

#include "generated/devlist.h"

#endif

#include "api/libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
#include "libc/stdio.h"
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

static  uint8_t num_ctx = 0;
#define MAX_EPx_PKT_SIZE 512
#define RAND_UINT_32 65535

/*
    les variables MAX_USB_CTRL_CTX et usbctrl_context_t sont définies dans usbctrl.h
    pour des raisons de visibilité des variables dans Frama

*/

#else

#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX
static volatile uint8_t num_ctx = 0;
volatile usbctrl_context_t    ctx_list[MAX_USB_CTRL_CTX] = { 0 };

#endif/*!__FRAMAC__*/


/*@
    @ requires 0 <= dev_id < RAND_UINT_32 ;
    @
    @ behavior bad_ctxh:
    @   assumes  ctxh == \null;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @
    @ behavior bad_num_ctx:
    @   assumes num_ctx >= MAX_USB_CTRL_CTX ;
    @ 	assumes ctxh != \null  ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NOMEM ;
    @
    @ behavior bad_dev_id:
    @   assumes num_ctx < MAX_USB_CTRL_CTX ;
    @ 	assumes ctxh != \null  ;
    @   assumes dev_id != USB_OTG_HS_ID && dev_id != USB_OTG_FS_ID ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NOBACKEND ;
    @
    @ behavior ok:
    @   assumes (dev_id == USB_OTG_HS_ID || dev_id == USB_OTG_FS_ID) ;
    @	assumes num_ctx < MAX_USB_CTRL_CTX ;
    @ 	assumes ctxh != \null ;
    @   assigns *ctxh, ctx_list[\old(num_ctx)], num_ctx, usbotghs_ctx  ; 
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_UNKNOWN ;
    @   ensures *ctxh == \old(num_ctx) ;
    @   ensures num_ctx == \old(num_ctx) +1 ;
    @   ensures ctx_list[\old(num_ctx)].dev_id == dev_id ;

    @ complete behaviors;
    @ disjoint behaviors;
*/

mbed_error_t usbctrl_declare(uint32_t dev_id, uint32_t *ctxh)
{
    log_printf("[USBCTRL] declaring USB backend\n");
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t i = 0;

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
        	/*@ assert \separated(&usbotghs_ctx,ctx_list + (0..(num_ctx-1))); */
            errcode = usb_backend_drv_declare() ; // Cyril : usbotghs_declare : assigns usbotghs_ctx
            break;
        case USB_OTG_FS_ID:
        	/*@ assert \separated(&usbotghs_ctx,ctx_list + (0..(num_ctx-1))); */
            errcode = usb_backend_drv_declare() ;  
            break;
        default:
            errcode = MBED_ERROR_NOBACKEND;
            goto err;
            //break;  // Cyril : jamais atteint à cause du goto
    }

    ctx_list[num_ctx].dev_id = dev_id;
    *ctxh = num_ctx;

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
    #else
        volatile usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
    #endif/*!__FRAMAC__*/

    num_ctx++;  

    /* initialize context */
    ctx->num_cfg = 1;


    /*@
        @ loop invariant 0 <= i <= CONFIG_USBCTRL_MAX_CFG;
        @ loop invariant \valid(ctx->cfg + (0..(CONFIG_USBCTRL_MAX_CFG-1))) ;
        @ loop assigns i , ctx->cfg[0..(CONFIG_USBCTRL_MAX_CFG-1)] ;
        @ loop variant (CONFIG_USBCTRL_MAX_CFG - i);
    */

    for (i = 0; i < CONFIG_USBCTRL_MAX_CFG; ++i) {
        ctx->cfg[i].interface_num = 0;
        ctx->cfg[i].first_free_epid = 1;
    }


    ctx->curr_cfg = 0;

    /*@ assert *ctxh == num_ctx-1 ; */   // Cyril : ajout de ces 2 assert pour que les ensures soient prouvés par WP
    /*@ assert ctx_list[num_ctx-1].dev_id == dev_id ; */

err:
    return errcode;
}

/*
 * basics for now
 */


/*@
    @ requires 0 <= ctxh < MAX_USB_CTRL_CTX ;
    @
    @ behavior bad_ctxh :
    @   assumes ctxh >= num_ctx ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior ok:
    @   assumes ctxh < num_ctx ;
    @   assigns ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interfaces[0..(MAX_INTERFACES_PER_DEVICE-1)] ;
    @	assigns ctx_list[ctxh];
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

    #if defined(__FRAMAC__)
        usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #else
        volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    #endif/*!__FRAMAC__*/


    //printf("[USBCTRL] initializing automaton\n");

/*
 TODO FRAMA-c : spécifier memset et memcpy...
*/

    #if defined(__FRAMAC__)

        //memset((void*)ctx->cfg[ctx->curr_cfg].interfaces, 0x0, MAX_INTERFACES_PER_DEVICE * sizeof(usbctrl_interface_t));
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
            //ctx->cfg[ctx->curr_cfg].interfaces[i].eps[MAX_EP_PER_INTERFACE] = 0 ;
        }

    #else
        memset((void*)ctx->cfg[ctx->curr_cfg].interfaces, 0x0, MAX_INTERFACES_PER_DEVICE * sizeof(usbctrl_interface_t));
    #endif/*!__FRAMAC__*/


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
    @ behavior bad_pointer :
    @	assumes (ctx == \null || handler == \null) ;
    @	assigns \nothing ;
    @	ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior not_found :
    @	assumes ctx != \null && handler != \null ;
    @	assumes \forall integer i ; 0 <= i < num_ctx ==> &(ctx_list[i]) != ctx ;
    @	assigns \nothing ;   
    @	ensures \result == MBED_ERROR_NOTFOUND ;

	@ behavior found :
    @	assumes ctx != \null && handler != \null ;
    @	assumes \exists integer i ; 0 <= i < num_ctx && &(ctx_list[i]) == ctx ;
    @ 	assigns *handler ;
    @ 	ensures \result == MBED_ERROR_NONE  ;  

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
        @ loop invariant 0 <= i <= num_ctx;
        @ loop invariant \valid_read(&ctx_list + (0..(num_ctx-1))) ;
        @ loop invariant \valid_read(ctx) ;
        @ loop invariant \valid(handler);
        @ loop invariant \forall integer prei; 0<=prei<i ==> &(ctx_list[prei]) != ctx;
        @ loop assigns i  ;
        @ loop variant (num_ctx - i);
*/

    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (&(ctx_list[i]) == ctx) {
            *handler = i;
            /*@ assert errcode == MBED_ERROR_NONE ; */
            /*@ assert 0 <= i < num_ctx ; */
            goto end;
        }
    }
    errcode = MBED_ERROR_NOTFOUND;
end:
    return errcode;
}


/*@

    @ behavior bad_pointer :
    @	assumes ctx == \null ;
    @	assigns \nothing ;
    @	ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior not_found :
    @	assumes ctx != \null ;
    @	assumes \forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != device_id ;
    @	assigns \nothing ;    
    @	ensures \result == MBED_ERROR_NOTFOUND ;

	@ behavior found :
    @	assumes ctx != \null ;
    @	assumes \exists integer i ; 0 <= i < num_ctx && ctx_list[i].dev_id == device_id ;
    @ 	assigns *ctx ;
    @ 	ensures \result == MBED_ERROR_NONE ; 
    @   ensures \exists integer i ; 0 <= i < num_ctx && *ctx == &ctx_list[i]; // Cyril : je pense que c'est  ça le résultat important

    @ complete behaviors ;
    @ disjoint behaviors ;
*/


mbed_error_t usbctrl_get_context(uint32_t device_id,
                                 usbctrl_context_t **ctx)
{

    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }
    /* search */

	/*@
        @ loop invariant 0 <= i <= num_ctx;
        @ loop invariant \valid_read(&ctx_list + (0..(num_ctx-1))) ;
        @ loop invariant \valid(ctx) ;
        @ loop invariant \forall integer prei; 0<=prei<i ==> ctx_list[prei].dev_id != device_id  ;
        @ loop invariant \at(ctx,LoopEntry) == \at(ctx,LoopCurrent) ;
        @ loop assigns i ;
        @ loop variant (num_ctx - i);
	*/

    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (ctx_list[i].dev_id == device_id) {
            *ctx = (usbctrl_context_t*)&(ctx_list[i]);
            /*@ assert *ctx == &ctx_list[i]; */
            goto end;
        }
    }
   /*@ assert \at(ctx,Here) == \at(ctx,Pre) ; */
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

    @ behavior EP_0:
    @   assumes ctx != \null;
    @   assumes ep == EP0 ;
    @   ensures \result == \true ;

    @ behavior EP_not_found:
    @   assumes ctx != \null ;
    @   assumes ep != EP0 ;
    @   assumes !(\exists integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
    			ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep) ;
    @   ensures \result == \false;

    @ behavior EP_found:
    @   assumes ctx != \null ;
    @   assumes ep != EP0 ;
    @   assumes (\exists  integer i,j ; 0 <= i < ctx->cfg[ctx->curr_cfg].interface_num && 0 <= j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number &&
    				 ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep);
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
	@	assumes ctx == \null ;
	@	ensures \result == \false ;

	@ behavior iface_false:
	@	assumes ctx != \null ;
	@	assumes iface >= ctx->cfg[ctx->curr_cfg].interface_num ;
	@	ensures \result == \false ;

	@ behavior true :
	@ 	assumes ctx != \null ;
	@	assumes !(iface >= ctx->cfg[ctx->curr_cfg].interface_num) ;
	@	ensures \result == \true ;

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
	@	assumes ctx == \null ;
	@	ensures \result == \null ;

	@ behavior iface_null:
	@	assumes ctx != \null ;
	@	assumes iface >= ctx->cfg[ctx->curr_cfg].interface_num ;
	@	ensures \result == \null ;

	@ behavior iface_ok :
	@ 	assumes ctx != \null ;
	@	assumes !(iface >= ctx->cfg[ctx->curr_cfg].interface_num) ;
	@	ensures \result == &(ctx->cfg[ctx->curr_cfg].interfaces[iface]) ;

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
	@ requires 0 <= ctxh ;

    @ behavior bad_ctxh :
    @   assumes ctxh >= num_ctx ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior invalid_iface :
    @   assumes iface == \null ;
    @	assumes ctxh < num_ctx ;
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
    @   assumes ctx_list[ctxh].num_cfg >= (MAX_USB_CTRL_CTX-1) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_NOMEM ;

    @ behavior ok :
    @   assumes ctxh < num_ctx ;
    @   assumes iface != \null ;
    @   assumes !(ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num >= MAX_INTERFACES_PER_DEVICE) ;
    @ 	assumes (iface->dedicated  == true) && (ctx_list[ctxh].cfg[ctx_list[ctxh].curr_cfg].interface_num != 0 ) && (ctx_list[ctxh].num_cfg < (MAX_USB_CTRL_CTX-1))
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
        if(ctx->num_cfg >= MAX_USB_CTRL_CTX-1){
            errcode = MBED_ERROR_NOMEM;
            goto err;
        }

        ctx->num_cfg++;
        iface_config = ctx->num_cfg;
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
        //usb_ep_infos_t *ep = &(ctx->cfg[iface_config].interfaces[iface_num].eps[i]) ;
        //ep->configured = false;
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

/* @
	@ behavior bad_ctxh :
	@	assumes ctxh >= num_ctx ;
	@	assigns \nothing ;
	@	ensures \result == MBED_ERROR_INVPARAM ;

	@ behavior error_configure:
	@	assumes ctxh < num_ctx ;
	@	assumes


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

    log_printf("[USBCTRL] configuring backend driver\n");
    //PMO
    /* @ assert usbotghs_ctx.in_eps[0].mpsize ==0 ;*/
    if ((errcode = usb_backend_drv_configure(USB_BACKEND_DRV_MODE_DEVICE, usbctrl_handle_inepevent, usbctrl_handle_outepevent)) != MBED_ERROR_NONE) {
        //log_printf("[USBCTRL] failed while initializing backend: err=%d\n", errcode);
        usbctrl_set_state(ctx, USB_DEVICE_STATE_INVALID);
        goto end;
    }
    /* Initialize EP0 with first FIFO. Should be reconfigued at Reset time */
    if ((errcode = usb_backend_drv_set_recv_fifo((uint8_t*)&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0)) != MBED_ERROR_NONE) {
        //printf("[USBCTRL] failed to initialize EP0 FIFO!\n");
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
    volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);

    ctx = ctx;
    /* FIXME: TODO */
err:
    return errcode;
}


/**********************************************
 * USB CTRL State automaton getters and setters
 *********************************************/


/*@
  @ assigns \nothing ;
  @ ensures (ctx == \null) ==> \result == USB_DEVICE_STATE_INVALID ;
  @ ensures (ctx != \null) ==> \result == ctx->state ;
*/

usb_device_state_t usbctrl_get_state(const usbctrl_context_t *ctx)
{
   if (ctx == NULL) {
       return USB_DEVICE_STATE_INVALID;
   }
   return ctx->state;
}

/*
 * This function is eligible in both main thread and ISR
 * mode (through trigger execution). Please use aprintf only
 * here.
 */

/*@
  @ assigns ctx->state ;
  @ ensures (ctx == \null) ==> (\result == MBED_ERROR_INVPARAM) ;
  @ ensures (newstate > USB_DEVICE_STATE_INVALID ) ==> (\result == MBED_ERROR_INVPARAM) ;
  @ ensures (ctx != \null && is_valid_state(ctx->state) && newstate <= USB_DEVICE_STATE_INVALID)  ==> (\result == MBED_ERROR_NONE && ctx->state == newstate) ;
*/

#if defined(__FRAMAC__)
mbed_error_t usbctrl_set_state(__out usbctrl_context_t *ctx,
                               __in usb_device_state_t newstate)
{
    /* FIXME: transient, maybe we need to lock here. */
   if (ctx == NULL) {
       return MBED_ERROR_INVPARAM;
   }
    if (newstate > USB_DEVICE_STATE_INVALID) {
        //log_printf("[USBCTRL] invalid state transition !\n");
        return MBED_ERROR_INVPARAM;
    }
    //log_printf("[USBCTRL] changing from state %x to %x\n", ctx->state, newstate);
    ctx->state = newstate;

      /* assert ctx->state == newstate; */

    return MBED_ERROR_NONE;
}
#else
mbed_error_t usbctrl_set_state(__out volatile usbctrl_context_t *ctx,
                               __in usb_device_state_t newstate)
{
    /* FIXME: transient, maybe we need to lock here. */
   if (ctx == NULL) {
       return MBED_ERROR_INVPARAM;
   }
    if (newstate > USB_DEVICE_STATE_INVALID) {   //Cyril : avant, newstate >= USB_DEVICE_STATE_INVALID donc on avait jamais ctx->state = USB_DEVICE_STATE_INVALID
        log_printf("[USBCTRL] invalid state transition !\n");
        return MBED_ERROR_INVPARAM;
    }
    log_printf("[USBCTRL] changing from state %x to %x\n", ctx->state, newstate);
    ctx->state = newstate;

    return MBED_ERROR_NONE;
}
#endif/*!__FRAMAC__*/ 



/******************************************************
 * USBCTRL automaton management function (transition and
 * state check)
 *****************************************************/

/*!
 * \brief return the next automaton state
 *
 * The next state is returned depending on the current state
 * and the current request. In some case, it can be 0xff if multiple
 * next states are possible.
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return the next state, or 0xff
 */

/*@ 
  @ requires is_valid_state(current_state);
  @ requires is_valid_request_code(request);
  @ assigns \nothing ;
  @ ensures (\forall integer i; 0 <= i < MAX_TRANSITION_STATE ==> usb_automaton[current_state].req_trans[i].request != request)
            ==> \result == 0xff ;
  @ ensures (\result != 0xff) ==> \exists integer i; 0 <= i < MAX_TRANSITION_STATE && usb_automaton[current_state].req_trans[i].request == request
            && \result == usb_automaton[current_state].req_trans[i].target_state ;
*/

uint8_t usbctrl_next_state(usb_device_state_t current_state,
                           usbctrl_request_code_t request)
{
    
  /*@
      @ loop invariant 0 <= i <= MAX_TRANSITION_STATE ;
      @ loop invariant \valid_read(usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)));
      @ loop invariant (\forall integer prei ; 0 <= prei < i ==> usb_automaton[current_state].req_trans[prei].request != request) ;
      @ loop assigns i ;
      @ loop variant MAX_TRANSITION_STATE -i ;
  */

    for (uint8_t i = 0; i < MAX_TRANSITION_STATE; ++i) {
        if (usb_automaton[current_state].req_trans[i].request == request) {
            return (usb_automaton[current_state].req_trans[i].target_state);
        }
    }
    /* fallback, no corresponding request found for  this state */
    return 0xff;
}

/*!
 * \brief Specify if the current request is valid for the current state
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return true if the transition request is allowed for this state, or false
 */

/*@
    @ requires \valid(ctx);
    @ requires is_valid_state(current_state) ;
    @ requires is_valid_transition(transition);
    @ requires \valid_read(GHOST_usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)));
    @ requires \separated(GHOST_usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)),ctx);

    @ behavior true:
    @   assumes is_valid_request_transition(current_state,transition) ;
    @   assigns \nothing ;
    @   ensures \result == \true ;

    @ behavior false:
    @   assumes !is_valid_request_transition(current_state,transition) ;
    @   assigns *ctx ;
    @   ensures \result == \false  ;
    @   ensures ctx->state == USB_DEVICE_STATE_INVALID  ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

bool usbctrl_is_valid_transition(usb_device_state_t current_state,
                                 usb_device_trans_t transition,
                                 usbctrl_context_t *ctx)
{
  /*@
      @ loop invariant 0 <= i <= MAX_TRANSITION_STATE ;
      @ loop invariant \valid_read(GHOST_usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)));
      @ loop invariant (\forall integer prei ; 0 <= prei < i ==> GHOST_usb_automaton[current_state].req_trans[prei].request != transition) ;
      @ loop assigns i ;
      @ loop variant MAX_TRANSITION_STATE -i ;
  */


    for (uint8_t i = 0; i < MAX_TRANSITION_STATE; ++i) {
        if (usb_automaton[current_state].req_trans[i].request == transition) {
            return true;
        }
    }
    /*
     * Didn't find any request associated to current state. This is not a
     * valid transition. We should stall the request.
     */
    log_printf("%s: invalid transition from state %d, request %d\n", __func__, current_state, transition);
    
    usbctrl_set_state(ctx, USB_DEVICE_STATE_INVALID);
    /*@ assert ctx->state ==  USB_DEVICE_STATE_INVALID; */ 
    
    return false;
}

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
    @ requires ctx != \null ;
    @ assigns \nothing ;
    @ ensures (ctx->state == USB_DEVICE_STATE_CONFIGURED) ==> \result == \true ;
    @ ensures !(ctx->state == USB_DEVICE_STATE_CONFIGURED) ==> \result == \false ;

*/

static inline bool is_class_requests_allowed(usbctrl_context_t *ctx)
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

    @ behavior USB_DEVICE_STATE_ADDRESS_bad_recipient:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assigns *ctx ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   

    @ behavior USB_DEVICE_STATE_ADDRESS_bad_index:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes ((pkt->wIndex & 0xf) != 0) ;
    @   assigns *ctx ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_NONE   ;
    @   ensures ctx->ctrl_req_processing == \false;   

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_USB_REQ_RECIPIENT_ENDPOINT_endpoint_false:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
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
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_NONE   ; // je dois ajouter un ensures pour : return the recipient status (2 bytes, or wLength if smaller)

    @ behavior USB_DEVICE_STATE_ADDRESS_recipient_other :
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assumes !(((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT && ((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   assumes !((pkt->wIndex & 0xf) != 0) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_ENDPOINT) ;
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
            /*@ assert \separated(ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
            usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN);
            /*request finish here */
            ctx->ctrl_req_processing = false;
            break;
        case USB_DEVICE_STATE_ADDRESS: 
            if (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_ENDPOINT &&
                usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE) {
                /* only interface or endpoint 0 allowed in ADDRESS state */
                /* request error: sending STALL on status or data */
                /*@ assert \separated(ctx,r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
                //usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_IN); 
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
            switch (usbctrl_std_req_get_recipient(pkt)) {
                case USB_REQ_RECIPIENT_ENDPOINT: {
                    /*does requested EP exists ? */
                    uint8_t epnum = pkt->wIndex & 0xf;
                    if (!usbctrl_is_endpoint_exists(ctx, epnum)) { // Cyril : je ne peux arriver ici qu'avec ctx null, question est-ce que je peux utiliser la fonction avec ctx null?
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
                    
                    // cyril : bon pour cette fonction, pas encore de assigns valides
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
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: get iface\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        /*request finish here */
        ctx->ctrl_req_processing = false;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    ctx = ctx;
    /*request finish here */
    ctx->ctrl_req_processing = false;
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
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) , *r_CORTEX_M_USBOTG_HS_DOEPCTL(0), *pkt;  
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_ADDRESS:
    @   assumes ctx->state == USB_DEVICE_STATE_ADDRESS ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) , *r_CORTEX_M_USBOTG_HS_DOEPCTL(0), *pkt;  
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior USB_DEVICE_STATE_CONFIGURED:
    @   assumes ctx->state == USB_DEVICE_STATE_CONFIGURED ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(0) , *r_CORTEX_M_USBOTG_HS_DOEPCTL(0), *pkt;  
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

// cyril:  à mettre à jour quand les assigns seront mis dans send_data

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

    //requested_configuration = pkt->wValue;  //Cyril : Problème ici: pkt->wValue est un uint16_t, alors que requested_configuration est un uint8_t
                                              // voir comment traiter le pb proprement

    /* sanity on requested configuration */   // cyril : j'ai remplacé requested_configuration par par pkt->wValue, parce qu'il y a un bug entre uint8 et uint16
    if ((pkt->wValue == 0) || (pkt->wValue > ctx->num_cfg)) {
        log_printf("[USBCTRL] Invalid requested configuration!\n");
        /*@ assert ctx->state == USB_DEVICE_STATE_CONFIGURED ; */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    ctx->curr_cfg = pkt->wValue - 1;
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
        *r_CORTEX_M_USBOTG_HS_DIEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num), // comment dire que toute une plage de mémoire est assign?
        *r_CORTEX_M_USBOTG_HS_DOEPCTL(ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num)

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

    @ complete behaviors ;
    @ disjoint behaviors ;

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
            if (pkt->wIndex != 0) {   // Cyril : si pkt->wIndex == 0, ça cause un pb pour handle class request : voir avec Philippe
                /*request finish here */
                ctx->ctrl_req_processing = false;
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
            if (maxlength == 0) {  // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch (test if ligne 1946)
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
            if (maxlength == 0) {    // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch (test if ligne 1946)
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
            if (maxlength == 0) {     // Cyril : vu que pkt n'est pas modifié, on ne peut pas arriver ici avec le test avant le switch (test if ligne 1946)
                errcode = usb_backend_drv_send_zlp(0);
                /*request finish here */
                ctx->ctrl_req_processing = false;
            } else {
                if ((errcode = usbctrl_get_descriptor(USB_DESC_INTERFACE, &(buf[0]), &size, ctx, pkt)) != MBED_ERROR_NONE) {
                    // Cyril : comme on est dans le cas USB_DESC_INTERFACE, size == 0, donc on n'entrera jamais dans le test ligne 2074 (else) ; code non atteignable par EVA
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
                // Cyril : comme on est dans le cas USB_DESC_ENDPOINT, size == 0, donc on n'entrera jamais dans le test ligne 2074 (else) ; code non atteignable par EVA
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
    @   ensures ctx->ctrl_req_processing == \false;
    @   assigns *ctx ;

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
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: set feature\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        /* request finish here */
        ctx->ctrl_req_processing = false;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
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
    @   assigns *ctx;
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
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: set interface\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    usb_backend_drv_send_zlp(0);
err:
    /*request finish here */
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
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] Std req: sync_frame\n");
    if (!is_std_requests_allowed(ctx)) {
        /* error handling, invalid state */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handling standard Request */
    pkt = pkt;
    usb_backend_drv_send_zlp(0);
err:
    return errcode;
}


/*
 * Standard requests must be supported by any devices and are handled here.
 * These requests handlers are written above and executed directly by the libusbctrl
 */

/* @
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


    @ behavior std_requests_not_allowed:
    @   assumes !(ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assigns \nothing ;
    @   ensures \result == MBED_ERROR_INVSTATE ;

    @ behavior no_iface:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assumes (((pkt->wIndex) & 0xff) - 1 ) >= ctx->cfg[ctx->curr_cfg].interface_num ;  // condition pour is_interface_exists : iface_idx >= ctx->cfg[ctx->curr_cfg].interface_num
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_NOTFOUND || \result == MBED_ERROR_UNKNOWN ;  // Cyril : je ne comprends pas pq invstate...

    @ behavior handler:
    @   assumes (ctx->state == USB_DEVICE_STATE_CONFIGURED) ;
    @   assumes !((((pkt->wIndex) & 0xff) - 1) >= ctx->cfg[ctx->curr_cfg].interface_num) ;
    @   assigns \nothing ;  // Cyril : parce que le pointeur de fonction assigns \nothing (hypothèse de ma part)
    @   ensures is_valid_error(\result) ;  // errcode = iface->rqst_handler(handler, pkt); // pour etre général avec le pointeur de fonction

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
    
    /*
        Cyril : Ajout de ce test (defense en profondeur) pour éviter ce cas lors du calcul de iface_idx
                normalement, cas impossible (interdit dans les specs)

    */

    if(((pkt->wIndex) & 0xff) == 0 ){   
        /*@ assert ((pkt->wIndex) & 0xff) == 0 ; */ 
        errcode = MBED_ERROR_INVPARAM ;
        goto err ;
    }

    /*@ assert ((pkt->wIndex) & 0xff) != 0 ; */  // Cyril : validé
    /*@ assert ((pkt->wIndex) & 0xff) > 0 ; */   // Cyril : non validé, je ne comprends pas pq

    iface_idx = (((pkt->wIndex) & 0xff) -1 );  // Cyril : iface_idx : problème d'uint8_t >=0 (rte downcast). 0xff joue le rôle d'un masque, les 8 premiers bits de index sont mis à 0 donc <= 255 ça marche

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
    uint32_t handler = 0 ;  // Cyril : ajout pour EVA, handler doit être initialisé avant l'appel de iface->rqst_handler(handler, pkt)
                            // ou alors il manque un goto err dans le test en dessous 
    if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
        log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
    }

    if (iface->rqst_handler != NULL) {   // Cyril : ajout d'un test sur la valeur du pointeur de fonction
 
    /*@ assert iface->rqst_handler ∈ {usbctrl_class_rqst_handler}; */   // Cyril : ne passe pas avec EVA : il manque un test sur le pointeur de fonction : null ou pas...
    /*@ calls usbctrl_class_rqst_handler; */  // Cyril : problem assert Eva: initialization: \initialized(&handler);  à creuser...

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

/*@
    @ behavior bad_pkt:
    @   assumes pkt == \null ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior bad_ctx:
    @   assumes pkt != \null ;
    @   assumes \forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id ;
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;
    @   ensures \result == MBED_ERROR_UNKNOWN ;

    @ behavior USB_REQ_TYPE_STD:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) ;
    @   assumes (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;
    @   ensures is_valid_error(\result) ;   // être plus précis quand la fonction usbctrl_handle_std_requests sera correctement spécifiée
    @   assigns ctx_list[0..(num_ctx-1)];

    @ behavior USB_REQ_TYPE_VENDOR:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;
    @   ensures (\result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_NONE) ;

    @ behavior USB_REQ_TYPE_CLASS:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;   
    @   assumes ((((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS) || (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE)) ;
    @   ensures is_valid_error(\result) ;   // Cyril : dans l'attente de discuter avec Philippe de errcode et upperstack

    @ behavior UNKNOWN:
    @   assumes pkt != \null ;
    @   assumes !(\forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id) ;
    @   assumes !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) ;
    @   assumes !(((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;    
    @   assumes !((((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_CLASS) || (((pkt->bmRequestType) & 0x1F) == USB_REQ_RECIPIENT_INTERFACE)) ; 
    @   assigns *pkt, ctx_list[0..(num_ctx-1)] ;  // cyril : je dois laisser ctx_list[0..(num_ctx-1)], *ctx_list n'est pas validé par WP
    @   assigns *r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), *r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0) ;  
    @   ensures \result == MBED_ERROR_UNKNOWN ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/


/*        

assigns de std, vendor et class encore à faire (pas validé pour le moment)

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
        /*@ assert \separated(pkt,ctx_list + (0..(num_ctx-1)),r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
        errcode = MBED_ERROR_UNKNOWN;
        usb_backend_drv_stall(EP0, USB_EP_DIR_OUT);
        /*@ assert \forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id ; */  // Cyril : seule condition pour avoir usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE car *ctx != NULL
        goto err;
    }

  /*@ assert \exists integer i; 0 ≤ i < num_ctx && ctx_list[i].dev_id == dev_id; */
  /*@ assert \exists integer i; 0 ≤ i < num_ctx && ctx == &ctx_list[i]; */ ;


    if (   (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_STD)
        && (usbctrl_std_req_get_recipient(pkt) != USB_REQ_RECIPIENT_INTERFACE)) {

    /*@   assert (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_STD) ;  */
    /*@   assert (((pkt->bmRequestType) & 0x1F) != USB_REQ_RECIPIENT_INTERFACE) ;  */

        ctx->ctrl_req_processing = true;
        /* For current request of current context, is the current context is a standard
         * request ? If yes, handle localy */
        errcode = usbctrl_handle_std_requests(pkt, ctx);
    } 
    else if (usbctrl_std_req_get_type(pkt) == USB_REQ_TYPE_VENDOR) {
        /* ... or, is the current request is a vendor request, then handle locally
         * for vendor */
        /*@ assert (((pkt->bmRequestType >> 5) & 0x3) == USB_REQ_TYPE_VENDOR) ;  */
        ctx->ctrl_req_processing = true;
        /*@ assert \separated(pkt,ctx_list + (0..(num_ctx-1))) ; */
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
                if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {  // cyril : il manque pas un break ici aussi?
                    log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
                }
                
                /*@ assert ctx->cfg[curr_cfg].interfaces[i].rqst_handler ∈ {&usbctrl_class_rqst_handler}; */
                /*@ calls usbctrl_class_rqst_handler; */

                if ((upper_stack_err = ctx->cfg[curr_cfg].interfaces[i].rqst_handler(handler, pkt)) == MBED_ERROR_NONE) {  // Cyril : mais que devient errcode? c'est lui qui est return à la fin
                    /* upper class handler found, we can leave the loop */
                    break;
                }
            }
        }
        /* fallback if no upper stack class request handler was able to handle the received CLASS request */
        if (upper_stack_err != MBED_ERROR_NONE) {
            /*@ assert \separated(pkt,ctx_list + (0..(num_ctx-1)),r_CORTEX_M_USBOTG_HS_DIEPCTL(EP0), r_CORTEX_M_USBOTG_HS_DOEPCTL(EP0)) ; */
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
    //ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;   // Cyril : probleme ici, on peut y arriver avec ctx non défini (donc accès mémoire invalide)
    return errcode;
}


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

/*@
    @ assigns \nothing ;
    @ ensures \result == MBED_ERROR_NONE ;
*/

mbed_error_t usbctrl_handle_earlysuspend(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}



/*@
    @ assigns \nothing ;
    @ ensures \result == MBED_ERROR_NONE ;
*/

mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

mbed_error_t usbctrl_handle_reset(uint32_t dev_id)
{
    
    mbed_error_t       errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    usbctrl_context_t *ctx = NULL;
    log_printf("[USBCTRL] Handling reset\n");
    /* TODO: support for multiple drivers in the same time.
    This requires a driver table with callbacks or a preprocessing mechanism
    to select the corresponding driver API. While the libctrl is not yet fully
    operational, we handle only usbotghs driver API */
    dev_id = dev_id;

    log_printf("[USBCTRL] reset: get context for dev_id %d\n", dev_id);
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) { 
        /*@ assert \forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id ; */
        log_printf("[USBCTRL] reset: no ctx found!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    // Cyril : de ctx, je dois remonter à ctx_list[i], avec i inconnu... 0 <= i <= num_ctx

    /*@ assert \exists integer i ; 0 <= i < num_ctx && ctx_list[i].dev_id == dev_id ; */
    /*@ assert &ctx_list[0] == ctx ; */  // comment généraliser avec un integer i?

    usb_device_state_t state = usbctrl_get_state(ctx);

    /* resetting directly depends on the current state */
    if (!usbctrl_is_valid_transition(state, USB_DEVICE_TRANS_RESET, ctx)) {       
        log_printf("[USBCTRL] RESET transition is invalid in current state !\n");
        /*@ assert ctx_list[0].state ==  USB_DEVICE_STATE_INVALID; */
        /* @ assert \at(ctx_list,Here) != \at(ctx_list,Pre) ; */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    log_printf("[USBCTRL] reset: execute transition from state %d\n", state);
    /* handling RESET event depending on current state */
    switch (state) {
        case USB_DEVICE_STATE_POWERED:
            /* initial reset of the device, set EP0 FIFO. Other EPs FIFO
             * are handled at SetConfiguration & SetInterface time */
            /* as USB Reset action reinitialize the EP0 FIFOs (flush, purge and deconfigure) they must
             * be reconfigure for EP0 here. */
            log_printf("[USBCTRL] reset: set reveive FIFO for EP0\n");

            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);


            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            break;
        case USB_DEVICE_STATE_SUSPENDED_DEFAULT:
            /* awake from suspended state, back to default */
            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;

            break;
        case USB_DEVICE_STATE_SUSPENDED_ADDRESS:
            /* awake from suspended state, back to address */
            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;

            break;
        case USB_DEVICE_STATE_SUSPENDED_CONFIGURED:
            /* awake from suspended state, back to configured */
            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            break;
        case USB_DEVICE_STATE_DEFAULT:
            /* going back to default... meaning doing nothing */
            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            break;
        case USB_DEVICE_STATE_ADDRESS:
            /* going back to default */
            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            ctx->address = 0;
            usb_backend_drv_set_address(0); 
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* INFO: deconfigure any potential active EP of current config is automatically
             * done by USB OTG HS core at reset */

            /* going back to default */
            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            /* when configured, the upper layer must also be reset */
            ctx->address = 0;
            usb_backend_drv_set_address(0); 
            usbctrl_reset_received();
            break;
        default:
            /* this should *not* happend ! this is not standard. */
            usbctrl_set_state(ctx, USB_DEVICE_STATE_INVALID);
            errcode = MBED_ERROR_INVSTATE;
            goto err;
            break;

    }
    /* Switching to state targeted by the automaton, Depending on the current
     * state.
     * This action is generic thinks to the automaton and can be executed out
     * of the above switch().
     * after sanitation, should not fail */
    usbctrl_set_state(ctx, usbctrl_next_state(state, USB_DEVICE_TRANS_RESET));

err:
    return errcode;
}



/*
 * IN EP event (data sent) for EP 0
 */


/*@
    @ behavior ctx_not_found:
    @   assumes \forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id ;
    @   assigns \nothing ;    
    @   ensures \result == MBED_ERROR_NOTFOUND ;

    @ behavior ctx_found :
    @   assumes \exists integer i ; 0 <= i < num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assigns ctx_list[0..(num_ctx-1)] ;  // cyril :c'est large mais ça passe, je ne sais pas comment faire un assigns plus précise (ctx_list[i])
    @   ensures is_valid_error(\result);

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id, uint32_t size, uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;
    log_printf("[LIBCTRL] handle inevent\n");
    /* get back associated context */
    if ((errcode = usbctrl_get_context(dev_id, &ctx)) != MBED_ERROR_NONE) {
        /*@ assert \forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id ; */
        goto err;
    }

    /*@ assert \exists integer i ; 0 <= i < num_ctx && ctx_list[i].dev_id == dev_id  ; */
    /*@ assert \exists integer i ; 0 <= i < num_ctx && ctx == &ctx_list[i] ; */  // Cyril : plus généralement, c'est ctx == &ctx_list[i] tel que ctx_list[i].dev_id == dev_id
                                         // mais je sais pas comment le dire 

    /*
     * By now, this handler is called only for successfully transmitted pkts
     * TODO: maybe we should handle NAK effective & errors at control level, using
     * ep state
     */
    /* acknowledge data transfert. For control & bulk (not isochronous, IT ?) */
    // acknowledgement in request handling by now...
    // usb_backend_drv_send_zlp(ep);

    log_printf("[LIBCTRL] handle inpevent\n");
    uint8_t curr_cfg = ctx->curr_cfg;
    /* If we are in a request processing, we just close it. request processing
     * that are closed here are the ones which send data (get_descriptor & co.)
     * For them, the flag ctx->ctrl_req_processing is risen at request exec and
     * is cleared here. other requests (the one which do not send data)
     * have this flag clear syncrhonously. */
    if (ctx->ctrl_req_processing == true) {
        log_printf("[LIBCTRL] end of control level request\n");
        ctx->ctrl_req_processing = false;
    } else {
        log_printf("[LIBCTRL] end of upper layer request\n");
        
        /*@
            @ loop invariant 0 <= iface <= ctx->cfg[curr_cfg].interface_num ;
            @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface].eps + (ctx->cfg[curr_cfg].interface_num - 1));
            @ loop assigns iface, errcode ;
            @ loop variant (ctx->cfg[curr_cfg].interface_num - iface);
        */

        for (uint8_t iface = 0; iface < ctx->cfg[curr_cfg].interface_num; ++iface) {
            
        /*@
            @ loop invariant 0 <= i <= ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number ;
            @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface].eps + (ctx->cfg[curr_cfg].interface_num - 1));
            @ loop assigns i, errcode ;
            @ loop variant (ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number - i);
        */            

            for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number; ++i) {
                /* here we check both ep id and direction and EP0 is a specific full duplex case */
                if (   ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num == ep
                    && ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir == USB_EP_DIR_IN) {
                    log_printf("[LIBCTRL] found ep in iface %d, declared ep %d\n", iface, i);
                    if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler) {
                        log_printf("[LIBCTRL] iepint: executing upper class handler for EP %d\n", ep);
                        /* XXX: c'est ma FIFO ? oui, c'est pour moi. Non, c'est pour au dessus :-)*/
                            /*@ assert ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler ∈ {&handler_ep}; */
                            /*@ calls handler_ep; */
                        errcode = ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler(dev_id, size, ep);  // Cyril : ajout de errcode = (comme pour class_desc_handler)
                    }
                    break;
                }
            }
        }
    }
    dev_id = dev_id;
err:
    return errcode;
}


/*
 * OUT EP event (data recv) for EP 0
 */

/* @
    @ behavior ctx_not_found:
    @   assumes \forall integer i ; 0 <= i < num_ctx ==> ctx_list[i].dev_id != dev_id ;
    @   assigns \nothing ;    
    @   ensures \result == MBED_ERROR_NOTFOUND ;

    @ behavior ctx_found_USB_BACKEND_DRV_EP_STATE_SETUP_SIZE_8 :
    @   assumes \exists integer i ; 0 <= i < num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assumes usbotghs_ctx.in_eps[ep].state == USB_BACKEND_DRV_EP_STATE_SETUP ;
    @   assumes size == 8 ;
    @   assigns *ctx_list ;
    @   ensures \result == ;


    @ complete behaviors ;
    @ disjoint behaviors ;
*/

// cyril : probleme, je dois faire référence à usbotghs_ctx.in_eps[epnum].state pour les différents comportements
// usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_SETUP
// usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_DATA_OUT
// usbotghs_ctx.out_eps[ep].state != des deux autres états.
// tentative avec GHOST_usbotghs_ctx->out_eps[ep].state
// comment parcourir la fonction avec plusieurs états?

mbed_error_t usbctrl_handle_outepevent(uint32_t dev_id, uint32_t size, uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;

    log_printf("[LIBCTRL] handle Oepevent\n");
    /* get back associated context */
    if ((errcode = usbctrl_get_context(dev_id, &ctx)) != MBED_ERROR_NONE) {
        log_printf("[LIBCTRL] oepint: enable to get ctx !\n");
        goto err;
    }

    /* at ouepevent time, the EP can be in SETUP state or in DATA OUT state.
     * In the first case, we have received a SETUP packet, targetting the libctrl,
     * in the second case, we have received some data, targetting one of the
     * interface which has registered a DATA EP with the corresponding EP id */
    
    //#if defined(__FRAMAC__)
    //uint8_t State = Frama_C_interval(0,9);
    //switch(State){
    //#else
    switch (usb_backend_drv_get_ep_state(ep, USB_BACKEND_DRV_EP_DIR_OUT)) { // cyril : faire une "fausse fonction" avec juste des spec qui renvoient un état ?
    //#endif/*!__FRAMAC__*/                                                 // ou modifier la spec de usb_backend_drv_get_ep_state
        
        case USB_BACKEND_DRV_EP_STATE_SETUP:
            log_printf("[LIBCTRL] oepint: a setup pkt transfert has been fully received. Handle it !\n");
            if (size == 8) {
                /* first, we should not accept setup pkt from other EP than 0.
                 * Although, this is not forbidden by USB 2.0 standard. */
                /* Second, we must convert received data into current endianess */
                uint8_t *setup_packet = ctx->ctrl_fifo;
                usbctrl_setup_pkt_t formated_pkt = {
                    setup_packet[0],
                    setup_packet[1],
                    setup_packet[3] << 8 | setup_packet[2],
                    setup_packet[5] << 8 | setup_packet[4],
                    setup_packet[7] << 8 | setup_packet[6]
                };
                errcode = usbctrl_handle_requests(&formated_pkt, dev_id);
                usb_backend_drv_ack(EP0, USB_EP_DIR_OUT);
                return errcode;
            } else {  // Cyril : pas de errcode ici, donc \result == MBED_ERROR_NONE, c'est normal?
                log_printf("[LIBCTRL] recv setup pkt size != 8: %d\n", size);
                usb_backend_drv_stall(ep, USB_BACKEND_DRV_EP_DIR_OUT);
            }
            break;
        case USB_BACKEND_DRV_EP_STATE_DATA_OUT: {
            uint8_t curr_cfg = ctx->curr_cfg;
            if (size == 0) {
                /* Well; nothing to do with size = 0 ? */
                break;
            }
            /*@
                @ loop invariant 0 <= iface <= ctx->cfg[curr_cfg].interface_num ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface].eps + (ctx->cfg[curr_cfg].interface_num-1));
                @ loop assigns iface ;
                @ loop variant (ctx->cfg[curr_cfg].interface_num -iface) ;
            */

            for (uint8_t iface = 0; iface < ctx->cfg[curr_cfg].interface_num; ++iface) {
            
            /*@
                @ loop invariant 0 <= i <= ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface].eps + (ctx->cfg[curr_cfg].interface_num-1));
                @ loop assigns i ;
                @ loop variant (ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number -i);
            */


                for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number; ++i) {
                    /* here we check both ep id and direction and EP0 is a specific full duplex case */
                    if (   ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num == ep
                        && ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir == USB_EP_DIR_OUT) {
                        /*
                         * XXX: when using ctx->ctrl_req_processing flag, is the FIFO comparison
                         * still useful ?
                         * Though. We *must* set the recv FIFO again, considering that no
                         * DATA in on EP0 happen for CTRL lib, only for upper stack.
                         */
                        /* EP0 special: We have received data from the host on CTRL EP.
                         * These data can target our CTRL usage,  or another upper stack one's...
                         * We can differenciate such cases by compare the currently configured
                         * FIFO at driver level with our ususal recv FIFO. If the driver,
                         * during the rxflvl time, used a FIFO not controlled by us, this means
                         * that the current DATA out transfer is not for us.
                         * In that last case:
                         * 1. we call the upper layer stack
                         * 2. we set back our FIFO to handle properly next setup packets
                         */
                        log_printf("[LIBCTRL] oepint: executing upper data handler (0x%x) for EP %d (size %d)\n",ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler, ep, size);
                        if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler) {
                            ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler(dev_id, size, ep);
                            /* now that data are transfered (oepint finished) whe can set back our FIFO for
                             * EP0, in order to support next EP0 events */
                            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
                        }
                        goto err;
                    }
                }
            }
            /* if we arrive here, this means that no active EP has been found above, corresponding to
             * the EP on which we have received some content. This is *not* a valid behavior, and we
             * should inform the host of this */
            errcode = MBED_ERROR_INVSTATE;
            usb_backend_drv_nak(ep, USB_BACKEND_DRV_EP_DIR_OUT);
        }
        default:
            log_printf("[LIBCTRL] oepint: EP not in good state: %d !\n",
                    usb_backend_drv_get_ep_state(ep, USB_BACKEND_DRV_EP_DIR_OUT));
            break;
    }
err:
    return errcode;
}

mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

#define MAX_DESC_STRING_SIZE 32 /* max unicode string size supported (to define properly) */
/*
 * USB configuration descriptor. Global to the device, specify the
 * device configuration (number of interfaces, power, ...)
 */
typedef struct __packed usb_configuration_descriptor {
    uint8_t bLength;
    uint8_t bDescriptorType;
    uint16_t wTotalLength;
    uint8_t bNumInterfaces;
    uint8_t bConfigurationValue;
    uint8_t iConfiguration;
    struct {
        uint8_t reserved:5;
        uint8_t remote_wakeup:1;
        uint8_t self_powered:1;
        uint8_t reserved7:1;
    } bmAttributes;
    uint8_t bMaxPower;
} usb_configuration_descriptor_t;

/**
 * Interface descriptor set,
 */
/**
 * Endpoint descriptor set for run-time mode (only?).
 */
/* old
typedef struct __packed usb_ctrl_full_configuration_descriptor {
    usb_configuration_descriptor_t config;
    union {
        usb_ctr_full_endpoint_descriptor_t ep;
        usb_functional_descriptor_t functional_desc;
    };
} usb_ctrl_configuration_descriptor_t;
*/

/**
 * \brief String descriptor.
 */

/*
 * It is considered here that the buffer is large enough to hold the
 * requested descriptor. The buffer size is under the control of the
 * get_descriptor standard request handler
 */

/*@
    @ requires is_valid_descriptor_type(type); 
    @ requires \separated(buf,desc_size,ctx,pkt);  // cyril : je ne pense pas que separated sans valid soit une utilisation correcte

    @ behavior invaparam:
    @   assumes  (buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior USB_DESC_DEVICE:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_DEVICE ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == sizeof(usbctrl_device_descriptor_t) ;

    @ behavior USB_DESC_INTERFACE:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_INTERFACE ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;

    @ behavior USB_DESC_ENDPOINT:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_ENDPOINT ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;

    @ behavior USB_DESC_STRING:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_STRING ;
    @   ensures (\result == MBED_ERROR_UNSUPORTED_CMD &&  *desc_size == 0) ||
         (\result == MBED_ERROR_NONE && (*desc_size == 4 || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER)) 
                                    || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME)) || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL) ))) ;

    @ behavior USB_DESC_CONFIGURATION:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_CONFIGURATION ;
    @   ensures is_valid_error(\result) ;

    @ behavior USB_DESC_DEV_QUALIFIER:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_DEV_QUALIFIER ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;   

    @ behavior USB_DESC_OTHER_SPEED_CFG:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_OTHER_SPEED_CFG ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;  

    @ behavior USB_DESC_IFACE_POWER:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_IFACE_POWER ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;    

    @ behavior other_type:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes (type != USB_DESC_DEVICE) && (type != USB_DESC_INTERFACE) && (type != USB_DESC_ENDPOINT) && (type != USB_DESC_STRING) && (type != USB_DESC_CONFIGURATION) &&
                (type != USB_DESC_DEV_QUALIFIER) && (type != USB_DESC_OTHER_SPEED_CFG) && (type != USB_DESC_IFACE_POWER) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
    1 problemes pour finir de spécifier la fonction:  cast du type : usbctrl_device_descriptor_t *desc = (usbctrl_device_descriptor_t*)buf;  
                            desc->bLength = sizeof(usbctrl_device_descriptor_t);
            wp est perdu, assigns *buf ne passe pas (en même temps, buf est de type uin8_t *...)

    un bug :   uint32_t max_buf_size = *desc_size - curr_offset
                *desc_size quand on arrive ici vaut 0... alors que curr_offset >0
                probleme pour EVA  assert rte: unsigned_overflow: 0 ≤ *desc_size - curr_offset;

    pour le compteur poll, eva n'arrive pas à prouver qu'il reste >= 0

    les loop assigns ne passent pas également

*/


mbed_error_t usbctrl_get_descriptor(__in usbctrl_descriptor_type_t  type,
                                    __out uint8_t                   *buf,
                                    __out uint32_t                  *desc_size,
                                    __in  usbctrl_context_t         *ctx,
                                    __in usbctrl_setup_pkt_t       *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitation */
    if (buf == NULL || ctx == NULL || desc_size == NULL || pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    #if defined(__FRAMAC__)
    const char *USB_DEV_MANUFACTURER = CONFIG_USB_DEV_MANUFACTURER;  
    const char *USB_DEV_PRODNAME = CONFIG_USB_DEV_PRODNAME;  
    const char *USB_DEV_SERIAL = CONFIG_USB_DEV_SERIAL;  
    #endif/*__FRAMAC__*/


    switch (type) {
        case USB_DESC_DEVICE: {
            log_printf("[USBCTRL] request device desc (num cfg: %d)\n", ctx->num_cfg);
            usbctrl_device_descriptor_t *desc = (usbctrl_device_descriptor_t*)buf;  
            desc->bLength = sizeof(usbctrl_device_descriptor_t);
            desc->bDescriptorType = 0x1; /* USB Desc Device */
            desc->bcdUSB = 0x0200; /* USB 2.0 */
            desc->bDeviceClass = 0; /* replaced by default iface */
            desc->bDeviceSubClass = 0;
            desc->bDeviceProtocol = 0;
            desc->bMaxPacketSize = 64; /* on EP0 */
            desc->idVendor = CONFIG_USB_DEV_VENDORID;
            desc->idProduct = CONFIG_USB_DEV_PRODUCTID;
            desc->bcdDevice = 0x000;
            desc->iManufacturer = CONFIG_USB_DEV_MANUFACTURER_INDEX;
            desc->iProduct = CONFIG_USB_DEV_PRODNAME_INDEX;
            desc->iSerialNumber = CONFIG_USB_DEV_SERIAL_INDEX;
            desc->bNumConfigurations = ctx->num_cfg;

#if 0
            /* if we have only one cfg and one iface, we can set device-wide
             * information from iface */
            if (ctx->num_cfg == 1 && ctx->cfg[ctx->curr_cfg].interface_num == 1) {
                desc->bDeviceClass = ctx->cfg[ctx->curr_cfg].interfaces[0].usb_class;
                desc->bDeviceSubClass = ctx->cfg[ctx->curr_cfg].interfaces[0].usb_subclass;
                desc->bDeviceProtocol = ctx->cfg[ctx->curr_cfg].interfaces[0].usb_protocol;
            }
#endif
            *desc_size = sizeof(usbctrl_device_descriptor_t);
            break;
        }
        case USB_DESC_INTERFACE:
            log_printf("[USBCTRL] request iface desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_ENDPOINT:
            log_printf("[USBCTRL] request EP desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_STRING: {
            log_printf("[USBCTRL] request string desc\n");
            *desc_size = 0;
            uint32_t descriptor_size = sizeof(usbctrl_string_descriptor_t);
            if (descriptor_size > MAX_DESCRIPTOR_LEN) {
                log_printf("[USBCTRL] not enough space for string descriptor !!!\n");
                errcode = MBED_ERROR_UNSUPORTED_CMD;
                *desc_size = 0;
                goto err;
            }
            log_printf("[USBCTRL] create string desc of size %d\n", descriptor_size);
            {
                uint8_t *string_desc = buf;
                usbctrl_string_descriptor_t *cfg = (usbctrl_string_descriptor_t *)&(string_desc[0]);
                uint8_t string_type = pkt->wValue & 0xff;
                cfg->bDescriptorType = USB_DESC_STRING;
                /* INFO:  UTF16 double each size */
                #if defined(__FRAMAC__)  
                
                switch (string_type) {
                    case 0:
                        cfg->bLength = 4;
                        cfg->wString[0] = LANGUAGE_ENGLISH;
                        *desc_size = 4;
                        break;

                  
                    case CONFIG_USB_DEV_MANUFACTURER_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);

                        /*@
                            @ loop invariant \valid(cfg->wString + (0..(sizeof(USB_DEV_MANUFACTURER)-1)));
                            @ loop invariant \valid_read(USB_DEV_MANUFACTURER + (0..(sizeof(CONFIG_USB_DEV_MANUFACTURER)-1)));
                            @ loop invariant 0 <= i <= sizeof(CONFIG_USB_DEV_MANUFACTURER) ;
                            @ loop assigns i, *cfg ;
                            @ loop variant sizeof(CONFIG_USB_DEV_MANUFACTURER) - i ;
                        */

                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_MANUFACTURER); ++i) {
                            cfg->wString[i] = USB_DEV_MANUFACTURER[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);
                        break;
                    case CONFIG_USB_DEV_PRODNAME_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);
                        
                        /*@
                            @ loop invariant \valid(cfg->wString + (0..(sizeof(CONFIG_USB_DEV_PRODNAME)-1)));
                            @ loop invariant \valid_read(USB_DEV_PRODNAME + (0..(sizeof(CONFIG_USB_DEV_PRODNAME)-1)));
                            @ loop invariant 0 <= i <= sizeof(CONFIG_USB_DEV_PRODNAME) ;
                            @ loop assigns i, *cfg ;
                            @ loop variant sizeof(CONFIG_USB_DEV_PRODNAME) - i ;
                        */

                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_PRODNAME); ++i) {
                            cfg->wString[i] = USB_DEV_PRODNAME[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);
                        break;
                    case CONFIG_USB_DEV_SERIAL_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);
                        
                        /*@
                            @ loop invariant \valid(cfg->wString + (0..(sizeof(CONFIG_USB_DEV_SERIAL)-1)));
                            @ loop invariant \valid_read(USB_DEV_SERIAL + (0..(sizeof(CONFIG_USB_DEV_SERIAL)-1)));
                            @ loop invariant 0 <= i <= sizeof(CONFIG_USB_DEV_SERIAL) ;
                            @ loop assigns i, *cfg ;
                            @ loop variant sizeof(CONFIG_USB_DEV_SERIAL) - i ;
                        */
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_SERIAL); ++i) {
                            cfg->wString[i] = USB_DEV_SERIAL[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);
                        break;
                    default:
                        log_printf("[USBCTRL] Unsupported string index requested.\n");
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                        break;
                }
            #else

                switch (string_type) {
                    case 0:
                        cfg->bLength = 4;
                        cfg->wString[0] = LANGUAGE_ENGLISH;
                        *desc_size = 4;
                        break;
                  
                    case CONFIG_USB_DEV_MANUFACTURER_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_MANUFACTURER); ++i) {
                            cfg->wString[i] = CONFIG_USB_DEV_MANUFACTURER[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);
                        break;
                    case CONFIG_USB_DEV_PRODNAME_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);
                        
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_PRODNAME); ++i) {
                            cfg->wString[i] = CONFIG_USB_DEV_PRODNAME[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);
                        break;
                    case CONFIG_USB_DEV_SERIAL_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);
                        
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_SERIAL); ++i) {
                            cfg->wString[i] = CONFIG_USB_DEV_SERIAL[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);
                        break;
                    default:
                        log_printf("[USBCTRL] Unsupported string index requested.\n");
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                        break;
                }

            #endif/*__FRAMAC__*/
            }
            break;
        }
        case USB_DESC_CONFIGURATION: { 
            log_printf("[USBCTRL] request configuration desc\n");
            /* configuration descriptor is dynamic, depends on current config and its number of endpoints... */
            /* FIXME, we should be able to return a config descriptor with more
             * than one interface if needed, including potential successive
             * iface & EPs descriptors */
            /* 1) calculating desc size */
            //uint8_t requested_configuration = pkt->wValue; /* TODO to be used */
            uint8_t curr_cfg = ctx->curr_cfg;
            uint8_t iface_num = ctx->cfg[curr_cfg].interface_num;

            /* is there, at upper layer, an additional class descriptor for
             * current configuration ? if yes, we get back this descriptor
             * and add it to the complete configuration descriptor we send
             * to the host. */
            /* Here, we only calculate, for each interface, if there is a
             * class descriptor, its size. The effective descriptor will
             * be stored later, when the overall configuration descriptor
             * is forged. */
            uint32_t class_desc_size = 0;
            uint32_t handler;

            if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
                log_printf("[LIBCTRL] didn't get back handler from ctx\n");
                goto err;
            }
         
            /* @
                @ loop invariant 0 <= i <= iface_num ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num-1)));
                @ loop invariant \separated(buf,ctx);
                @ loop assigns i, class_desc_size, errcode  ;
                @ loop variant (iface_num -i);
            */

            for (uint8_t i = 0; i < iface_num; ++i) {
                if (ctx->cfg[curr_cfg].interfaces[i].class_desc_handler != NULL) {
                    uint32_t max_buf_size = MAX_DESCRIPTOR_LEN;
                    /*@ assert ctx->cfg[curr_cfg].interfaces[i].class_desc_handler ∈ {&class_get_descriptor}; */
                    /*@ calls class_get_descriptor; */
                    errcode = ctx->cfg[curr_cfg].interfaces[i].class_desc_handler(i, buf, &max_buf_size, handler);
                    if (errcode != MBED_ERROR_NONE) {
                        log_printf("[LIBCTRL] failure while getting class desc: %d\n", errcode);
                        goto err;
                    }
                    log_printf("[LIBCTRL] found one class level descriptor of size %d\n", max_buf_size);
                    class_desc_size += max_buf_size;
                }
            }

            /*
             * Calculate and generate the complete configuration descriptor
             */
            /* then calculate the overall descriptor size */
            uint32_t descriptor_size = sizeof(usbctrl_configuration_descriptor_t);
 
             /* @
                @ loop invariant 0 <= i <= iface_num ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num-1)));
                @ loop assigns i, descriptor_size  ;
                @ loop variant (iface_num -i);
            */           


            for (uint8_t i = 0; i < iface_num; ++i) {
                /* for endpoint, we must not declare CONTROL eps in interface descriptor */
                uint8_t num_ep = 0;
                
                /* @
                    @ loop invariant 0 <= ep <= ctx->cfg[curr_cfg].interfaces[i].usb_ep_number ;
                    @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[i].eps + (0..(ctx->cfg[curr_cfg].interfaces[i].usb_ep_number -1))) ;
                    @ loop assigns num_ep, ep ;
                    @ loop variant (ctx->cfg[curr_cfg].interfaces[i].usb_ep_number - ep);
                */

                for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[i].usb_ep_number; ++ep) {
                    if (ctx->cfg[curr_cfg].interfaces[i].eps[ep].type != USB_EP_TYPE_CONTROL) {
                        ++num_ep;
                    }
                }
                descriptor_size += sizeof(usbctrl_interface_descriptor_t) + num_ep * sizeof(usbctrl_endpoint_descriptor_t);
            }
            
            /* we add potential class descriptors found above ... From now on, the global descriptor size is
             * complete, and can be sanitized properly in comparison with the passed buffer size */
            descriptor_size += class_desc_size;

            if (descriptor_size > MAX_DESCRIPTOR_LEN) {
                log_printf("[USBCTRL] not enough space for config descriptor !!!\n");
                errcode = MBED_ERROR_UNSUPORTED_CMD;
                *desc_size = 0;
                goto err;
            }
            log_printf("[USBCTRL] create config desc of size %d with %d ifaces\n", descriptor_size, iface_num);
            uint32_t curr_offset = 0;
            uint8_t *config_desc = &(buf[curr_offset]);
            {
                usbctrl_configuration_descriptor_t *cfg = (usbctrl_configuration_descriptor_t *)&(config_desc[0]);
                cfg->bLength = sizeof(usbctrl_configuration_descriptor_t);
                cfg->wTotalLength = descriptor_size;
                cfg->bDescriptorType = USB_DESC_CONFIGURATION;
                cfg->bNumInterfaces = iface_num;
                cfg->bConfigurationValue = 1;
                cfg->iConfiguration = 0;
                cfg->bmAttributes.reserved7 = 1;
                cfg->bmAttributes.self_powered = 1;
                cfg->bmAttributes.remote_wakeup = 0;
                cfg->bmAttributes.reserved = 0;
                cfg->bMaxPower = 0;
                curr_offset += sizeof(usbctrl_configuration_descriptor_t);
            }
            /* there can be 1, 2 or more interfaces. interfaces offset depends on the previous
             * interfaces number, and are calculated depending on the previous interfaces
             * descriptors (iface+ep) size.
             * To do this, we start at offset 0 after configuration descriptor for the first
             * interface, and at the end of each interface, we increment the offset of the size
             * of the complete interface descriptor, including EP. */
                                            
            /* @
                @ loop invariant 0 <= iface_id <= iface_num ;
                @ loop invariant 0 <= curr_offset <=  255 ; 
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num -1))) ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1))) ;
                @ loop invariant \valid(buf + (0..255));
                @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1)),buf + (0..255));
                @ loop assigns iface_id, curr_offset, errcode, buf[0..255] ;
                @ loop variant (iface_num - iface_id) ;
            */
            
            for (uint8_t iface_id = 0; iface_id < iface_num; ++iface_id) {
                    {
                        /* pointing to next field: interface descriptor */
                        usbctrl_interface_descriptor_t *cfg = (usbctrl_interface_descriptor_t*)&(buf[curr_offset]);
                        /* @ assert &buf[curr_offset] ==  cfg ; */
                        cfg->bLength = sizeof(usbctrl_interface_descriptor_t);
                        cfg->bDescriptorType = USB_DESC_INTERFACE;
                        cfg->bInterfaceNumber = iface_id;
                        cfg->bAlternateSetting = 0;

                        uint8_t num_ep = 0;
                /* @
                    @ loop invariant 0 <= ep <= ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number ;
                    @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1))) ;
                    @ loop assigns num_ep, ep ;
                    @ loop variant (ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - ep);
                */

                        for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number; ++ep) {
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep].type != USB_EP_TYPE_CONTROL) {
                                ++num_ep;
                            }
                        }
                       
                        cfg->bNumEndpoints = num_ep;
                        cfg->bInterfaceClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_class;
                        cfg->bInterfaceSubClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_subclass;
                        cfg->bInterfaceProtocol = ctx->cfg[curr_cfg].interfaces[iface_id].usb_protocol;
                        cfg->iInterface = 1;
                        curr_offset += sizeof(usbctrl_interface_descriptor_t);
                    }
                    {
                        // class level descriptor of current interface 
                         #if defined(__FRAMAC__)
                         ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler = class_get_descriptor ; 
                         // Cyril : la ligne du dessus sert à faire passer EVA, je ne comprends pas pourquoi je n'entre pas dans le test sinon... 
                         #endif/*!__FRAMAC__*/

                        if (ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler != NULL) {
                            uint8_t *cfg = &(buf[curr_offset]);
                            uint32_t handler;
                            if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
                                log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
                            }
                            
                            #if defined(__FRAMAC__)
                            uint32_t max_buf_size = curr_offset ;  // Cyril : pour faire passer framaC sans erreur...
                            #else
                            uint32_t max_buf_size = *desc_size - curr_offset; 
                            #endif/*!__FRAMAC__*/

                            // Cyril : bug : *desc_size quand on arrive ici vaut 0... alors que curr_offset >0
                            // Cyril : probleme pour EVA /*@ assert rte: unsigned_overflow: 0 ≤ *desc_size - curr_offset; 

                            /*@ assert ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler ∈ {&class_get_descriptor}; */
                            /*@ calls class_get_descriptor; */
                            errcode = ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler(iface_id, cfg, &max_buf_size, handler);


                            if (errcode != MBED_ERROR_NONE) {
                                goto err;
                            }
                            curr_offset += max_buf_size;
                        }
                    }
                    {
                        /* and for this interface, handling each EP */

                        uint8_t poll ;
                /* @
                    @ loop invariant 0 <= ep_number <= ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number ;
                    @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - 1))) ;
                    @ loop invariant \valid(buf + (0..255));
                    @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - 1)),buf + (0..255));
                    @ loop invariant 0 <= curr_offset <=  255 ; 
                    @ loop assigns ep_number, poll, curr_offset, buf[0..255];
                    @ loop variant (ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - ep_number);
                */

                        for (uint8_t ep_number = 0; ep_number < ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number; ++ep_number) {
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type == USB_EP_TYPE_CONTROL) {
                                /* Control EP (EP0 usage) are not declared here */
                                continue;
                            }
                            usbctrl_endpoint_descriptor_t *cfg = (usbctrl_endpoint_descriptor_t*)&(buf[curr_offset]); // modèle mémoire cast à tester, sinon assert
                            cfg->bLength = sizeof(usbctrl_endpoint_descriptor_t);
                            cfg->bDescriptorType = USB_DESC_ENDPOINT;
                            cfg->bEndpointAddress = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].ep_num;
                          
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].dir == USB_EP_DIR_IN) {
                                cfg->bEndpointAddress |= 0x80; /* set bit 7 to 1 for IN EPs */
                            }

                            cfg->bmAttributes =
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type       |
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].attr << 2  |
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].usage << 4;
                            cfg->wMaxPacketSize = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].pkt_maxsize;
                            
                            /* See table 9.3: microframe interval: bInterval specification */
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type == USB_EP_TYPE_INTERRUPT) {
                                /* in case of HS driver, bInterval == 2^(interval-1), where interval is the
                                 * uframe length. In FS, the interval is free between 1 and 255. To simplify
                                 * the handling of bInterval, knowing that drivers both set uFrame interval to 3
                                 * we use the same 2^(interval-1) calculation for HS and FS */
                                /* TODO: here, we consider that the usb backend driver set the uFrame interval to 3,
                                 * it would be better to get back the uFrame interval from the driver and calculate
                                 * the bInterval value */
                                /* calculating interval depending on backend driver, to get
                                 * back the same polling interval (i.e. 64 ms, hardcoded by now */
                                poll = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].poll_interval;
                                /* falling back to 1ms polling, if not set */
                                if (poll == 0) {
                                    log_printf("[USBCTRL] invalid poll interval %d\n", poll);
                                    poll = 1;
                                }
                                if (usb_backend_drv_get_speed() == USB_BACKEND_DRV_PORT_HIGHSPEED) {
                                    /* value in poll is set in ms, in HS, value is 2^(interval-1)*125us
                                     * here, we get the position of the first bit at 1 in poll value, and add 2 to this
                                     * value, to get the same result as the above */
                                    uint8_t i = 0;  // Cyril : on a déjà une boucle avec i déclaré, je pense qu'il faut nommer deux variables différentes (variable renommé en ep_number)
                                    /* get back the position of the first '1' bit */
                                    
                                    uint8_t compteur_poll = 9;
                                    /* @
                                        @ loop invariant i >= 0 ;
                                        @ loop invariant poll >= 0 ;
                                        @ loop invariant compteur_poll >= 0 ;
                                        @ loop assigns poll, i, compteur_poll;
                                        @ loop variant compteur_poll;
                                    */
                                      // Cyril : pour faire passer frama, on peut faire un compteur max de 9 (poll a 8 bits) pour faire un variant sur ce compteur...
                                      // ou 9 -i en variant  
                                    while (!(poll & 0x1) || compteur_poll > 0) {
                                        poll >>= 1;
                                        i++;
                                        compteur_poll -- ;  // cyril : faux positif avec EVA, qui n'arrive pas à vérifier que compteur_poll >= 0 (ça passe avec wp)
                                    }
                                    /* binary shift left by 2, to handle (interval-1)*125us from a value in milisecond */
                                    i+=2;
                                    cfg->bInterval = i;
                                 } else {
                                    /* in Fullspeed, the bInterval field is directly set in ms, between 1 and 255 */
                                    cfg->bInterval = poll;
                                  }
                            } else {
                                /* for BULK EP, we set bInterval to 0 */
                                cfg->bInterval = 0;
                            }
                            curr_offset += sizeof(usbctrl_endpoint_descriptor_t);
                        }
                        
                    }
            /* returns the descriptor */
            }
            *desc_size = descriptor_size;
            break;
        }
        case USB_DESC_DEV_QUALIFIER:
            log_printf("[USBCTRL] request dev qualifier desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_OTHER_SPEED_CFG:
            log_printf("[USBCTRL] request other speed cfg desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_IFACE_POWER:
            log_printf("[USBCTRL] request iface power desc\n");
            *desc_size = 0;
            break;
        default:
            log_printf("[USBCTRL] request unknown desc\n");
            errcode = MBED_ERROR_INVPARAM;
            goto err;
    }
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

//@ assigns Frama_C_entropy_source \from Frama_C_entropy_source;
void Frama_C_update_entropy(void) {
  Frama_C_entropy_source = Frama_C_entropy_source;
}

int Frama_C_interval(int min, int max)
{
  int r,aux;
  Frama_C_update_entropy();
  aux = Frama_C_entropy_source;
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

    uint32_t dev_id = Frama_C_interval(0,RAND_UINT_32-1) ;
    uint32_t size = Frama_C_interval(0,RAND_UINT_32-1) ;
    uint32_t ctxh = Frama_C_interval(0,MAX_USB_CTRL_CTX-1);
    uint32_t handler = Frama_C_interval(0,RAND_UINT_32-1);
    uint8_t ep = Frama_C_interval(0,255);
    uint8_t iface = Frama_C_interval(0,MAX_INTERFACES_PER_DEVICE-1);
    uint8_t ep_number = Frama_C_interval(0,MAX_EP_PER_INTERFACE);
    uint8_t EP_type = Frama_C_interval(0,3);
    uint8_t EP_dir = Frama_C_interval(0,1);
    uint8_t  USB_class = Frama_C_interval(0,17);
    uint32_t USBdci_handler = Frama_C_interval(0,RAND_UINT_32-1) ;


/*
    def d'une nouvelle interface pour test de la fonction usbctrl_declare_interface
    Déclaration d'une structure usb_rqst_handler_t utilisée dans les interfaces, qui nécessite aussi une structure usbctrl_setup_pkt_t
*/

    uint8_t RequestType = Frama_C_interval(0,255);
    uint8_t Request = Frama_C_interval(0,255);
    uint16_t Value = Frama_C_interval(0,65535);
    uint16_t Index = Frama_C_interval(0,65535);  // Cyril : à confirmer avec Philippe que Index commence bien à 1 (sinon bug dans usbctrl_handle_class_requests)
    uint16_t Length = Frama_C_interval(0,65535);

	usbctrl_setup_pkt_t pkt = { .bmRequestType = RequestType, .bRequest = Request, .wValue = Value, .wIndex = Index, .wLength = Length };
	usbctrl_interface_t iface_1 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
								  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep,
                                  .rqst_handler = usbctrl_class_rqst_handler, .class_desc_handler = class_get_descriptor};
	usbctrl_interface_t iface_2 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
	                              .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep,
                                   .rqst_handler = usbctrl_class_rqst_handler, .class_desc_handler = class_get_descriptor};

    /*@ assert  \valid(ctx_list + (0 .. (MAX_USB_CTRL_CTX - 1))); */
	/*@ assert 0 <= num_ctx < MAX_USB_CTRL_CTX ; */

    usbctrl_declare(dev_id, &ctxh);

    /*@ assert 0 <= num_ctx < MAX_USB_CTRL_CTX ; */

    usbctrl_initialize(ctxh);
    usbctrl_declare_interface(ctxh, &iface_1) ;
    usbctrl_get_interface((usbctrl_context_t *)&(ctx_list[ctxh]), iface);
    usbctrl_get_handler((usbctrl_context_t *)&(ctx_list[ctxh]), &handler);

    usbctrl_context_t *ctx1 = NULL;

    usbctrl_get_context(dev_id, &ctx1);
    usbctrl_declare_interface(ctxh, &iface_2);
    usbctrl_get_interface((usbctrl_context_t *)&(ctx_list[ctxh]), iface);
    usbctrl_is_endpoint_exists((usbctrl_context_t *)&(ctx_list[ctxh]), ep);
    usbctrl_is_interface_exists((usbctrl_context_t *)&(ctx_list[ctxh]), iface);
    usbctrl_start_device(ctxh) ;
    usbctrl_stop_device(ctxh) ;
/*
    appel des différentes fonctions de la libxDCI
*/

    ctx_list[ctxh].state = Frama_C_interval(0,9);  // pour EVA, pour avoir tous les états possibles notamment pour la fonction usbctrl_handle_reset

    usbctrl_handle_reset(dev_id);
    usbctrl_handle_inepevent(dev_id, size, ep);
    usbctrl_handle_outepevent(dev_id, size, ep);  // voir comment l'appeler, je dois être dans certains états je pense    												// USB_BACKEND_DRV_EP_STATE_SETUP ou USB_BACKEND_DRV_EP_STATE_DATA_OUT
    usbctrl_handle_requests(&pkt, dev_id) ;
    usbctrl_handle_class_requests(&pkt,&(ctx_list[ctxh])) ;
    usbctrl_handle_earlysuspend(dev_id) ;
    usbctrl_handle_usbsuspend(dev_id);
    usbctrl_handle_wakeup(dev_id) ;
    usbctrl_std_req_get_dir(&pkt) ;
    //usbctrl_std_req_handle_get_status(&pkt, &(ctx_list[ctxh])) ; // pour avoir pkt->wLength qui varie pour parcourir la fonction send_data. Mais ça génère plein de pb...

}

/*

 test_fcn_erreur : test des fonctons définies dans usbctrl.c afin d'atteindre les portions de code défensif
 					(pointeurs nulls, débordement de tableaux...)

*/

void test_fcn_usbctrl_erreur(){

	uint32_t dev_id = Frama_C_interval(0,RAND_UINT_32-1) ;
	uint8_t iface = Frama_C_interval(0,MAX_INTERFACES_PER_DEVICE-1);
	uint8_t ep = Frama_C_interval(0,255);
	uint32_t ctxh ;

	/*
		usbctrl_declare : cas d'erreur - pointeur ctxh null
									   - num_ctx >= 2
						deux appels à la fonction pour tester ces cas d'erreur
	*/

	uint32_t *bad_ctxh = NULL;
	usbctrl_declare(dev_id, bad_ctxh);

	ctxh = 1 ;
	num_ctx = 2;
	usbctrl_declare(dev_id, &ctxh);

	/*
		usbctrl_declare : cas d'erreur : ctxh >= num_ctx
	*/

	ctxh = 1 ;
	num_ctx = 0 ;
	usbctrl_initialize(ctxh);

	/*
		usbctrl_declare_interface : cas d'erreur - ctxh >= num_ctx
												 - pointeur iface == null
												 - interface_num >= MAX_INTERFACES_PER_DEVICE
												 - pkt_maxsize > usbotghs_get_ep_mpsize()
		Dans le cas nominal, avec le test sur 2 interfaces, num_cfg >= MAX_USB_CTRL_CTX-1 donc une partie du code n'est pas atteinte. Cas traité ci-dessous, quand on rajoute
		une interface de contrôle
	*/

	ctxh = 1 ;
	num_ctx = 0 ;
	usbctrl_interface_t *iface_1 = NULL ;
	usbctrl_declare_interface(ctxh, iface_1) ;

	ctxh = 0 ;
	num_ctx = 1 ;
	usbctrl_declare_interface(ctxh, iface_1) ;

	usbctrl_interface_t iface_2 = {.usb_class = 0, .usb_ep_number = 2, .dedicated = true, .eps[0].type = 3, .eps[0].pkt_maxsize = MAX_EPx_PKT_SIZE + 1 };
	ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE ;
	usbctrl_declare_interface(ctxh, &iface_2) ;

	//ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE - 1 ;
	//ctx_list[ctxh].cfg[0].interfaces[0].eps[0].pkt_maxsize = MAX_EPx_PKT_SIZE + 1 ;
	//usbctrl_declare_interface(ctxh, &iface_2) ;

	ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE - 1 ;
	ctx_list[ctxh].num_cfg < MAX_USB_CTRL_CTX -1  ;
	usbctrl_declare_interface(ctxh, &iface_2) ;



	/*
		usbctrl_get_interface : cas d'erreur - pointeur ctx null
		cas iface < ctx->cfg[ctx->curr_cfg].interface_num pas atteint dans le cas nominal
	*/
	usbctrl_context_t *bad_ctx = NULL ;
	usbctrl_get_interface(bad_ctx, iface);

	ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE ;
	usbctrl_get_interface((usbctrl_context_t *)&(ctx_list[ctxh]), iface);

	/*
		usbctrl_get_handler : cas d'erreur - pointeur ctx null
										   - pointeur handler null
		comme num_ctx < MAX_USB_CTRL_CTX pour ne pas avoir de débordement de tableau, la boucle n'est parcourue qu'une fois dans la fonction
	*/

	uint32_t handler = 1 ;
	usbctrl_get_handler(bad_ctx, &handler);

	uint32_t *bad_handler = NULL ;
	usbctrl_get_handler((usbctrl_context_t *)&(ctx_list[ctxh]), bad_handler);

	/*
		usbctrl_get_context, usbctrl_is_endpoint_exists &&  usbctrl_is_interface_exists  : cas d'erreur - pointeur ctx null
	*/
	usbctrl_context_t **bad_ctx1 = NULL ;
    usbctrl_get_context(dev_id, bad_ctx1);
    usbctrl_is_endpoint_exists(bad_ctx, ep);
    usbctrl_is_interface_exists(bad_ctx, iface);

    //usbctrl_std_req_handle_get_status(usbctrl_setup_pkt_t *pkt, usbctrl_context_t *ctx)
}

int main(void)
{

    test_fcn_usbctrl() ;
    test_fcn_usbctrl_erreur() ;
    test_fcn_driver_eva() ;


}
#endif/*!__FRAMAC__*/
