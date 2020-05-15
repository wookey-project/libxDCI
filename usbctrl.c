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

#include "driver_api/usbotghs_frama.h"
#include "api/libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
#include "usbctrl_state.h"
#include "socs/stm32f439/devlist.h"
#include "socs/stm32f439/usbotghs_fifos.h"
#include "usbctrl_handlers.h"
#include "usbctrl.h"


/*
 * by now, the libusbctrl handle upto 2 USB Ctrl context,
 * which means that an application can handle up to 2 USB blocks
 * with 2 dedicated context that may completely differ.
 *
 */

#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX

#if defined(__FRAMAC__)
static  uint8_t num_ctx = 0;
usbctrl_context_t    ctx_list[MAX_USB_CTRL_CTX] = { 0 }; 
#define MAX_EPx_PKT_SIZE 512
#define RAND_UINT_32 65535 

#else
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
    @   assigns *ctxh ;
    @   assigns ctx_list[\old(num_ctx)] ;
    @   assigns num_ctx ;
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_UNKNOWN ;
    @   ensures *ctxh == \old(num_ctx) ;
    @   ensures num_ctx == \old(num_ctx) +1 ;
    @   ensures ctx_list[\old(num_ctx)].dev_id == dev_id ;

    @ complete behaviors;
    @ disjoint behaviors;
*/

mbed_error_t usbctrl_declare(uint32_t dev_id,
                             uint32_t *ctxh)
{
    //log_printf("[USBCTRL] declaring USB backend\n");
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
        	errcode = usb_backend_drv_declare() ;  // Cyril : Frama-c semble avoir du mal avec l'alliasing...(les assigns ne passent pas)
            break;
        case USB_OTG_FS_ID:
        	errcode = usb_backend_drv_declare() ;  // Cyril : Frama-c semble avoir du mal avec l'alliasing...(les assigns ne passent pas)
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

    num_ctx++;  // Cyril : je pense qu'il faut ajouter un test ici si on depasse le nombre max de contexte pour ne pas avoir de débordement de tableau
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
    @	assigns ctx_list[ctxh] ;
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
    @	assigns \nothing ;    // Cyril : même si handler n'est pas modifié dans ce cas, je suppose que comme il y a loop assigns *handler, 
    							// wp considère qu'il peut bouger dès qu'on rentre dans la boucle
    @	ensures \result == MBED_ERROR_NOTFOUND ;

	@ behavior found :
    @	assumes ctx != \null && handler != \null ; 
    @	assumes \exists integer i ; 0 <= i < num_ctx && &(ctx_list[i]) == ctx ;
    @ 	assigns *handler ;
    @ 	ensures \result == MBED_ERROR_NONE  ;  // Cyril :ajout de || \result == MBED_ERROR_NOTFOUND 
    										   //  sinon ça ne passe pas avec wp, pourtant dans ce cas, il n'y a pas d'erreur...
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
    @	assigns \nothing ;    // Cyril : même si ctx n'est pas modifié dans ce cas, je suppose que comme il y a loop assigns *ctx, 
    							// wp considère qu'il peut bouger dès qu'on rentre dans la boucle
    @	ensures \result == MBED_ERROR_NOTFOUND ;

	@ behavior found :
    @	assumes ctx != \null ; 
    @	assumes \exists integer i ; 0 <= i < num_ctx && ctx_list[i].dev_id == device_id ;
    @ 	assigns *ctx ;
    @ 	ensures \result == MBED_ERROR_NONE ;  // Cyril :ajout de || \result == MBED_ERROR_NOTFOUND 
    										  //  sinon ça ne passe pas avec wp, pourtant dans ce cas, il n'y a pas d'erreur...
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
            /*@  assert errcode == MBED_ERROR_NONE ; */
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
    @   ensures \result == \true ;   // Cyril : là encore, wp n'y arrive que si j'ajoute || \result == \false, comme pour les 
    													  // fonctions get_context et get_handler
 
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
    @   assigns *iface ;
    @   assigns ctx_list[ctxh] ;
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
        //memcpy((void*)&(ctx->cfg[iface_config].interfaces[iface_num]), (void*)iface, sizeof(usbctrl_interface_t));

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
   /* 3) or, depending on the interface flags, add it to current config or to a new config */
   /* at declaration time, all interface EPs are disabled  and calculate EP identifier for the interface */


/*@
    @ loop invariant 0 <= i <= ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number ;
    @ loop invariant \valid(ctx->cfg[iface_config].interfaces[iface_num].eps +(0..(ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number-1))) ;
    @ loop invariant \valid(iface->eps+(0..(ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number-1))) ;
    @ loop invariant \separated(ctx->cfg[iface_config].interfaces[iface_num].eps +(0..(ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number-1)),iface->eps+(0..(ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number-1)));
    @ loop assigns i;
    @ loop assigns *iface ;
    @ loop assigns ctx_list[ctxh] ;
    @ loop assigns drv_ep_mpsize ;
    @ loop variant (ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number - i) ;
*/

   for (i = 0; i < ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number; ++i) {

    #if defined(__FRAMAC__)
      usb_ep_infos_t *ep = &(ctx->cfg[iface_config].interfaces[iface_num].eps[i]) ;
    #else
        volatile usb_ep_infos_t *ep = &(ctx->cfg[iface_config].interfaces[iface_num].eps[i]) ;
    #endif/*!__FRAMAC__*/

    ep->configured = false; //Cyril : où se fait la configuration de l'ep?
    /*@ assert ctx_list[ctxh].cfg[iface_config].interfaces[iface_num].eps[i].configured == false ; */


       if (ep->type == USB_EP_TYPE_CONTROL) {
           //printf("declare EP (control) id 0\n");
           ep->ep_num = 0;
           iface->eps[i].ep_num = 0;
       } else {
            ep->ep_num = ctx->cfg[iface_config].first_free_epid;
            iface->eps[i].ep_num = ep->ep_num;
           //printf("declare EP (not control) id %d\n", ep->ep_num);
           ctx->cfg[iface_config].first_free_epid++;          

           /* FIXME: max EP num must be compared to the MAX supported EP num at driver level */
           /* check that declared ep mpsize is compatible with backend driver */
           

#if defined(__FRAMAC__)
	   drv_ep_mpsize = MAX_EPx_PKT_SIZE ; // Cyril : l'appel à usb_backend_get_ep_mpsize ou directement à usbotghs_get_ep_mpsize pose des problemes à wp pour le assign
	   //		  dans la spec de la fonction. Je ne sais pas pourquoi...
#else
	   drv_ep_mpsize = usb_backend_get_ep_mpsize();;
#endif/*!__FRAMAC__*/

           if (ep->pkt_maxsize > drv_ep_mpsize) {
               //log_printf("truncating EP max packet size to backend driver EP max pktsize\n");
               ep->pkt_maxsize = drv_ep_mpsize;
           }
       }
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
    //PMO
    /* @ assert usbotghs_ctx.in_eps[0].mpsize !=0;*/ 
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
    uint16_t Index = Frama_C_interval(0,65535);
    uint16_t Length = Frama_C_interval(0,65535);

	usbctrl_setup_pkt_t pkt = { .bmRequestType = RequestType, .bRequest = Request, .wValue = Value, .wIndex = Index, .wLength = Length };
	usbctrl_interface_t iface_1 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
								  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep,
                                  .rqst_handler = usbctrl_class_rqst_handler , .class_desc_handler = class_get_descriptor};
	usbctrl_interface_t iface_2 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
	                              .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep,
                                   .rqst_handler = usbctrl_class_rqst_handler , .class_desc_handler = class_get_descriptor};

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
    usbctrl_start_device(ctxh);

/*
	handler fct : usbctrl_handle_requests

 * Global requests dispatcher. This function call the corresponding request handler, get back
 * its error code in return, release the EP0 receive FIFO lock and return the error code.

*/

    usbctrl_handle_reset(dev_id);  // attention, fonction modifiée pour commenter l'appel aux fonctions touchant aux registres...   
    usbctrl_handle_inepevent(dev_id, size, ep);
    usbctrl_handle_outepevent(dev_id, size, ep);  // voir comment l'appeler, je dois être dans certains états je pense    												// USB_BACKEND_DRV_EP_STATE_SETUP ou USB_BACKEND_DRV_EP_STATE_DATA_OUT
    usbctrl_handle_requests(&pkt, dev_id) ;
    
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

}

int main(void)
{
    
    test_fcn_usbctrl() ;
    test_fcn_usbctrl_erreur() ;

        
}
#endif/*!__FRAMAC__*/
