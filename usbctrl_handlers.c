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

#include "api/libusbctrl.h"
#include "usbctrl_handlers.h"
#include "usbctrl_state.h"
#include "usbctrl.h"


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


// PMO suppression des behaviors

/*@
    @ requires 0 < GHOST_num_ctx ; // reset after usbctrl_declare ok, so 0 < GHOST_num_ctx
    @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)),&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx,&usbotghs_ctx, &GHOST_idx_ctx); // PMO addition GHOST_idx_ctx
    @ requires \valid(ctx_list + (0..(GHOST_num_ctx-1))) ;
    @ assigns reset_requested, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx, GHOST_idx_ctx, ctx_list[0..(GHOST_num_ctx-1)] ; // moins .state PMO ctx_list[0..(GHOST_num_ctx-1)].state passe mais il faut ctx_list[GHOST_idx_ctx].state
    @ ensures GHOST_num_ctx == \old(GHOST_num_ctx) ;

    @ ensures \result == MBED_ERROR_INVPARAM
    ==>  !(\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list, Pre)[i].dev_id == dev_id)
    || ((usbotghs_ctx.out_eps[0].configured == \false) || (usbotghs_ctx.out_eps[0].mpsize == 0)) ;

    @ ensures \result == MBED_ERROR_INVSTATE && ctx_list[GHOST_idx_ctx].state == USB_DEVICE_STATE_INVALID
    ==>  (\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list, Pre)[i].dev_id == dev_id
     && !(\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list, Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET))
     && (0 <= GHOST_idx_ctx < GHOST_num_ctx) ;

    @ ensures \result == MBED_ERROR_NONE && ctx_list[GHOST_idx_ctx].state != USB_DEVICE_STATE_INVALID
    ==>(\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list, Pre)[i].dev_id == dev_id
    && (\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list, Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET))
    && !((usbotghs_ctx.out_eps[0].configured == \false) || (usbotghs_ctx.out_eps[0].mpsize == 0))
    && (0 <= GHOST_idx_ctx < GHOST_num_ctx) ;

*/

mbed_error_t usbctrl_handle_reset(uint32_t dev_id)
{

    mbed_error_t       errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;
    log_printf("[USBCTRL] Handling reset\n");
    /* TODO: support for multiple drivers in the same time.
    This requires a driver table with callbacks or a preprocessing mechanism
    to select the corresponding driver API. While the libctrl is not yet fully
    operational, we handle only usbotghs driver API */

    //dev_id = dev_id;

    log_printf("[USBCTRL] reset: get context for dev_id %d\n", dev_id);
    /*@ assert &ctx != NULL ; */
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] reset: no ctx found!\n");
     /*  assert ctx == &ctx_list[GHOST_idx_ctx] ; */
    /*@ assert &ctx != NULL ; */
        /*@ assert !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id) ; */
        /*  assert !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx == &ctx_list[i] && GHOST_idx_ctx == i ) ; */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id && GHOST_idx_ctx == i ) ; */
    /*  assert (\exists integer i ; 0 <= i < GHOST_num_ctx && ctx == &ctx_list[i] && GHOST_idx_ctx == i ) ; */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id) ; */
    /*@ assert ctx == &ctx_list[GHOST_idx_ctx] ; */
    /*@ assert ctx->state == ctx_list[GHOST_idx_ctx].state ; */
    /*@ assert 0 <= GHOST_idx_ctx < GHOST_num_ctx; */

    /*@ assert ctx != 0 ; */
    usb_device_state_t state = usbctrl_get_state(ctx);
    /*@ assert state == ctx->state ; */
    /*@ assert state == ctx_list[GHOST_idx_ctx].state ; */
    /*@ assert \at(ctx_list,Pre)[GHOST_idx_ctx].state == \at(ctx_list, Here)[GHOST_idx_ctx].state ; */
    /*@ assert \at(ctx_list,Pre)[GHOST_idx_ctx] == \at(ctx_list, Here)[GHOST_idx_ctx] ; */
    /*@ assert 0 <= GHOST_idx_ctx < GHOST_num_ctx; */


    /* resetting directly depends on the current state */
    if (!usbctrl_is_valid_transition(state, USB_DEVICE_TRANS_RESET, ctx)) {
        log_printf("[USBCTRL] RESET transition is invalid in current state !\n");

        /*@ assert  ctx_list[GHOST_idx_ctx].state  == USB_DEVICE_STATE_INVALID ; */
    /*@ assert !(\exists integer i; 0 <= i < GHOST_num_ctx && i!= GHOST_idx_ctx && \at(ctx_list,Pre)[i].state != ctx_list[i].state) ; */
    /*  assert ctx == &ctx_list[GHOST_idx_ctx] ; */
        /*  assert !(\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list, beforeif)[GHOST_idx_ctx].state].req_trans[j].request == USB_DEVICE_TRANS_RESET) ; */
    /*@ assert !(\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list, Pre)[GHOST_idx_ctx].state].req_trans[j].request == USB_DEVICE_TRANS_RESET) ; */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list,Pre)[i].dev_id == dev_id && !(\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list,Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET)) ; */
        errcode = MBED_ERROR_INVSTATE;
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list,Pre)[i].dev_id == dev_id && !(\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list,Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET)) ==> (errcode == MBED_ERROR_INVSTATE) ; */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list,Pre)[i].dev_id == dev_id && !(\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list,Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET)) ==> (errcode == MBED_ERROR_INVSTATE && ctx_list[GHOST_idx_ctx].state  == USB_DEVICE_STATE_INVALID) ; */
    /*@ assert 0 <= GHOST_idx_ctx < GHOST_num_ctx; */
        goto err;
    }
    /*@ assert errcode == MBED_ERROR_NONE ; */
    /*@ assert ctx_list[GHOST_idx_ctx]  == \at(ctx_list,Pre)[GHOST_idx_ctx] ; */
    /*@ assert ctx_list[GHOST_idx_ctx].state == \at(ctx_list,Pre)[GHOST_idx_ctx].state ; */
    /*@ assert (\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[ctx_list[GHOST_idx_ctx].state].req_trans[j].request == USB_DEVICE_TRANS_RESET) ; */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id && (\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list,Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET)) ; */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id && ctx_list[i].dev_id == \at(ctx_list,Pre)[i].dev_id); */
    /*  assert state == ctx_list[GHOST_idx_ctx].state ; */

    log_printf("[USBCTRL] reset: execute transition from state %d\n", state);
    /* handling RESET event depending on current state */
    switch (state) {
        case USB_DEVICE_STATE_POWERED:
            /* initial reset of the device, set EP0 FIFO. Other EPs FIFO
             * are handled at SetConfiguration & SetInterface time */
            /* as USB Reset action reinitialize the EP0 FIFOs (flush, purge and deconfigure) they must
             * be reconfigure for EP0 here. */
            /*  assert ctx_list[GHOST_idx_ctx].state == USB_DEVICE_STATE_POWERED ; */
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
    /*@ assert ctx ≡ &ctx_list[GHOST_idx_ctx]; */ ;
    /*@ assert !(\exists integer i; 0 <= i < GHOST_num_ctx && i!= GHOST_idx_ctx && \at(ctx_list,Pre)[i].state != ctx_list[i].state) ; */
    /*@ assert ctx_list[GHOST_idx_ctx].state!= USB_DEVICE_STATE_INVALID; */
    /*@ assert errcode == MBED_ERROR_NONE; */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list,Pre)[i].dev_id == dev_id && (\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list,Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET)); */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && \at(ctx_list,Pre)[i].dev_id == dev_id  && (\exists integer j ; 0 <= j < MAX_TRANSITION_STATE && usb_automaton[\at(ctx_list,Pre)[i].state ].req_trans[j].request == USB_DEVICE_TRANS_RESET)) ==>  ( errcode == MBED_ERROR_NONE  &&  ctx_list[GHOST_idx_ctx].state!= USB_DEVICE_STATE_INVALID ) ; */
err:
        /*@ assert !(\exists integer i; 0 <= i < GHOST_num_ctx && i!= GHOST_idx_ctx && \at(ctx_list,Pre)[i].state != ctx_list[i].state) ; */
    return errcode;
}



/*
 * IN EP event (data sent) for EP 0
 */

/*@
    @ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx,&usbotghs_ctx,&GHOST_idx_ctx);
    @ ensures GHOST_num_ctx == \old(GHOST_num_ctx) ;
    @   assigns ctx_list[0..(GHOST_num_ctx-1)],GHOST_idx_ctx ;  // cyril :c'est large mais ça passe, je ne sais pas comment faire un assigns plus précise (ctx_list[i])

    @ behavior ctx_not_found:
    @   assumes !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id) ;
    @   ensures \result == MBED_ERROR_NOTFOUND  ;

    @ behavior ctx_found :
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id  ;
    @   ensures is_valid_error(\result);
    @   ensures  (\exists integer i ; 0 <= i < GHOST_num_ctx && GHOST_idx_ctx == i ) ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
    TODO : spec très large pour ctx_found : possible de raffiner? pb, comment dire ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num == ep && ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir == USB_EP_DIR_IN
            à partir de ctx_list  ? même probleme pour reset et outepevent (mais bon, j'ai prouvé la terminaison de la fonction pour le moment)
*/

mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id, uint32_t size, uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;
    log_printf("[LIBCTRL] handle inevent\n");

    /* get back associated context */
    if ((errcode = usbctrl_get_context(dev_id, &ctx)) != MBED_ERROR_NONE) {
        /*@ assert !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id) ; */
        /*@ assert !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx == &ctx_list[i] && GHOST_idx_ctx == i ) ; */
        /*@ assert errcode == MBED_ERROR_NOTFOUND ; */
        goto err;
    }

    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id) ; */
    /*@ assert (\exists integer i ; 0 <= i < GHOST_num_ctx && ctx == &ctx_list[i] && GHOST_idx_ctx == i ) ; */
    /*@ assert  ctx == &ctx_list[GHOST_idx_ctx] ; */

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

                        #ifndef __FRAMAC__
                        if (handler_sanity_check_with_panic((physaddr_t)ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler)) {
                            goto err;
                        }
                        #endif

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


/*@

    @ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx,&usbotghs_ctx,((uint32_t *)(USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) );
    @ ensures GHOST_num_ctx == \old(GHOST_num_ctx) ;

    @ behavior ctx_not_found:
    @   assumes \forall integer i ; 0 <= i < GHOST_num_ctx ==> ctx_list[i].dev_id != dev_id ;
    @   assigns GHOST_idx_ctx;
    @   ensures \result == MBED_ERROR_NOTFOUND ;

    @ behavior bad_ep:
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assumes !(ep < USBOTGHS_MAX_OUT_EP) ;
    @   assigns GHOST_idx_ctx;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior state_USB_BACKEND_DRV_EP_STATE_SETUP_size_8 :
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assumes (ep < USBOTGHS_MAX_OUT_EP) ;
    @   assumes (usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_SETUP) ;
    @   assumes size == 8 ;
    @   ensures is_valid_error(\result);

    @ behavior state_USB_BACKEND_DRV_EP_STATE_SETUP_size_other :
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assumes (ep < USBOTGHS_MAX_OUT_EP) ;
    @   assumes (usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_SETUP) ;
    @   assumes size != 8 ;
	@   assigns GHOST_idx_ctx;
    @   assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)) ;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior state_USB_BACKEND_DRV_EP_STATE_DATA_OUT_size_0:
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assumes (ep < USBOTGHS_MAX_OUT_EP) ;
    @   assumes (usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_DATA_OUT) ;
    @   assumes size == 0 ;
    @   assigns GHOST_idx_ctx;
    @   ensures \result == MBED_ERROR_NONE ;

    @ behavior state_USB_BACKEND_DRV_EP_STATE_DATA_OUT_size_not_0:
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assumes (ep < USBOTGHS_MAX_OUT_EP) ;
    @   assumes (usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_DATA_OUT) ;
    @   assumes size != 0 ;
	@   assigns GHOST_idx_ctx;
    @   assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx ;
    @   ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_INVSTATE || \result == MBED_ERROR_INVPARAM ;

    @ behavior defaults_state:
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == dev_id ;
    @   assumes (ep < USBOTGHS_MAX_OUT_EP) ;
    @   assumes !(usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_SETUP) ;
    @   assumes !(usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_DATA_OUT) ;
    @   assigns GHOST_idx_ctx;
    @   ensures \result == MBED_ERROR_NONE ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
    TODO :  assigns pour behavior state_USB_BACKEND_DRV_EP_STATE_SETUP_size_8 : en attente des assigns de usbctrl_handle_requests

            state_USB_BACKEND_DRV_EP_STATE_DATA_OUT_size_not_0 : possiblité de plus préciser ce behavior, mais ça dépend de ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num == ep
            && ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir == USB_EP_DIR_OUT   ==> problème, ctx c'est ctx_list[i], et c'est compliqué de dire ça...

*/


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

    switch (usb_backend_drv_get_ep_state(ep, USB_BACKEND_DRV_EP_DIR_OUT)) {
        case USB_BACKEND_DRV_EP_STATE_SETUP:
            /*@ assert (ep < USBOTGHS_MAX_OUT_EP && usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_SETUP) ; */
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
                return errcode;
            } else {

                log_printf("[LIBCTRL] recv setup pkt size != 8: %d\n", size);
                /*@ assert \separated(r_CORTEX_M_USBOTG_HS_DIEPCTL(ep),r_CORTEX_M_USBOTG_HS_DOEPCTL(ep), &usbotghs_ctx,ctx) ; */
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
                @ loop invariant size != 0 ;
                @ loop invariant usbotghs_ctx.out_eps[ep].state == USB_BACKEND_DRV_EP_STATE_DATA_OUT ;
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

                            /*@ assert ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler ∈ {&handler_ep}; */
                            /*@ calls handler_ep; */
                            ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler(dev_id, size, ep);

                            /* now that data are transfered (oepint finished) whe can set back our FIFO for
                             * EP0, in order to support next EP0 events */
                            errcode = usb_backend_drv_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
                            /*@ assert errcode == MBED_ERROR_NONE || errcode == MBED_ERROR_INVPARAM ; */
                        }
                        /*@ assert errcode == MBED_ERROR_NONE || errcode == MBED_ERROR_INVPARAM ; */
                        goto err;
                    }
                }
            }
            /* if we arrive here, this means that no active EP has been found above, corresponding to
             * the EP on which we have received some content. This is *not* a valid behavior, and we
             * should inform the host of this */
            errcode = MBED_ERROR_INVSTATE;
            /*@ assert \separated(&usbotghs_ctx,ctx) ; */
            usb_backend_drv_nak(ep, USB_BACKEND_DRV_EP_DIR_OUT);
            /* goto err is, currently, useless as there is no effective code executed between this line
             * and the err: label. Though, in order to be future-proof in case of code inclusion, we
             * prefer to add the goto statement. */
            goto err;
            break;
        }
        default:
            log_printf("[LIBCTRL] oepint: EP not in good state: %d !\n",usb_backend_drv_get_ep_state(ep, USB_BACKEND_DRV_EP_DIR_OUT));
            /*@ assert errcode == MBED_ERROR_NONE ; */
            break;
    }
err:
    return errcode;
}

/*@
    @ assigns \nothing ;
    @ ensures \result == MBED_ERROR_NONE ;

*/

mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}
