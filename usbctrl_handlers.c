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


mbed_error_t usbctrl_handle_earlysuspend(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

/* @
    @ assigns \nothing ;  // en fait, je touche à un contexte global, déclaré dans un autre fichier...je ne sais pas comment le dire (ctx_list)

    @ ensures \forall integer i ; 0 <= i < MAX_USB_CTRL_CTX ==> ctx_list[i].dev_id != dev_id 
                                ==> \result == MBED_ERROR_INVPARAM ;
    @ 
    @ ensures \exists integer i ; 0 <= i < MAX_USB_CTRL_CTX && ctx_list[i].dev_id == dev_id && 
*/

// dans les ensures, je dois dire : si je suis dans tel état, je termine dans tel état à la fin de la fonction
// mais pour ça je dois faire référence à ctx->state, déclaré dans la fonction...donc je peux pas le mettre ici. 
//  Je dois utiliser ctx_list, qui n'est pas connu par la fonction usbctrl_handle_reset

mbed_error_t usbctrl_handle_reset(uint32_t dev_id)
{
    mbed_error_t       errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    usbctrl_context_t *ctx = NULL;
    //log_printf("[USBCTRL] Handling reset\n");
    /* TODO: support for multiple drivers in the same time.
    T his requires a driver table with callbacks or a preprocessing mechanism
    to select the corresponding driver API. While the libctrl is not yet fully
    operational, we handle only usbotghs driver API */
    dev_id = dev_id;

    //log_printf("[USBCTRL] reset: get context for dev_id %d\n", dev_id);
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {
        //log_printf("[USBCTRL] reset: no ctx found!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    usb_device_state_t state = usbctrl_get_state(ctx);
    /* resetting directly depends on the current state */
    if (!usbctrl_is_valid_transition(state, USB_DEVICE_TRANS_RESET, ctx)) {
        //log_printf("[USBCTRL] RESET transition is invalid in current state !\n");
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }

    //log_printf("[USBCTRL] reset: execute transition from state %d\n", state);
    /* handling RESET event depending on current state */
    switch (state) {
        case USB_DEVICE_STATE_POWERED:
            /* initial reset of the device, set EP0 FIFO. Other EPs FIFO
             * are handled at SetConfiguration & SetInterface time */
            /* as USB Reset action reinitialize the EP0 FIFOs (flush, purge and deconfigure) they must
             * be reconfigure for EP0 here. */
            //log_printf("[USBCTRL] reset: set reveive FIFO for EP0\n");

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
            #if defined(__FRAMAC__)
            #else
            usb_backend_drv_set_address(0); 
            #endif/*!__FRAMAC__*/
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
            
            #if defined(__FRAMAC__)
           
            #else
            usb_backend_drv_set_address(0); 
            #endif/*!__FRAMAC__*/
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

    /*@ assert ctx->state == USB_DEVICE_STATE_DEFAULT ; */   // c'est un cas particulier, l'état initial est powered, après le reset le device est en défaut
    /* @ assert ctx_list[0].state == USB_DEVICE_STATE_DEFAULT ; */

err:
    return errcode;
}

mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}


/*
 * IN EP event (data sent) for EP 0
 */
mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id, uint32_t size, uint8_t ep)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;
    log_printf("[LIBCTRL] handle inevent\n");
    /* get back associated context */
    if ((errcode = usbctrl_get_context(dev_id, &ctx)) != MBED_ERROR_NONE) {
        goto err;
    }

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
        for (uint8_t iface = 0; iface < ctx->cfg[curr_cfg].interface_num; ++iface) {
            for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interfaces[iface].usb_ep_number; ++i) {
                /* here we check both ep id and direction and EP0 is a specific full duplex case */
                if (   ctx->cfg[curr_cfg].interfaces[iface].eps[i].ep_num == ep
                    && ctx->cfg[curr_cfg].interfaces[iface].eps[i].dir == USB_EP_DIR_IN) {
                    log_printf("[LIBCTRL] found ep in iface %d, declared ep %d\n", iface, i);
                    if (ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler) {
                        log_printf("[LIBCTRL] iepint: executing upper class handler for EP %d\n", ep);
                        /* XXX: c'est ma FIFO ? oui, c'est pour moi. Non, c'est pour au dessus :-)*/
                        ctx->cfg[curr_cfg].interfaces[iface].eps[i].handler(dev_id, size, ep);
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
    #if defined(__FRAMAC__)
    uint8_t State = Frama_C_interval(0,9);
    switch(State){
    #else
    switch (usb_backend_drv_get_ep_state(ep, USB_BACKEND_DRV_EP_DIR_OUT)) {
    #endif/*!__FRAMAC__*/
        case USB_BACKEND_DRV_EP_STATE_SETUP:
            log_printf("[LIBCTRL] oepint: a setup pkt transfert has been fully received. Handle it !\n");
            if (size == 8) {
                /* first, we shoule not accept setup pkt from other EP than 0.
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
                //usb_backend_drv_ack(EP0, USB_EP_DIR_OUT);
                return errcode;
            } else {
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
            for (uint8_t iface = 0; iface < ctx->cfg[curr_cfg].interface_num; ++iface) {
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
            //usb_backend_drv_nak(ep, USB_BACKEND_DRV_EP_DIR_OUT);
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

