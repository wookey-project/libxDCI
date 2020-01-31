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
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */

#include "libusbotghs.h"
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

mbed_error_t usbctrl_handle_reset(uint32_t dev_id)
{
    mbed_error_t       errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    usbctrl_context_t *ctx = NULL;
    log_printf("[USBCTRL] Handling reset\n");
    /* TODO: support for multiple drivers in the same time.
    T his requires a driver table with callbacks or a preprocessing mechanism
    to select the corresponding driver API. While the libctrl is not yet fully
    operational, we handle only usbotghs driver API */
    dev_id = dev_id;

    log_printf("[USBCTRL] reset: get context for dev_id %d\n", dev_id);
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] reset: no ctx found!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    usb_device_state_t state = usbctrl_get_state(ctx);
    /* resetting directly depends on the current state */
    if (!usbctrl_is_valid_transition(state, USB_DEVICE_TRANS_RESET, ctx)) {
        log_printf("[USBCTRL] RESET transition is invalid in current state !\n");
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
            errcode = usbotghs_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            break;
        case USB_DEVICE_STATE_SUSPENDED_DEFAULT:
            /* awake from suspended state, back to default */
            errcode = usbotghs_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;

            break;
        case USB_DEVICE_STATE_SUSPENDED_ADDRESS:
            /* awake from suspended state, back to address */
            errcode = usbotghs_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;

            break;
        case USB_DEVICE_STATE_SUSPENDED_CONFIGURED:
            /* awake from suspended state, back to configured */
            errcode = usbotghs_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            break;
        case USB_DEVICE_STATE_DEFAULT:
            /* going back to default... meaning doing nothing */
            errcode = usbotghs_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            break;
        case USB_DEVICE_STATE_ADDRESS:
            /* going back to default */
            errcode = usbotghs_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            ctx->address = 0;
            usbotghs_set_address(0);
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* INFO: deconfigure any potential active EP of current config is automatically
             * done by USB OTG HS core at reset */

            /* going back to default */
            errcode = usbotghs_set_recv_fifo(&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0);
            if (errcode != MBED_ERROR_NONE) {
                goto err;
            }
            /* control pipe recv FIFO is ready to be used */
            ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
            ctx->address = 0;
            usbotghs_set_address(0);
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
    usbctrl_set_state(ctx, usbctrl_next_state(state,
                          USB_DEVICE_TRANS_RESET));
err:
    return errcode;
}

mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

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
    // usbotghs_send_zlp(ep);

    log_printf("[LIBCTRL] handle inpevent\n");
    for (uint8_t i = 0; i < ctx->interfaces[ctx->curr_cfg].usb_ep_number; ++i) {
        if (ctx->interfaces[ctx->curr_cfg].eps[i].ep_num == ep) {
            if (ctx->interfaces[ctx->curr_cfg].eps[i].handler) {
                log_printf("[LIBCTRL] iepint: executing upper class handler for EP %d\n", ep);
                ctx->interfaces[ctx->curr_cfg].eps[i].handler(size);
            }
            break;
        }
    }
    dev_id = dev_id;
err:
    return errcode;
}


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

    log_printf("[LIBCTRL] oepint: current ep state is %d\n", usbotghs_get_ep_state(ep, USBOTG_HS_EP_DIR_OUT));
    if (ep == EP0) {
        switch (usbotghs_get_ep_state(ep, USBOTG_HS_EP_DIR_OUT)) {
            case USBOTG_HS_EP_STATE_SETUP:
                log_printf("[LIBCTRL] oepint: a setup pkt transfert has been fully received. Handle it !\n");
                if (size == 8) {
                    /* first, we must convert received data into current endianess */
                    uint8_t *setup_packet = ctx->ctrl_fifo;
                    usbctrl_setup_pkt_t formated_pkt = {
                        setup_packet[0],
                        setup_packet[1],
                        setup_packet[3] << 8 | setup_packet[2],
                        setup_packet[5] << 8 | setup_packet[4],
                        setup_packet[7] << 8 | setup_packet[6]
                    };
                    return usbctrl_handle_requests(&formated_pkt, dev_id);
                } else {
                    log_printf("[LIBCTRL] recv setup pkt size != 8: %d\n", size);
                }
                break;
            default:
                log_printf("[LIBCTRL] oepint: EP not in good state: %d !\n",
                        usbotghs_get_ep_state(ep, USBOTG_HS_EP_DIR_OUT));
                break;
        }
    } else {
        log_printf("[LIBCTRL] handle outepevent\n");
        for (uint8_t iface = 0; iface < ctx->interface_num; ++iface) {
            if (ctx->interfaces[iface].cfg_id == ctx->curr_cfg) {
                for (uint8_t i = 0; i < ctx->interfaces[iface].usb_ep_number; ++i) {
                    if (ctx->interfaces[iface].eps[i].ep_num == ep) {
                        if (ctx->interfaces[iface].eps[i].handler) {
                            log_printf("[LIBCTRL] oepint: executing upper class handler for EP %d\n", ep);
                            ctx->interfaces[iface].eps[i].handler(size);
                        }
                        goto err;
                    }
                }
            }
        }
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

