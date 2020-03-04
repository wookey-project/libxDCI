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
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
#include "usbctrl_state.h"
#include "generated/devlist.h"
#include "usbctrl.h"

/*
 * by now, the libusbctrl handle upto 2 USB Ctrl context,
 * which means that an application can handle up to 2 USB blocks
 * with 2 dedicated context that may completely differ.
 *
 */
#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX

static volatile uint8_t num_ctx = 0;
volatile usbctrl_context_t    ctx_list[MAX_USB_CTRL_CTX] = { 0 };


mbed_error_t usbctrl_declare(uint32_t dev_id,
                             uint32_t *ctxh)
{
    log_printf("[USBCTRL] declaring USB backend\n");
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitiation */
    if (ctxh == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (num_ctx == MAX_USB_CTRL_CTX) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    switch (dev_id) {
        case USB_OTG_HS_ID:
            errcode = usb_backend_drv_declare();
            break;
        case USB_OTG_FS_ID:
            errcode = usb_backend_drv_declare();
            break;
        default:
            errcode = MBED_ERROR_NOBACKEND;
            break;
    }
    ctx_list[num_ctx].dev_id = dev_id;
    *ctxh = num_ctx;
    volatile usbctrl_context_t *ctx = &(ctx_list[num_ctx]);
    num_ctx++;
    /* initialize context */
    ctx->num_cfg = 1;
    for (uint8_t i = 0; i < CONFIG_USBCTRL_MAX_CFG; ++i) {
        ctx->cfg[i].interface_num = 0;
        ctx->cfg[i].first_free_epid = 1;
    }
    ctx->address = 0;
    ctx->curr_cfg = 0;

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
    volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    log_printf("[USBCTRL] initializing automaton\n");
    memset((void*)ctx->cfg[ctx->curr_cfg].interfaces, 0x0, MAX_INTERFACES_PER_DEVICE * sizeof(usbctrl_interface_t));
    /* receive FIFO is not set in the driver. Wait for USB reset */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_NOSTORAGE;
    /* initialize with POWERED. We wait for the first reset event */

    usbctrl_set_state(ctx, USB_DEVICE_STATE_POWERED);
    /* Initialize EP0 with first FIFO. Should be reconfigued at Reset time */
    if ((errcode = usb_backend_drv_set_recv_fifo((uint8_t*)&(ctx->ctrl_fifo[0]), CONFIG_USBCTRL_EP0_FIFO_SIZE, 0)) != MBED_ERROR_NONE) {
        goto end;
    }
    /* control pipe recv FIFO is ready to be used */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_FREE;
    ctx->ctrl_req_processing = false;

    /* default config is 0. In it, first free EP id is 1 */
    ctx->cfg[0].first_free_epid = 1;


end:
    return errcode;
}

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
    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (ctx_list[i].dev_id == device_id) {
            *ctx = (usbctrl_context_t*)&(ctx_list[i]);
            goto end;
        }
    }
    errcode = MBED_ERROR_NOTFOUND;
end:
    return errcode;
}

bool usbctrl_is_endpoint_exists(usbctrl_context_t *ctx, uint8_t ep)
{
    if (ep == EP0) {
        return true;
    }
    for (uint8_t i = 0; i < ctx->cfg[ctx->curr_cfg].interface_num; ++i) {
        for (uint8_t j = 0; j < ctx->cfg[ctx->curr_cfg].interfaces[i].usb_ep_number; ++j) {
            if (ctx->cfg[ctx->curr_cfg].interfaces[i].eps[j].ep_num == ep) {
                return true;
            }
        }
    }
    return false;
}

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
mbed_error_t usbctrl_declare_interface(__in     uint32_t ctxh,
                                       __out    usbctrl_interface_t  *iface)
{
    uint8_t iface_config = 0;
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (iface == NULL) {
        errcode = MBED_ERROR_INVPARAM;
    }
    volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);
    /* check space */
    if (ctx->cfg[ctx->curr_cfg].interface_num == MAX_INTERFACES_PER_DEVICE) {
        errcode = MBED_ERROR_NOMEM;
    }
    if (iface->dedicated == true && ctx->cfg[ctx->curr_cfg].interface_num != 0) {
        ctx->num_cfg++;
        iface_config = ctx->num_cfg;
        ctx->cfg[iface_config].first_free_epid = 1;
    } else {
        iface_config = ctx->curr_cfg;
    }
    if (iface_config >= CONFIG_USBCTRL_MAX_CFG) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }
    /* iface identifier in target configuration */
    uint8_t iface_num = ctx->cfg[iface_config].interface_num;

    /* let's register */
   log_printf("declaring new interface class %x, %d EPs in Cfg %d/%d\n", iface->usb_class, iface->usb_ep_number, iface_config, iface_num);
   /* 1) make a copy of interface. The interface identifier is its cell number  */
   memcpy((void*)&(ctx->cfg[iface_config].interfaces[iface_num]), (void*)iface, sizeof(usbctrl_interface_t));
   /* 2) or, depending on the interface flags, add it to current config or to a new config */
   /* at declaration time, all interface EPs are disabled  and calculate EP identifier for the interface */
   for (uint8_t i = 0; i < ctx->cfg[iface_config].interfaces[iface_num].usb_ep_number; ++i) {
       volatile usb_ep_infos_t *ep = &(ctx->cfg[iface_config].interfaces[iface_num].eps[i]);
       ep->configured = false;
       if (ep->type == USB_EP_TYPE_CONTROL) {
           ep->ep_num = 0;
       } else {
           uint32_t drv_ep_mpsize;
           ep->ep_num = ctx->cfg[iface_config].first_free_epid++;
           /* FIXME: max EP num must be compared to the MAX supported EP num at driver level */
           /* check that declared ep mpsize is compatible with backend driver */
           drv_ep_mpsize = usb_backend_get_ep_mpsize();
           if (ep->pkt_maxsize > drv_ep_mpsize) {
               log_printf("truncating EP max packet size to backend driver EP max pktsize\n");
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
mbed_error_t usbctrl_start_device(uint32_t ctxh)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctxh >= num_ctx) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }
    volatile usbctrl_context_t *ctx = &(ctx_list[ctxh]);

    log_printf("[USBCTRL] configuring backend driver\n");
    if ((errcode = usb_backend_drv_configure(USB_BACKEND_DRV_MODE_DEVICE, usbctrl_handle_inepevent, usbctrl_handle_outepevent)) != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] failed while initializing backend: err=%d\n", errcode);
        usbctrl_set_state(ctx, USB_DEVICE_STATE_INVALID);
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
