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
#include "api/libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
#include "usbctrl_state.h"
#include "generated/devlist.h"
/* include usb driver API */
#include "libusbotghs.h"
#include "usbctrl.h"

/*
 * by now, the libusbctrl handle upto 2 USB Ctrl context,
 * which means that an application can handle up to 2 USB blocks
 * with 2 dedicated context that may completely differ.
 *
 */
#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX

static uint8_t num_ctx = 0;
usbctrl_context_t    *ctx_list[MAX_USB_CTRL_CTX] = { 0 };


mbed_error_t usbctrl_declare(usbctrl_context_t*ctx)
{
    log_printf("[USBCTRL] declaring USB backend\n");
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitiation */
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    switch (ctx->dev_id) {
        case USB_OTG_HS_ID:
            errcode = usbotghs_declare();
            break;
        case USB_OTG_FS_ID:
            errcode = MBED_ERROR_NOBACKEND;
            break;
        default:
            errcode = MBED_ERROR_NOBACKEND;
            break;
    }
err:
    return errcode;
}

/*
 * basics for now
 */
mbed_error_t usbctrl_initialize(usbctrl_context_t*ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USBCTRL] initializing automaton\n");
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }
    if (num_ctx == MAX_USB_CTRL_CTX) {
        errcode = MBED_ERROR_NOMEM;
        goto end;
    }
    ctx_list[num_ctx] = ctx;
    num_ctx++;
    /* initialize context */
    ctx->interface_num = 0;
    ctx->address = 0;
    memset(ctx->interfaces, 0x0, MAX_INTERFACES_PER_DEVICE * sizeof(usbctrl_interface_t));
    /* receive FIFO is not set in the driver. Wait for USB reset */
    ctx->ctrl_fifo_state = USB_CTRL_RCV_FIFO_SATE_NOSTORAGE;
    /* initialize with POWERED. We wait for the first reset event */

    log_printf("[USBCTRL] configuring backend driver\n");
    if ((errcode = usbotghs_configure(USBOTGHS_MODE_DEVICE)) != MBED_ERROR_NONE) {
        log_printf("[USBCTRL] failed while initializing backend: err=%d\n", errcode);
        goto end;
    }
    ctx->state = USB_DEVICE_STATE_POWERED;
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
    if (*ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto end;
    }
    /* search */
    for (uint8_t i = 0; i < num_ctx; ++i) {
        if (ctx_list[i] != 0) {
            if (ctx_list[i]->dev_id == device_id) {
                *ctx = ctx_list[i];
                goto end;
            }
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
    for (uint8_t i = 0; i < ctx->interface_num; ++i) {
        for (uint8_t j = 0; j < ctx->interfaces[i].usb_ep_number; ++j) {
            if (ctx->interfaces[i].eps[j].ep_num == ep) {
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

    if (iface < ctx->interface_num) {
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

    if (iface < ctx->interface_num) {
        return &(ctx->interfaces[iface]);
    }
    return NULL;
}

/*
 * Here we declare a new USB interface for the given context.
 */
mbed_error_t usbctrl_declare_interface(__in      usbctrl_context_t   *ctx,
                                       __out    usbctrl_interface_t  *iface)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (ctx == NULL || iface == NULL) {
        errcode = MBED_ERROR_INVPARAM;
    }
    /* check space */
   if (ctx->interface_num == MAX_INTERFACES_PER_DEVICE) {
        errcode = MBED_ERROR_NOMEM;
   }
   /* let's register */
   /* 1) make a copy of interface. The interface identifier is its cell number  */
   memcpy((void*)&(ctx->interfaces[ctx->interface_num]), (void*)iface, sizeof(usbctrl_interface_t));
   /* 2) register endpoints */

   /* 3) now that everything is Okay, consider iface registered */
   ctx->interface_num++;
   return errcode;
}
