#include "api/libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "usbctrl_state.h"

/* include usb driver API */
#include "usb.h"

/*
 * by now, the libusbctrl handle upto 2 USB Ctrl context,
 * which means that an application can handle up to 2 USB blocks
 * with 2 dedicated context that may completely differ.
 *
 */
#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX

static uint8_t num_ctx = 0;
usbctrl_context_t    *ctx_list[MAX_USB_CTRL_CTX] = { 0 };

/*
 * basics for now
 */
mbed_error_t usbctrl_initialize(usbctrl_context_t*ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
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
    /* initialize with POWERED. We wait for the first reset event */
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
        for (uint8_t j = 0; j < ctx->personalities[i]->usb_ep_number; ++j) {
            if (ctx->personalities[i]->eps[j].ep_num == ep) {
                return true;
            }
        }
    }
    return false;
}
