#include "api/libusbctrl.h"

/*
 * by now, the libusbctrl handle upto 2 USB Ctrl context,
 * which means that an application can handle up to 2 USB blocks
 * with 2 dedicated context that may completely differ.
 *
 */
#define MAX_USB_CTRL_CTX 2

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
end:
    return errcode;
}
