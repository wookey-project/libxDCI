/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
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
#include "usbctrl_reset.h"
#include "usbctrl_state.h"
#include "usbctrl.h"

/**
 * A reset event is received
 *
 * A reset has multiple impact, including a state automaton switch.
 */
mbed_error_t usbctrl_handle_reset(uint32_t             dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbctrl_context_t *ctx = NULL;
    usb_device_state_t nextstate = USB_DEVICE_STATE_INVALID;

    /* Detect which context is assocated to current request and set local ctx */
    if (usbctrl_get_context(dev_id, &ctx) != MBED_ERROR_NONE) {
        /* trapped on oepint() from a device which is not handled here ! what ? */
        errcode = MBED_ERROR_UNKNOWN;
        goto err;
    }
    /* handle USB state automaton: get next state */
    nextstate = usbctrl_next_state(ctx->state, USB_DEVICE_TRANS_RESET);
    /* handling reset itself.... */
    /* switch to next state */
    usbctrl_set_state(ctx, nextstate);


err:
    return errcode;
}
