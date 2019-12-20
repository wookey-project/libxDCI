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
#include "usbctrl_event.h"
#include "usbctrl_state.h"
#include "usbctrl.h"

/*
 * Here are implemented the various triggers of the USB drivers on specific
 * interrupt-based events that neeed control plane action.
 */



mbed_error_t usbctrl_handle_earlysuspend(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

mbed_error_t usbctrl_handle_outepevent(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}

mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    dev_id = dev_id;
    return errcode;
}



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
    /* check if reset is allowed during current state */
    if (! usbctrl_is_valid_transition(usbctrl_get_state(ctx), USB_DEVICE_TRANS_RESET, ctx)) {
        /* A reset should not be received here !!! */
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /* handle USB state automaton: get next state */
    nextstate = usbctrl_next_state(usbctrl_get_state(ctx), USB_DEVICE_TRANS_RESET);
    /* handling reset itself.... */
    switch (usbctrl_get_state(ctx)) {
        case USB_DEVICE_STATE_POWERED:
            /* This is the first reset received. INFO: RBE, you'll be happy to
             * handle Reset handling more easily by now :-) */
            /* here, there is nothing special to do other than going into default
             * state
             */
            goto schedule_state;
            break;
        case USB_DEVICE_STATE_DEFAULT:
            /* TODO */
            break;
        case USB_DEVICE_STATE_ADDRESS:
            /* TODO */
            break;
        case USB_DEVICE_STATE_CONFIGURED:
            /* TODO */
            break;
        case USB_DEVICE_STATE_SUSPENDED_DEFAULT:
            /* TODO */
            break;
        case USB_DEVICE_STATE_SUSPENDED_ADDRESS:
            /* TODO */
            break;
        case USB_DEVICE_STATE_SUSPENDED_CONFIGURED:
            /* TODO */
            break;
        default:
            errcode = MBED_ERROR_INVSTATE;
            /* fallbacking */

    }
schedule_state:
    /* switch to next state */
    usbctrl_set_state(ctx, nextstate);


err:
    return errcode;
}
