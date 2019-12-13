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
#ifndef USBCTRL_STATE_H_
#define USBCTRL_STATE_H_

#include "api/libusbctrl.h"
#include "usbctrl_requests.h"

/*
 * USB device standard automaton. This automaton is described in USB 2.0 standard,
 * Figure 9.1
 */
typedef enum {
    USB_DEVICE_STATE_ATTACHED,
    USB_DEVICE_STATE_POWERED,
    USB_DEVICE_STATE_SUSPENDED_POWER, /* two suspend case: during early init (POWERED)
                                        and runtime. when reach through POWERED mode,
                                        no reset is possible. To make the automaton
                                        easy, one suspend state per previous state is
                                        made, to simplify the transition */
    USB_DEVICE_STATE_SUSPENDED_DEFAULT,
    USB_DEVICE_STATE_SUSPENDED_ADDRESS,
    USB_DEVICE_STATE_SUSPENDED_CONFIGURED,
    USB_DEVICE_STATE_DEFAULT,
    USB_DEVICE_STATE_ADDRESS,
    USB_DEVICE_STATE_CONFIGURED,
    USB_DEVICE_STATE_INVALID
} usb_device_state_t;

/*
 * device standard transitions (USB 2.0 standard, figure 9.1)
 */
typedef enum {
    USB_DEVICE_TRANS_POWER_INTERRUPT,
    USB_DEVICE_TRANS_RESET,
    USB_DEVICE_TRANS_BUS_INACTIVE,
    USB_DEVICE_TRANS_BUS_ACTIVE,
    USB_DEVICE_TRANS_HUB_CONFIGURED,
    USB_DEVICE_TRANS_HUB_DECONFIGURED,
    USB_DEVICE_TRANS_HUB_RESET,
    USB_DEVICE_TRANS_ADDRESS_ASSIGNED,
    USB_DEVICE_TRANS_DEV_CONFIGURED,
    USB_DEVICE_TRANS_DEV_DECONFIGURED,
} usb_device_trans_t;

/*
 * Return the current state of the USB device
 */
usb_device_state_t usbctrl_get_state(const usbctrl_context_t *ctx);

/*
 * set the current state of the USB device
 */
mbed_error_t usbctrl_set_state(__out usbctrl_context_t *ctx,
                               __in usb_device_state_t newstate);


uint8_t usbctrl_next_state(usb_device_state_t current_state,
                           usbctrl_request_code_t request);

bool usbctrl_is_valid_transition(usb_device_state_t current_state,
                                 usb_device_trans_t transition,
                                 usbctrl_context_t *ctx);

#endif/*!USBCTRL_STATE_H_*/
