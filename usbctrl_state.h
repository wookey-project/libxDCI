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
#ifndef USBCTRL_STATE_H_
#define USBCTRL_STATE_H_

#include "api/libusbctrl.h"
#include "usbctrl.h"
#include "usbctrl_requests.h"

/*
 * USB device standard automaton. This automaton is described in USB 2.0 standard,
 * Figure 9.1
 */
typedef enum {
    USB_DEVICE_STATE_ATTACHED = 0,         /* Attached but not powered. Should never be reached from device side */
    USB_DEVICE_STATE_POWERED,              /* Attached and powered, first reset not received yet */
    USB_DEVICE_STATE_SUSPENDED_POWER,      /* Suspended, from the Power state */
    USB_DEVICE_STATE_SUSPENDED_DEFAULT,    /* Suspended, from the default state */
    USB_DEVICE_STATE_SUSPENDED_ADDRESS,    /* Suspended, from the address state */
    USB_DEVICE_STATE_SUSPENDED_CONFIGURED, /* Suspended, from the configured state */
    USB_DEVICE_STATE_DEFAULT,              /* First reset received, unique address not yet assigned */
    USB_DEVICE_STATE_ADDRESS,              /* First reset received, address asigned, not yet configured */
    USB_DEVICE_STATE_CONFIGURED,           /* First reset received, address asigned, configured, functions provided by the device can now be used */
    USB_DEVICE_STATE_INVALID               /* Not defined in the USB standard. exists as an INVALID case. Should not be reached */
} usb_device_state_t;

/*
 * device standard transitions (USB 2.0 standard, figure 9.1)
 */
typedef enum {
    USB_DEVICE_TRANS_POWER_INTERRUPT = 0,
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
mbed_error_t usbctrl_set_state(__out volatile usbctrl_context_t *ctx,
                               __in usb_device_state_t newstate);


uint8_t usbctrl_next_state(usb_device_state_t current_state,
                           usbctrl_request_code_t request);

bool usbctrl_is_valid_transition(usb_device_state_t current_state,
                                 usb_device_trans_t transition,
                                 usbctrl_context_t *ctx);

#endif/*!USBCTRL_STATE_H_*/
