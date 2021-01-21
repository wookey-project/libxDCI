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

#ifndef __FRAMAC__
/* this enumerate is declared in libusbctrl_framac.h to handle specs usage
 * of libusbctrl proof
 */

typedef enum {
    USB_DEVICE_STATE_ATTACHED              = 0, /* Attached but not powered. Should never be reached from device side */
    USB_DEVICE_STATE_POWERED               = 1, /* Attached and powered, first reset not received yet */
    USB_DEVICE_STATE_SUSPENDED_POWER       = 2, /* Suspended, from the Power state */
    USB_DEVICE_STATE_SUSPENDED_DEFAULT     = 3, /* Suspended, from the default state */
    USB_DEVICE_STATE_SUSPENDED_ADDRESS     = 4, /* Suspended, from the address state */
    USB_DEVICE_STATE_SUSPENDED_CONFIGURED  = 5, /* Suspended, from the configured state */
    USB_DEVICE_STATE_DEFAULT               = 6, /* First reset received, unique address not yet assigned */
    USB_DEVICE_STATE_ADDRESS               = 7, /* First reset received, address asigned, not yet configured */
    USB_DEVICE_STATE_CONFIGURED            = 8, /* First reset received, address asigned, configured, functions provided by the device can now be used */
    USB_DEVICE_STATE_INVALID               = 9  /* Not defined in the USB standard. exists as an INVALID case. Should not be reached */
} usb_device_state_t;

#endif/*!__FRAMAC__*/

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


/*@ predicate is_valid_transition(usb_device_trans_t i) =
        i == USB_DEVICE_TRANS_POWER_INTERRUPT ||
        i == USB_DEVICE_TRANS_RESET ||
        i == USB_DEVICE_TRANS_BUS_INACTIVE ||
        i == USB_DEVICE_TRANS_BUS_ACTIVE ||
        i == USB_DEVICE_TRANS_HUB_CONFIGURED ||
        i == USB_DEVICE_TRANS_HUB_DECONFIGURED ||
        i == USB_DEVICE_TRANS_HUB_RESET ||
        i == USB_DEVICE_TRANS_ADDRESS_ASSIGNED ||
        i == USB_DEVICE_TRANS_DEV_CONFIGURED ||
        i == USB_DEVICE_TRANS_DEV_DECONFIGURED ;
*/

#if defined(__FRAMAC__)

#define MAX_TRANSITION_STATE 10

typedef struct usb_operation_code_transition {
    uint8_t request;
    uint8_t target_state;
} usb_request_code_transition_t;


static const struct {
    usb_device_state_t state;
    usb_request_code_transition_t   req_trans[MAX_TRANSITION_STATE];
} usb_automaton[] = {
    {USB_DEVICE_STATE_ATTACHED, {
                 {USB_DEVICE_TRANS_HUB_CONFIGURED, USB_DEVICE_STATE_POWERED},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 }
     },
    {USB_DEVICE_STATE_POWERED, {
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_POWER},
                  {USB_DEVICE_TRANS_HUB_RESET, USB_DEVICE_STATE_ATTACHED},
                  {USB_DEVICE_TRANS_HUB_DECONFIGURED, USB_DEVICE_STATE_ATTACHED},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                 }
     },
    {USB_DEVICE_STATE_SUSPENDED_POWER, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_POWERED},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_SUSPENDED_DEFAULT, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_DEFAULT},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_SUSPENDED_ADDRESS, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_ADDRESS},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_SUSPENDED_CONFIGURED, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_CONFIGURED},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_DEFAULT, {
                  {USB_DEVICE_TRANS_ADDRESS_ASSIGNED, USB_DEVICE_STATE_ADDRESS},
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_DEFAULT},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },
    {USB_DEVICE_STATE_ADDRESS, {
                  {USB_DEVICE_TRANS_DEV_CONFIGURED, USB_DEVICE_STATE_CONFIGURED},
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_ADDRESS},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },
    {USB_DEVICE_STATE_CONFIGURED, {
                  {USB_DEVICE_TRANS_DEV_DECONFIGURED, USB_DEVICE_STATE_ADDRESS},
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_CONFIGURED},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },
    {USB_DEVICE_STATE_INVALID, {
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },

};

#endif/*__FRAMAC__*/


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
                           usb_device_trans_t request);

bool usbctrl_is_valid_transition(usb_device_state_t current_state,
                                 usb_device_trans_t transition,
                                 usbctrl_context_t *ctx);



#endif/*!USBCTRL_STATE_H_*/
