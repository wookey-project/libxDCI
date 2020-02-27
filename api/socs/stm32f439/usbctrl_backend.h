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
#ifndef USBCTRL_BACKEND_H_
#define USBCTRL_BACKEND_H_

/*
 * This file is an abstraction of the backend USB driver API, which permits to
 * interact with various USB drivers on various boards, while they keep the same
 * upper layer API.
 * The libusbctrl consider that a USB driver should respect a generic USB driver
 * API which permits to handle:
 * - driver initialization
 * - driver configuration
 * - endpoint manipulation (configuration, activation, deactivation, deconfiguration)
 * - USB relacted action on endpoints (ACK, NAK, STALL actions)
 * - data reception and transmission on endpoint (sending and receiving data,
 *   depending on the endpoint direction)
 *
 * If there is variation between driver enumerates (MPSIZE, EP type, etc.), the enumerates
 * must be overloaded here, through an abstracted type.
 *
 * If the abstraction API only use preprocessing substitution (i.e. the fastest mechanism
 * as it does not generate runtime modification), the driver must be compatible with the
 * libusbctrl API usage (return type, arguments types).
 *
 * On the other side, the abstraction layer must define volatile functions that translate
 * the libusbctrl usage of the driver API into a driver-compliant usage.
 * This will add some supplementary instructions at runtime.
 */

#include "autoconf.h"
#include "libc/types.h"

/*
 * First, specify the effective driver header to load
 */
#include "libusbotghs.h"

/*
 * Abstraction layer for the STM32F4 USB OTG HS driver
 * Here, only preprocessing usage is enough.
 */

/*
 * About driver's API types.
 * Here we keep the enumerates 'as-is' (no modification of the enumeration in the
 * abstraction layer).
 */
#define usb_backend_drv_ep_dir_t usbotghs_ep_dir_t

/*
 * About driver's API prototypes
 */
#define usb_backend_drv_configure           usbotghs_configure
#define usb_backend_drv_declare             usbotghs_declare
#define usb_backend_drv_activate_endpoint   usbotghs_activate_endpoint
#define usb_backend_drv_configure_endpoint  usbotghs_configure_endpoint
#define usb_backend_drv_endpoint_clear_nak  usbotghs_endpoint_clear_nak
#define usb_backend_drv_endpoint_set_nak    usbotghs_endpoint_set_nak
#define usb_backend_drv_endpoint_stall      usbotghs_endpoint_stall
#define usb_backend_drv_get_ep_state        usbotghs_get_ep_state
#define usb_backend_drv_send_data           usbotghs_send_data
#define usb_backend_drv_send_zlp            usbotghs_send_zlp
#define usb_backend_drv_set_address         usbotghs_set_address
#define usb_backend_drv_set_recv_fifo       usbotghs_set_recv_fifo

#endif/*!USBCTRL_BACKEND_H_*/
