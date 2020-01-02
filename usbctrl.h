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
#ifndef USBCTRL_H_
#define USBCTRL_H_

#include "libc/types.h"
#include "libc/stdio.h"
#include "api/libusbctrl.h"

/*********************************************************
 * General tooling
 */

#if CONFIG_USR_LIB_USBCTRL_DEBUG
# define log_printf(...) printf(__VA_ARGS__)
#else
# define log_printf(...)
#endif


/*********************************************************
 * Core API
 */
mbed_error_t usbctrl_get_context(uint32_t device_id,
                                 usbctrl_context_t **ctx);

bool usbctrl_is_endpoint_exists(usbctrl_context_t *ctx, uint8_t ep);

bool usbctrl_is_interface_exists(usbctrl_context_t *ctx, uint8_t iface);

usbctrl_interface_t* usbctrl_get_interface(usbctrl_context_t *ctx, uint8_t iface);

#endif/*!USBCTRL_H_*/
