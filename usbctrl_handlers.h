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
#ifndef USBCTRL_HANDLERS_H_
#define USBCTRL_HANDLERS_H_

#include "libc/types.h"

/*
 * This package hold the various USB handlers that are triggered by the USB
 * drivers on various external events
 *
 * Handlers are not requests. They are not associated to any data but can be seen like
 * signals from the USB low level stacks.
 * Some of them are received before any data is transmit in any EP (including control pipe).
 */
mbed_error_t usbctrl_handle_earlysuspend(uint32_t dev_id);

mbed_error_t usbctrl_handle_reset(uint32_t dev_id);

mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id);

mbed_error_t usbctrl_handle_inepevent(uint32_t dev_id, uint32_t size, uint8_t ep);

mbed_error_t usbctrl_handle_outepevent(uint32_t dev_id, uint32_t size, uint8_t ep);

mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id);

#endif/*!USBCTRL_HANDLERS_H_*/
