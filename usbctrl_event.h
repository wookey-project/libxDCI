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
#ifndef USBCTRL_EVENT_H_
#define USBCTRL_EVENT_H_

/*
 * This file handle the overall reset events, and the associate state change, in
 * interaction with the state automaton.
 */

#include "libc/types.h"
#include "api/libusbctrl.h"

/*
 * INFO: functions declared in the usbctrl_event.c file are made to be resolved at link
 * time by the driver. They are not static, but they are not defined in a header, as
 * they are not called from any part of the libUSBCtrl, but only triggered from the
 * driver itself.
 */

#endif/*!USBCTRL_EVENT_H_*/
