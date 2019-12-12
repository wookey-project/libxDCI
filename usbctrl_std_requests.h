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
#ifndef USBCTRL_STD_REQUESTS_H_
#define USBCTRL_STD_REQUESTS_H_

#include "api/types.h"
#include "api/libusbctrl.h"
/*
 * Here is handled the standard requests management of the control interface.
 * This API handle all the possible requests that can be sent by the host through
 * a setup packet, and the way the device respond to it
 *
 * Associated structures are also defined here.
 * Requests from the hosts are always responded from the device standard control pipe.
 * See USB 2.0 standard specification, table 9.2, chapter 9.3
 *
 * The request subsystem can be seen as an automaton handling requests and responses,
 * with error handling. Responses depends on the content of the various fields of the
 * requests.
 *
 * Here we wish to handle the overall requests subprotocol through a full automaton
 * mechanism associated with its own state machine. This also permit to associate a
 * global request state for the overall device.
 *
 * Requests can't be handled in any states, they are allowed only in some states, as
 * described in USB 2.0 specification chap. 9.4.
 *
 * As a consequence, handling requests must be done in association with the
 * usbctrl_state API in order to check if the request is valid in the current state.
 */
#include "api/libusbctrl.h"

/*
 * Standard request codes, table 9.4, USB standard revision 2.0
 *
 * This does NOT handle class-specific requests (BULK, SCSI, and so on).
 * These requests are handled in the associated EP (not standard control pipe)
 * or with specific codes that are not in the current enumerate.
 *
 * If, for the current control endpoint, an upper layer as registered a specific usage
 * (e.g. DFU) including dedicated REQUESTS and the current requests do not match,
 * the currently received request is passed to the upper layer, and the current handler
 * is waiting for the upper handler response (i.e. setup pkt to return).
 *
 *
 * [ upper layer(s)      ]
 *     ^           |
 *     |           >
 * [ libctrl rqst handler]  ---> std request ? handling localy
 *     ^           |             or return the setup pkg to upper layer(s) if not
 *     |           >
 * [ driver              ]
 *
 * The libctrl requests various upper layer once a success is received or all upper
 * layers (i.e. personality class handlers) are executed.
 *
 */
typedef enum {
    USB_REQ_GET_STATUS        = 0x0,
    USB_REQ_CLEAR_FEATURE     = 0x1,
    USB_REQ_FUTURE1           = 0x2,
    USB_REQ_SET_FEATURE       = 0x3,
    USB_REQ_FUTURE2           = 0x4,
    USB_REQ_SET_ADDRESS       = 0x5,
    USB_REQ_GET_DESCRIPTOR    = 0x6,
    USB_REQ_SET_DESCRIPTOR    = 0x7,
    USB_REQ_GET_CONFIGURATION = 0x8,
    USB_REQ_SET_CONFIGURATION = 0x9,
    USB_REQ_GET_INTERFACE     = 0xa,
    USB_REQ_SET_INTERFACE     = 0xb,
    USB_REQ_SYNCH_FRAME       = 0xc,
} usbctrl_request_code_t;

typedef enum {
    USB_DESC_DEVICE          = 0x1,
    USB_DESC_CONFIGURATION   = 0x2,
    USB_DESC_STRING          = 0x3,
    USB_DESC_INTERFACE       = 0x4,
    USB_DESC_ENDPOINT        = 0x5,
    USB_DESC_DEV_QUALIFIER   = 0x6,
    USB_DESC_OTHER_SPEED_CFG = 0x7,
    USB_DESC_IFACE_POWER     = 0x8
} usbctrl_descriptor_type_t;

/*
 * standard feature selector for setup packet.
 * In case of unsupported feature, the device should stall
 */
typedef enum {
   USB_FEATURE_ENDPOINT_HALT      = 0x0,
   USB_FEATURE_DEVICE_REMOTE_WKUP = 0x1,
   USB_FEATURE_TEST_MODE          = 0x2,
} usbctrl_feature_selector_t;

/*
 * Handle USB requests (standard setup packets)
 * TODO: this will probably need more args, or better decomposition, as it impact
 * the state automaton.
 */
mbed_error_t usbctrl_handle_requests(usbctrl_context_t *ctx);

#endif/*USBCTRL_STD_REQUESTS_H_*/
