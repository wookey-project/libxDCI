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
#ifndef USBCTRL_STD_REQUESTS_H_
#define USBCTRL_STD_REQUESTS_H_

#include "libc/types.h"
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
 * layers (i.e. interface class handlers) are executed.
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

/*@ predicate is_valid_request_code(usbctrl_request_code_t i) =
        i == USB_REQ_GET_STATUS ||
        i == USB_REQ_CLEAR_FEATURE ||
        i == USB_REQ_FUTURE1 ||
        i == USB_REQ_SET_FEATURE ||
        i == USB_REQ_FUTURE2 ||
        i == USB_REQ_SET_ADDRESS ||
        i == USB_REQ_GET_DESCRIPTOR ||
        i == USB_REQ_SET_DESCRIPTOR ||
        i == USB_REQ_GET_CONFIGURATION ||
        i == USB_REQ_SET_CONFIGURATION ||
        i == USB_REQ_GET_INTERFACE ||
        i == USB_REQ_SET_INTERFACE ||
        i == USB_REQ_SYNCH_FRAME ;
*/

typedef enum {
    USB_DESC_DEVICE          = 0x1,
    USB_DESC_CONFIGURATION   = 0x2,
    USB_DESC_STRING          = 0x3,
    USB_DESC_INTERFACE       = 0x4,
    USB_DESC_ENDPOINT        = 0x5,
    USB_DESC_DEV_QUALIFIER   = 0x6,
    USB_DESC_OTHER_SPEED_CFG = 0x7,
    USB_DESC_IFACE_POWER     = 0x8,
    USB_DESC_IAD             = 0x0B
} usbctrl_descriptor_type_t;

/*@ predicate is_valid_descriptor_type(usbctrl_descriptor_type_t i) =
        i == USB_DESC_DEVICE ||
        i == USB_DESC_CONFIGURATION ||
        i == USB_DESC_STRING ||
        i == USB_DESC_INTERFACE ||
        i == USB_DESC_ENDPOINT ||
        i == USB_DESC_DEV_QUALIFIER ||
        i == USB_DESC_OTHER_SPEED_CFG ||
        i == USB_DESC_IFACE_POWER ||
        i == USB_DESC_IAD;
*/

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
 * Max descriptor len in bytes. Descriptor may include successive descriptors,
 * for e.g. in case of configuration descriptor requests, to which we respond
 * by returning the current device descriptor, configuration descriptor, and,
 * for each interface active, the interface descriptor and associated
 * endpoint descriptors.
 * Other descriptor, for e.g. for String descriptors, may also be large, for
 * example for internationalization, for which the size is 255.
 */
#define MAX_DESCRIPTOR_LEN 256


/*
 * Handle USB requests (standard setup packets)
 * This API is to be used by te driver as a callback to oepint().
 * This means that the driver needs to fullfill these two arguments:
 * pkt: the setup packet
 * id:  the overall system USB device identifier
 *
 * TODO: A way to handle the overall device identifier may be to add a unique
 * identifier into the JSON file, which generate each device header file.
 *
 * This identifier is then guaranteed to be unique and can be used to discriminate
 * each device when handling multiple USB devices in the same application.
 * If we do that, the usb_device_identifier_t, would be replaced by a 'device_identifier_t'
 *
 */
mbed_error_t usbctrl_handle_requests(usbctrl_setup_pkt_t *pkt,
                                     uint32_t             id);



#if defined(__FRAMAC__)
mbed_error_t usbctrl_handle_class_requests(usbctrl_setup_pkt_t *pkt,
                                                         usbctrl_context_t   *ctx);


#endif/*__FRAMAC__*/

mbed_error_t usbctrl_unset_active_endpoints(usbctrl_context_t *ctx);

#endif/*USBCTRL_STD_REQUESTS_H_*/
