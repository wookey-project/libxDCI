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
#ifndef LIBUSBCTRL_H_
#define LIBUSBCTRL_H_

#include "libc/types.h"
#include "libc/syscall.h"

/**********
 * USB driver(s) have to handle a standard eumerate defining an USB identifier
 * for the SoC USB device(s). When multiple USB devices are handled in the same
 * palteform, each one must handle a unique, dedicated identifier, which allows
 * the libusbctrl to discriminate each device and associate ctrl/data flow from
 * the lower layer. This is under the responsability of the driver to handle this
 * as whe driver will use callbacks from the libusbctrl to respond to USB device
 * interrupt.
 * The libusbctrl handle context and associate this very identifier to associated
 * device_t struct to differenciate each event source and associated context.
 *
 * The identifier as to be passed to the various handler by the bellowing driver.
 */
typedef enum {
    USB_DRIVER_STM32F4XX_FS = 0x0,
    USB_DRIVER_STM32F4XX_HS = 0x1,
} usb_device_identifier_t;

/* End of TODO */

/************************************************
 * About standard USB classes
 *
 * These classes are used by USB personnalities
 * that need to register against the libusbCTRL.
 * These classes are standard USB ones
 *
 * Declaring the class together with the pesonality
 * allows USB control to handle some class-specific
 * EP usage, for e.g. EP0 reconfiguration for
 * DATA mode (e.g. DFU or RAW HID).
 ***********************************************/

typedef enum {
    USB_CLASS_UNSPECIFIED = 0x00, /*< Unspecified, see device descriptors */
    USB_CLASS_AUDIO       = 0x01, /*< Speaker, microphone... */
    USB_CLASS_CDC_CTRL    = 0x02, /*< Modem, Eth, Wifi, RS232, with class 0x0a */
    USB_CLASS_HID         = 0x03, /*< Human interaction devices (keyboard, mouse) */
    USB_CLASS_RESERVED1   = 0x04, /*< reserved */
    USB_CLASS_PID         = 0x05, /*< Joysticks */
    USB_CLASS_PTP_MTP     = 0x06, /*< Webcam, scanner */
    USB_CLASS_PRINTER     = 0x07, /*< USB printers */
    USB_CLASS_MSC_UMS     = 0x08, /*< Mass storage */
    USB_CLASS_HUB         = 0x09, /*< Mass storage */
    USB_CLASS_CDC_DATA    = 0x0a, /*< Mass storage */
    USB_CLASS_CCID        = 0x0b, /*< Smartcards */
    USB_CLASS_RESERVED2   = 0x0c, /*< reserved */
    USB_CLASS_CSEC        = 0x0d, /*< Fingerprint readers */
    USB_CLASS_VIDEO       = 0x0e, /*< Fingerprint readers */
    USB_CLASS_PHDC        = 0x0f, /*< Personal Healthcare */
    USB_CLASS_AV          = 0x10, /*< Audio, Video */
    USB_CLASS_BILLBOARD   = 0x11, /*< USB-C alternate modes */
    USB_CLASS_DIAG        = 0xDC, /*< USB diagnostic device */
    USB_CLASS_WIRELESS    = 0xE0, /*< BT, RNDIS... */
    USB_CLASS_MISC        = 0xEF, /*< misc devices */
    USB_CLASS_DFU         = 0xFE, /*< DFU, IrDA */
    USB_CLASS_VSPECIFIC   = 0xFF, /*< Vendor specific */
} usb_class_t;

/************************************************
 * about endpoints
 * USB devices are based on half duplex communication
 * end-points. Only Endpoint 0, which is always up,
 * is full-duplex. This endpoint is handled by the
 * libctrl itself as the EP0 is used mostly for
 * control.
 * Although, this endpoint may be used for other
 * usage in some case, for e.g. for DFU mode.
 ***********************************************/


/*
 * USB Endpoint type
 */
typedef enum {
   USB_EP_TYPE_CONTROL      = 0x00,
   USB_EP_TYPE_ISOCHRONOUS  = 0x01,
   USB_EP_TYPE_BULK         = 0x02,
   USB_EP_TYPE_INTERRUPT    = 0x03,
} usb_ep_type_t;

/*
 * USB Endpoint access mode
 */
typedef enum {
    USB_EP_MODE_READ,
    USB_EP_MODE_WRITE,
    USB_EP_MODE_DATA /* e.g. DFU EP */
} usb_ep_mode_t;

/*
 * USB Endpoint attribute
 */
typedef enum {
    USB_EP_ATTR_NO_SYNC     = 0x0,
    USB_EP_ATTR_ASYNC       = 0x1,
    USB_EP_ATTR_ADAPTATIVE  = 0x2,
    USB_EP_ATTR_SYNC        = 0x3,
} usb_ep_attr_t;

/*
 * USB Endpoint usage
 */
typedef enum {
    USB_EP_USAGE_DATA               = 0x0,
    USB_EP_USAGE_FEEDBACK           = 0x1,
    USB_EP_USAGE_IMPLICIT_FEEDBACK  = 0x2,
} usb_ep_usage_t;


/*
 * USB Endpoint definition
 * Each Endpoint is defined by:
 * - its type, mode attribute and usage
 * - Its identifier, which depend on the first free EP identifier in the
 *   libcontrol USB device context (or 0 in case of EP requiring EP0 usage)
 */
typedef struct {
    usb_ep_type_t    type;                  /* EP type */
    usb_ep_mode_t    mode;                  /* EP mode */
    usb_ep_attr_t    attr;                  /* EP attributes */
    usb_ep_usage_t   usage;                 /* EP usage */
    uint16_t         pkt_maxsize;           /* pkt maxsize in this EP */
    uint8_t          ep_num;                /* EP identifier */
} usb_ep_infos_t;

/************************************************
 * about personnalities
 *
 * A personality is a USB device profile (e.g.
 * a SCSI mass storage device, a Raw HID device, etc.)
 * based on a standard USB type (RAW, BULK, etc...)
 * and composed of 1 or more EP(s). In some case,
 * this EP can be the EP0 (DFU personality)
 ***********************************************/

/*
 * A personality can have up to this number of endpoints.
 */
#define MAX_EP_PER_PERSONALITY 8

/*
 * A personality may have to handle dedicated
 * requests from the host. These requests are received on the standard
 * configuration pipe of the device, and handled by the corresponding
 * device class handler after dispatching (in case of hybrid devices
 * (i.e. multiple personality declared).
 *
 */
typedef struct __packed {
    uint8_t bmRequestType;
    uint8_t bRequest;
    uint16_t wValue;
    uint16_t wIndex;
    uint16_t wLength;
} usbctrl_setup_pkt_t;

/*
 * A personality usually handle dedicated requests (setup packets) in the
 * standard control pipe. These requests will be dispatched and distributed by
 * the libusbctrl to the various personalities, through the usb_rqst_handler()
 * callback.
 * This callback treat the request and returns the response to the libusbctrl
 * control pipe handling, associated with an error state.
 */
typedef mbed_error_t     (*usb_rqst_handler_t)(usbctrl_setup_pkt_t *inpkt,
                                              usbctrl_setup_pkt_t **outpkt);

typedef uint8_t * functional_descriptor_p;

/*
 * This is the personality definition.
 *
 * The personality declare its class, subclass and protocol.
 * It also declare a request handler for potential dedicated (non-standard) requests
 * that need to be handled at personality level.
 *
 * Note that a personality doesn't define its class and endpoints  descriptor as
 * these descriptors are handled at libctrl level.
 * Although, functional descriptors are all specific, and have to be declared by the
 * upper layer. If they exists, they must be set in the personality structure (through
 * a uint8_t* pointer, associated to a size in byte). The libusbctrl will handle the
 * functional descriptor transmission to the host on the corresponding request.
 */
typedef struct {
   usb_class_t        usb_class;      /*< the standard USB Class */
   uint8_t            usb_subclass;   /*< personality subclass */
   uint8_t            usb_protocol;   /*< personality protocol */
   usb_rqst_handler_t rqst_handler;   /*< personality Requests handler */
   functional_descriptor_p func_desc; /*< pointer to functional descriptor, if it exists */
   uint8_t            func_desc_len;  /*< functional descriptor length (in byte)  */
   uint8_t            usb_ep_number;  /*< the number of EP associated */
   usb_ep_infos_t     eps[MAX_EP_PER_PERSONALITY];  /*< for each EP, the associated
                                                      informations */
} usbctrl_personality_t;

/************************************************
 * about libctrl context
 ***********************************************/

typedef struct {
    usb_device_identifier_t id;
    uint8_t                 state;
    device_t               usb_dev;
    uint8_t                personality_number;
    usbctrl_personality_t *personalities[];
} usbctrl_context_t;


/************************************************
 * about libctrl API
 ***********************************************/

/*
 * Declare the USB device through the ctrl interface
 */
mbed_error_t usbctrl_declare(usbctrl_context_t*ctx);

/*
 * create the first USB context, and create the endpoint 0 for
 * control. Other EP need to be registered by other libs (bulk, HID, and so on)
 * The USB state machine is also initialized
 *
 * Initialization *does not* touch the device. It only handle the local USB context.
 * The context is mapped to the device when requesting device start.
 * This permits to declare multiple classes/personalities before starting the device and
 * receiving the first requests from the host.
 */
mbed_error_t usbctrl_initialize(usbctrl_context_t*ctx);

/*
 * Bind the device to the task, if not mapped
 * (ask the driver to map)
 */
mbed_error_t usbctrl_bind(usbctrl_context_t*ctx);

/*
 * Unmap the device, if mapped
 * (ask the driver to unmap)
 */
mbed_error_t usbctrl_unbind(usbctrl_context_t*ctx);

/*
 * definitivery release the device
 * (ask the driver to release)
 */
mbed_error_t usbctrl_release(usbctrl_context_t*ctx);

/*
 * declare a new USB personality. Endpoints are created, EP refs are set in
 * the personality context. personality is associated to the context.
 * (ask the driver to release)
 *
 * At personality declaration, all needed information to generate the associated
 * full descriptor is given. Each personality descriptor can be created by the
 * libusbctrl itself, as a consequence.
 */
mbed_error_t usbctrl_declare_personality(__in      usbctrl_context_t      *ctx,
                                          __out    usbctrl_personality_t *up);

/*
 * Effective device start. FIXME: define the effective behavior:
 * - bind and enable the device, send the setup packet and descriptors
 *
 * Although, it is possible to declare new personality after a start, as hotplugged
 * personality in the USB standard. Do we wish to support that feature ?
 */
mbed_error_t usbctrl_start_device(usbctrl_context_t      *ctx);

/*
 * FIXME: Stop the device ? unmap and then ? Sending something to the host ? USB std
 * check is needed here
 */
mbed_error_t usbctrl_stop_device(usbctrl_context_t       *ctx);

#endif/*!LIBUSB_CTRL_H_*/
