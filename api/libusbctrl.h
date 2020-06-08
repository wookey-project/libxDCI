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
#ifndef LIBUSBCTRL_H_
#define LIBUSBCTRL_H_

#include "libc/types.h"
#include "libc/syscall.h"
#include "autoconf.h"

/*********************************************************************************
 * About backends
 *
 * The libusbctrl can handle various backends. A backend is a USB driver API.
 * In order to keep the overall libusbctrl (and upper stacks) implementation
 * portable on various hardwares, the libusbctrl provides an abstraction layer
 * which handle renaming and potential overload of driver-level API.
 * This abstraction layer is loaded here, using the system-wide configuration
 * as selector.
 */


/*
 * By now, the libusbctrl only supports the USB OTG HS for STM32F4 plateforms.
 * Feel free to add some more drivers !
 * CAUTION: please, try to write drivers that are as much as possible API
 * compatible with the USB OTG HS driver (its upper API is not HW specific).
 * This will reduce the overload of the abstraction layer.
 */
#if defined(CONFIG_STM32F439)
# include "socs/stm32f439/usbctrl_backend.h"
#else
# error "architecture not yet supported!"
#endif



/*********************************************************************************
 * About handlers
 *
 * The Control plane must declare some handlers for various events (see usbotghs_handlers.c
 * for more informations). These handlers are called on these events in order to execute
 * control level (or potentially upper level(s)) programs. They can use the USB OTG HS
 * driver API during their execution.
 *
 * Control level handlers are linked directly through their prototype definition here.
 *
 * We prefer to use prototype and link time symbol resolution instead of callbacks as:
 *   1. The USB control plane is not an hotpluggable element
 *   2. callbacks have security impacts, as they can be corrupted, generating arbitrary
 *      code execution
 *
 *  WARNING: as we use prototypes (and not callbacks), these functions *must* exists at
 *  link time, for symbol resolution.
 *  It has been decided that the driver doesn't hold weak symbols for these functions,
 *  as their absence would make the USB stack unfonctional.
 *  If one of these function is not set in the control plane (or in any element of the
 *  application to be linked) it would generate a link time error, corresponding to a
 *  missing symbol.
 *
 */

/* called by libusbctrl when the SetConfiguration request has been received and handled.
 * From now on, the upper layer EPs are set and ready to use */
void usbctrl_configuration_set(void);

/*
  definition de la fonction usbctrl_reset_requested 
  definie dans un fichier main.c qui n'appartient pas à libxDCI
*/

#if defined(__FRAMAC__)
    bool reset_requested = false;
    
/*@
    @ assigns reset_requested ;
    @ ensures reset_requested == true ;
*/

void usbctrl_reset_received(void){
    reset_requested = true; 
}
      
#else
    void usbctrl_reset_received(void);
#endif/*!__FRAMAC__*/ 


/************************************************
 * About standard USB classes
 *
 * These classes are used by USB personnalities
 * that need to register against the libusbCTRL.
 * These classes are standard USB ones
 *
 * Declaring the class together with the interface
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
    USB_CLASS_HUB         = 0x09, /*< Hub devices */
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
    USB_EP_DIR_OUT, /* EP OUT, receiving in device mode */
    USB_EP_DIR_IN   /* EP IN, sending in device mode */
} usb_ep_dir_t;

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
 * handler for EPx (other than control) content reception or transmission
 * This handler is called on oepint and iepint events by the libcontrol oepint and
 * iepint handlers for the corresponding EP.
 */
typedef mbed_error_t (*usb_ioep_handler_t)(uint32_t dev_id, uint32_t size, uint8_t ep_id);

/*
 * USB Endpoint definition
 * Each Endpoint is defined by:
 * - its type, mode attribute and usage
 * - Its identifier, which depend on the first free EP identifier in the
 *   libcontrol USB device context (or 0 in case of EP requiring EP0 usage)
 */
typedef struct {
    usb_ep_type_t    type;                  /* EP type */
    usb_ep_dir_t     dir;                   /* EP direction */
    usb_ep_attr_t    attr;                  /* EP attributes */
    usb_ep_usage_t   usage;                 /* EP usage */
    uint16_t         pkt_maxsize;           /* pkt maxsize in this EP */
    usb_ioep_handler_t handler;             /* EP handler */
    uint8_t          ep_num;                /* EP identifier */
    uint8_t          poll_interval;         /* EP polling interval in ms (for interrupt IN EP */
    bool             configured;            /* EP enable in current config */
} usb_ep_infos_t;

/************************************************
 * about interfaces
 *
 * An interfaces is a USB device profile (e.g.
 * a SCSI mass storage device, a Raw HID device, etc.)
 * based on a standard USB type (RAW, BULK, etc...)
 * and composed of 1 or more EP(s). In some case,
 * this EP can be the EP0 (DFU interface)
 ***********************************************/

/*
 * A interface can have up to this number of endpoints.
 */
#define MAX_EP_PER_INTERFACE 8

/*
 * A interface may have to handle dedicated
 * requests from the host. These requests are received on the standard
 * configuration pipe of the device, and handled by the corresponding
 * device class handler after dispatching (in case of hybrid devices
 * (i.e. multiple interface declared).
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
 * A interface usually handle dedicated requests (setup packets) in the
 * standard control pipe. These requests will be dispatched and distributed by
 * the libusbctrl to the various personalities, through the usb_rqst_handler()
 * callback.
 * This callback treat the request and returns the response to the libusbctrl
 * control pipe handling, associated with an error state.
 */

typedef mbed_error_t     (*usb_rqst_handler_t)(uint32_t usbdci_handler,
                                              usbctrl_setup_pkt_t *inpkt);

/*
 * Handler prototype for Class level descriptor getter. An upper stack must
 * have such handler if it possess such descriptor. Otherwise, it can be set
 * to NULL in the interface structure.
 */
typedef mbed_error_t
      (*usb_class_get_descriptor_handler_t)(uint8_t             iface_id,
                                            uint8_t            *buf,
                                            uint32_t           *desc_size,
                                            uint32_t            usbdci_handler);


/*
 * This is the interface definition.
 *
 * The interface declare its class, subclass and protocol.
 * It also declare a request handler for potential dedicated (non-standard) requests
 * that need to be handled at interface level.
 *
 * Note that a interface doesn't define its class and endpoints  descriptor as
 * these descriptors are handled at libctrl level.
 * Although, functional descriptors are all specific, and have to be declared by the
 * upper layer. If they exists, they must be set in the interface structure (through
 * a uint8_t* pointer, associated to a size in byte). The libusbctrl will handle the
 * functional descriptor transmission to the host on the corresponding request.
 */
typedef struct {
   uint8_t            id;             /*< interface id, set by libxDCI */
   usb_class_t        usb_class;      /*< the standard USB Class */
   uint8_t            usb_subclass;   /*< interface subclass */
   uint8_t            usb_protocol;   /*< interface protocol */
   bool               dedicated;      /*< is the interface hosted in a dedicated configuration (not shared with others) ? */
   usb_rqst_handler_t rqst_handler;   /*< interface Requests handler */
   usb_class_get_descriptor_handler_t class_desc_handler; /* class level descriptor getter */
   uint8_t            usb_ep_number;  /*< the number of EP associated */
   usb_ep_infos_t     eps[MAX_EP_PER_INTERFACE];  /*< for each EP, the associated
                                                      informations */
} usbctrl_interface_t;

/************************************************
 * about libctrl API
 ***********************************************/

/*
 * Declare the USB device through the ctrl interface, get back, for the current context,
 * the associated device identifier in ctx. This part handling the device part only.
 */
mbed_error_t usbctrl_declare(uint32_t dev_id,
                             uint32_t *ctxh);

/*
 * create the first USB context, and create endpoint 0 for default
 * control pipe. Other EPs need to be registered by other libs (bulk, HID, and so on)
 * The USB state machine is also initialized
 *
 * Initialization *does not* touch the device. It only handle the local USB context.
 * The context is mapped to the device when requesting device start.
 * This permits to declare multiple classes/itnerfaces before starting the device and
 * receiving the first requests from the host.
 */
mbed_error_t usbctrl_initialize(uint32_t ctxh);

/*
 * Bind the device to the task, if not mapped
 * (ask the driver to map)
 */
mbed_error_t usbctrl_bind(uint32_t ctxh);

/*
 * Unmap the device, if mapped
 * (ask the driver to unmap)
 */
mbed_error_t usbctrl_unbind(uint32_t ctxh);

/*
 * definitivery release the device
 * (ask the driver to release)
 */
mbed_error_t usbctrl_release(uint32_t ctxh);

/*
 * declare a new USB interface. Endpoints are created, EP refs are set in
 * the interface context. interface is associated to the context.
 *
 * At interface declaration, all needed information to generate the associated
 * full descriptors is given. Each interface descriptor can be created by the
 * libusbctrl itself, as a consequence (see above).
 *
 * At interface declaration time, interface endpoints infos are updated
 * (EP identifiers, etc.) depending on the current global device interface state.
 *
 */
mbed_error_t usbctrl_declare_interface(__in     uint32_t ctxh,
                                       __out    usbctrl_interface_t  *up);

/*
 * Effective device start.
 * bind and enable the device, initialize the communication and wait for the
 * initial requests from the host.
 *
 * By now, it is not possible to declare new interfaces *after* the device
 * is started.
 */
mbed_error_t usbctrl_start_device(uint32_t ctxh);

/*
 * FIXME: Stop the device ? unmap and then ? Sending something to the host ? USB std
 * check is needed here. This feature may be interesting in some cases.
 */
mbed_error_t usbctrl_stop_device(uint32_t ctxh);

#endif/*!LIBUSB_CTRL_H_*/
