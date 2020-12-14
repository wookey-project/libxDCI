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
#ifndef USB_CTRL_DESCRIPTORS_H_
#define USB_CTRL_DESCRIPTORS_H_

#include "usbctrl.h"
#include "usbctrl_requests.h"

#define MAX_DESC_STRING_SIZE		32

#define LANGUAGE_ENGLISH        0x0409

/*
 * This is the central USB control descriptors configuration and description.
 *
 * USB descriptors types are declared here and generated by the libusbctrl based on
 * the various informations declared by the upper libraries (libbulk, libhid,
 * libscsi...) in order to declare the device interface to the host.
 *
 * EP identifiers are generated depending on the interface declaration order.
 */
/*
 * Global device descriptor. This descriptor is unique for the entire device,
 * even in case of hybrid (multi-interface) device.
 */
typedef struct __packed {
	uint8_t  bLength;
	uint8_t  bDescriptorType;
	uint16_t bcdUSB;
	uint8_t  bDeviceClass;
	uint8_t  bDeviceSubClass;
	uint8_t  bDeviceProtocol;
	uint8_t  bMaxPacketSize;
	uint16_t idVendor;
	uint16_t idProduct;
	uint16_t bcdDevice;
	uint8_t  iManufacturer;
	uint8_t  iProduct;
	uint8_t  iSerialNumber;
	uint8_t  bNumConfigurations;
} usbctrl_device_descriptor_t;

typedef struct __packed {
	uint8_t bLength;
	uint8_t bDescriptorType;
	uint16_t wTotalLength;
	uint8_t bNumInterfaces;
	uint8_t bConfigurationValue;
	uint8_t iConfiguration;
	struct {
		uint8_t reserved:5;
		uint8_t remote_wakeup:1;
		uint8_t self_powered:1;
		uint8_t reserved7:1;
	} bmAttributes;
	uint8_t bMaxPower;
} usbctrl_configuration_descriptor_t;

typedef struct __packed {
 uint8_t bLength;
 uint8_t bDescriptorType;
 uint8_t bFirstInterface;
 uint8_t bInterfaceCount;
 uint8_t bFunctionClass;
 uint8_t bFunctionSubClass;
 uint8_t bFunctionProtocol;
 uint8_t iFunction;
} usbctrl_iad_descriptor_t;


typedef struct __packed {
	uint8_t bLength;
	uint8_t bDescriptorType;
	uint8_t bInterfaceNumber;
	uint8_t bAlternateSetting;
	uint8_t bNumEndpoints;
	uint8_t bInterfaceClass;
	uint8_t bInterfaceSubClass;
	uint8_t bInterfaceProtocol;
	uint8_t iInterface;
} usbctrl_interface_descriptor_t;

typedef struct __packed {
	uint8_t  bLength;
	uint8_t  bDescriptorType;
	uint8_t  bEndpointAddress;
    uint8_t  bmAttributes; /* bitmap */
	uint16_t wMaxPacketSize;
	uint8_t  bInterval;
} usbctrl_endpoint_descriptor_t;

typedef struct __packed {
	uint8_t bLength;
	uint8_t bDescriptorType;
	uint16_t wString[MAX_DESC_STRING_SIZE];
} usbctrl_string_descriptor_t;



typedef struct __packed {
	usbctrl_endpoint_descriptor_t ep_in;
	usbctrl_endpoint_descriptor_t ep_out;
} usbctrl_full_endpoint_descriptor_t;

typedef struct __packed {

    usbctrl_interface_descriptor_t interface_desc;
	usbctrl_endpoint_descriptor_t ep_in;
	usbctrl_endpoint_descriptor_t ep_out;
} usbctrl_full_configuration_descriptor_t;



/*
 * A given interface descriptor hold its interface descriptor,
 * one descriptor for each of its EPs
 * potential functional descriptors to complete
 */
typedef struct __packed {
	usbctrl_interface_descriptor_t         interface;
	usbctrl_full_endpoint_descriptor_t ep[];
} usbctrl_full_interface_descriptor_t;


mbed_error_t usbctrl_get_descriptor(usbctrl_descriptor_type_t  type,
                                    uint8_t                   *buf,
                                    uint32_t                  *desc_size,
                                    usbctrl_context_t         *ctx,
                                    usbctrl_setup_pkt_t       *pkt);

#endif/*!USB_CTRL_DESCRIPTORS_H_*/
