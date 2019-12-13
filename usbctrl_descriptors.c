#include "api/libusbctrl.h"
#include "usbctrl_descriptors.h"
#include "usbctrl.h"

#define MAX_DESC_STRING_SIZE 32 /* max unicode string size supported (to define properly) */
/*
 * Global device descriptor. This descriptor is unique for the entire device,
 * even in case of hybrid (multi-personality) device.
 */
typedef struct __packed usb_device_descriptor {
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
} usb_device_descriptor_t;

/*
 * USB configuration descriptor. Global to the device, specify the
 * device configuration (number of interfaces, power, ...)
 */
typedef struct __packed usb_configuration_descriptor {
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
} usb_configuration_descriptor_t;

/**
 * Interface descriptor set,
 */
typedef struct __packed usb_interface_descriptor {
	uint8_t bLength;
	uint8_t bDescriptorType;
	uint8_t bInterfaceNumber;
	uint8_t bAlternateSetting;
	uint8_t bNumEndpoints;
	uint8_t bInterfaceClass;
	uint8_t bInterfaceSubClass;
	uint8_t bInterfaceProtocol;
	uint8_t iInterface;
} usb_interface_descriptor_t;

/**
 * Endpoint descriptor set for run-time mode (only?).
 */
typedef struct __packed usb_endpoint_descriptor {
	uint8_t  bLength;
	uint8_t  bDescriptorType;
	uint8_t  bEndpointAddress;
    uint8_t  bmAttributes; /* bitmap */
	uint16_t wMaxPacketSize;
	uint8_t  bInterval;

} usb_endpoint_descriptor_t;


typedef struct __packed usb_ctr_full_endpoint_descriptor {
	usb_endpoint_descriptor_t ep_in;
	usb_endpoint_descriptor_t ep_out;
} usb_ctr_full_endpoint_descriptor_t;

/**
 * FIXME: this DFU functional descriptor should be handled at DFU level (not here)
typedef struct __packed usb_functional_descriptor {
    uint8_t bLength;
    uint8_t bDescriptorType;
    struct {
        uint8_t bitCanDnload:1;
        uint8_t bitCanUpload:1;
        uint8_t bitManifestationTolerant:1;
        uint8_t bitWillDetach:1;
        uint8_t reserved:4;
    } bmAttributes;
    uint16_t wDetachTimeOut;
    uint16_t wTransferSize;
    uint16_t bcdDFUVersion;
} usb_dfu_functional_descriptor_t;
 */

/*
 * A given personality descriptor hold its interface descriptor,
 * one descriptor for each of its EPs
 * potential functional descriptors to complete
 */
typedef struct usb_personality_descriptor {
	usb_interface_descriptor_t         interface;
	usb_ctr_full_endpoint_descriptor_t ep[];
} usb_personality_descriptor_t;

/* old
typedef struct __packed usb_ctrl_full_configuration_descriptor {
	usb_configuration_descriptor_t config;
	union {
		usb_ctr_full_endpoint_descriptor_t ep;
		usb_functional_descriptor_t functional_desc;
	};
} usb_ctrl_configuration_descriptor_t;
*/

/**
 * \brief String descriptor.
 */
typedef struct __packed usb_string_descriptor {
	uint8_t bLength;
	uint8_t bDescriptorType;
	uint16_t wString[MAX_DESC_STRING_SIZE];
} usb_string_descriptor_t;

