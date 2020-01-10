#include "libc/string.h"
#include "api/libusbctrl.h"
#include "usbctrl_descriptors.h"
#include "usbctrl.h"

#define MAX_DESC_STRING_SIZE 32 /* max unicode string size supported (to define properly) */
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
/**
 * Endpoint descriptor set for run-time mode (only?).
 */
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

/*
 * It is considered here that the buffer is large enough to hold the
 * requested descriptor. The buffer size is under the control of the
 * get_descriptor standard request handler
 */
mbed_error_t usbctrl_get_descriptor(usbctrl_descriptor_type_t  type,
                                    uint8_t                   *buf,
                                    uint32_t                  *desc_size,
                                    usbctrl_context_t         *ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitation */
    if (buf == NULL || ctx == NULL || desc_size == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    switch (type) {
        case USB_DESC_DEVICE:
            log_printf("[USBCTRL] request device desc\n");
            usbctrl_device_descriptor_t *desc = (usbctrl_device_descriptor_t*)buf;
            desc->bLength = sizeof(usbctrl_device_descriptor_t);
            desc->bDescriptorType = 0x1; /* USB Desc Device */
            desc->bcdUSB = 0x0200; /* USB 2.0 */
            desc->bDeviceClass = 0; /* replaced by default iface */
            desc->bDeviceSubClass = 0;
            desc->bDeviceProtocol = 0;
            desc->bMaxPacketSize = 64; /* on EP0 */
            desc->idVendor = CONFIG_USB_DEV_VENDORID;
            desc->idVendor = CONFIG_USB_DEV_PRODUCTID;
            desc->idVendor = CONFIG_USB_DEV_PRODUCTID;
            desc->bcdDevice = 0x000;
            desc->iManufacturer = CONFIG_USB_DEV_MANUFACTURER_INDEX;
            desc->iProduct = CONFIG_USB_DEV_PRODNAME_INDEX;
            desc->iSerialNumber = CONFIG_USB_DEV_SERIAL_INDEX;
            desc->bNumConfigurations = ctx->num_cfg; /* to be replaced by number of registered config */
            /* well, if current cfg is not null, the device desc should be
             * completed with a more complete content (typically a full desc */
            if (ctx->curr_cfg != 0) {
                desc->bDeviceClass = ctx->interfaces[ctx->curr_cfg].usb_class;
                desc->bDeviceSubClass = ctx->interfaces[ctx->curr_cfg].usb_subclass;
                desc->bDeviceProtocol = ctx->interfaces[ctx->curr_cfg].usb_protocol;
            }
            *desc_size = sizeof(usbctrl_device_descriptor_t);

            break;
        case USB_DESC_INTERFACE:
            log_printf("[USBCTRL] request iface desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_ENDPOINT:
            log_printf("[USBCTRL] request EP desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_STRING:
            log_printf("[USBCTRL] request string desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_CONFIGURATION:
            log_printf("[USBCTRL] request configuration desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_DEV_QUALIFIER:
            log_printf("[USBCTRL] request dev qualifier desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_OTHER_SPEED_CFG:
            log_printf("[USBCTRL] request other speed cfg desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_IFACE_POWER:
            log_printf("[USBCTRL] request iface power desc\n");
            *desc_size = 0;
            break;
        default:
            log_printf("[USBCTRL] request unknown desc\n");
            errcode = MBED_ERROR_INVPARAM;
            goto err;
    }
err:
    return errcode;
}
