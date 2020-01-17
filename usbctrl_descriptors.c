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
            desc->idProduct = CONFIG_USB_DEV_PRODUCTID;
            desc->bcdDevice = 0x000;
            desc->iManufacturer = CONFIG_USB_DEV_MANUFACTURER_INDEX;
            desc->iProduct = CONFIG_USB_DEV_PRODNAME_INDEX;
            desc->iSerialNumber = CONFIG_USB_DEV_SERIAL_INDEX;
            desc->bNumConfigurations = ctx->num_cfg;
            /* well, if current cfg is not null, the device desc should be
             * completed with a more complete content (typically a full desc */
#if 0 /* replaced by configuration descriptor request on configuration id x */
            if (ctx->curr_cfg != 0) {
                desc->bDeviceClass = ctx->interfaces[ctx->curr_cfg].usb_class;
                desc->bDeviceSubClass = ctx->interfaces[ctx->curr_cfg].usb_subclass;
                desc->bDeviceProtocol = ctx->interfaces[ctx->curr_cfg].usb_protocol;
            }
#endif
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
            /* configuration descriptor is dynamic, depends on current config and its number of endpoints... */
            /* FIXME, we should be able to return a config descriptor with more
             * than one interface if needed, including potential successive
             * iface & EPs descriptors */
            /* 1) calculating desc size */
            uint32_t descriptor_size =
                sizeof(usbctrl_configuration_descriptor_t) +
                sizeof(usbctrl_interface_descriptor_t) +
                ctx->interfaces[ctx->curr_cfg].usb_ep_number *
                    sizeof(usbctrl_endpoint_descriptor_t);
            if (descriptor_size > 128) {
                log_printf("[USBCTRL] not enough space for config descriptor !!!\n");
            }
            log_printf("[USBCTRL] create config desc of size %d\n", descriptor_size);
            {
            uint8_t *config_desc = buf;
            {
                usbctrl_configuration_descriptor_t *cfg = (usbctrl_configuration_descriptor_t *)&(config_desc[0]);
                cfg->bLength = sizeof(usbctrl_configuration_descriptor_t);
                cfg->bDescriptorType = USB_DESC_CONFIGURATION;
                cfg->bNumInterfaces = 1;
                cfg->bConfigurationValue = 1;
                cfg->iConfiguration = 0;
                cfg->bmAttributes.reserved7 = 1;
                cfg->bmAttributes.self_powered = 1;
                cfg->bmAttributes.remote_wakeup = 0;
                cfg->bmAttributes.reserved = 0;
                cfg->bMaxPower = 0;
            }
            {
                /* pointing to next field: interface descriptor */
                usbctrl_interface_descriptor_t *cfg = (usbctrl_interface_descriptor_t*)
                ((uint8_t*)(&(config_desc[0]) +
                        sizeof(usbctrl_configuration_descriptor_t)));
                cfg->bLength = sizeof(usbctrl_interface_descriptor_t);
                cfg->bDescriptorType = USB_DESC_INTERFACE;
                cfg->bInterfaceNumber = 0;
                cfg->bAlternateSetting = 0;
                cfg->bNumEndpoints = ctx->interfaces[ctx->curr_cfg].usb_ep_number;
                cfg->bInterfaceClass = ctx->interfaces[ctx->curr_cfg].usb_class;
                cfg->bInterfaceSubClass = ctx->interfaces[ctx->curr_cfg].usb_subclass;
                cfg->bInterfaceProtocol = ctx->interfaces[ctx->curr_cfg].usb_protocol;
                cfg->iInterface = 1;
            }
            {
                /* and for this interface, handling each EP */
                for (uint8_t i = 0; i < ctx->interfaces[ctx->curr_cfg].usb_ep_number; ++i) {
                    usbctrl_endpoint_descriptor_t *cfg = (usbctrl_endpoint_descriptor_t*)
                        ((uint8_t*)(&(config_desc[0]) +
                                sizeof(usbctrl_configuration_descriptor_t) +
                                i * (sizeof(usbctrl_endpoint_descriptor_t))));

                    cfg->bLength = sizeof(usbctrl_endpoint_descriptor_t);
                    cfg->bDescriptorType = USB_DESC_ENDPOINT;
                    ctx->interfaces[ctx->curr_cfg].eps[i].ep_num = i + 1;
                    cfg->bEndpointAddress = ctx->interfaces[ctx->curr_cfg].eps[i].ep_num;
                    if (ctx->interfaces[ctx->curr_cfg].eps[i].mode == USB_EP_MODE_READ) {
                        cfg->bEndpointAddress |= 0x8; /* set bit 7 to 1 for READ EPs */
                    }
                    cfg->bmAttributes =
                        ctx->interfaces[ctx->curr_cfg].eps[i].type       |
                        ctx->interfaces[ctx->curr_cfg].eps[i].attr << 2  |
                        ctx->interfaces[ctx->curr_cfg].eps[i].usage << 4;
                    cfg->wMaxPacketSize = ctx->interfaces[ctx->curr_cfg].eps[i].pkt_maxsize;
                    cfg->bInterval = 0;
                }
            }
            *desc_size = descriptor_size;
            /* returns the descriptor */
            }
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
