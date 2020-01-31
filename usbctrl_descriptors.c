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
                                    usbctrl_context_t         *ctx,
                                    usbctrl_setup_pkt_t       *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitation */
    if (buf == NULL || ctx == NULL || desc_size == NULL || pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    switch (type) {
        case USB_DESC_DEVICE: {
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
        }
        case USB_DESC_INTERFACE:
            log_printf("[USBCTRL] request iface desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_ENDPOINT:
            log_printf("[USBCTRL] request EP desc\n");
            *desc_size = 0;
            break;
        case USB_DESC_STRING: {
            log_printf("[USBCTRL] request string desc\n");
            *desc_size = 0;
            uint32_t descriptor_size = sizeof(usbctrl_string_descriptor_t);
            if (descriptor_size > 128) {
                log_printf("[USBCTRL] not enough space for string descriptor !!!\n");
            }
            log_printf("[USBCTRL] create string desc of size %d\n", descriptor_size);
            {
                uint8_t *string_desc = buf;
                usbctrl_string_descriptor_t *cfg = (usbctrl_string_descriptor_t *)&(string_desc[0]);
                uint8_t string_type = pkt->wValue & 0xff;
                cfg->bDescriptorType = USB_DESC_STRING;
                /* INFO:  UTF16 double each size */
                switch (string_type) {
                    case 0:
                        cfg->bLength = 4;
                        cfg->wString[0] = LANGUAGE_ENGLISH;
                        *desc_size = 4;
                        break;
                    case CONFIG_USB_DEV_MANUFACTURER_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_MANUFACTURER); ++i) {
                            cfg->wString[i] = CONFIG_USB_DEV_MANUFACTURER[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);
                        break;
                    case CONFIG_USB_DEV_PRODNAME_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_PRODNAME); ++i) {
                            cfg->wString[i] = CONFIG_USB_DEV_PRODNAME[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);
                        break;
                    case CONFIG_USB_DEV_SERIAL_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_SERIAL); ++i) {
                            cfg->wString[i] = CONFIG_USB_DEV_SERIAL[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);
                        break;
                    default:
                        log_printf("[USBCTRL] Unsupported string index requested.\n");
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                        break;
                }
            }
            break;
        }
        case USB_DESC_CONFIGURATION: {
            log_printf("[USBCTRL] request configuration desc\n");
            /* configuration descriptor is dynamic, depends on current config and its number of endpoints... */
            /* FIXME, we should be able to return a config descriptor with more
             * than one interface if needed, including potential successive
             * iface & EPs descriptors */
            /* 1) calculating desc size */
            uint8_t num_ifaces_for_cfg = 0;
            uint32_t descriptor_size =
                sizeof(usbctrl_configuration_descriptor_t);
            for (uint8_t i = 0; i < ctx->interface_num; ++i) {
                if (ctx->interfaces[i].cfg_id == ctx->curr_cfg) {
                    descriptor_size += sizeof(usbctrl_interface_descriptor_t) +
                        ctx->interfaces[i].usb_ep_number *
                        sizeof(usbctrl_endpoint_descriptor_t);
                    num_ifaces_for_cfg++;
                }
            }
            if (descriptor_size > 128) {
                log_printf("[USBCTRL] not enough space for config descriptor !!!\n");
                goto err;
            }
            log_printf("[USBCTRL] create config desc of size %d\n", descriptor_size);
            uint8_t *config_desc = buf;
            {
                usbctrl_configuration_descriptor_t *cfg = (usbctrl_configuration_descriptor_t *)&(config_desc[0]);
                cfg->bLength = sizeof(usbctrl_configuration_descriptor_t);
                cfg->wTotalLength = descriptor_size;
                cfg->bDescriptorType = USB_DESC_CONFIGURATION;
                cfg->bNumInterfaces = num_ifaces_for_cfg;
                cfg->bConfigurationValue = 1;
                cfg->iConfiguration = 0;
                cfg->bmAttributes.reserved7 = 1;
                cfg->bmAttributes.self_powered = 1;
                cfg->bmAttributes.remote_wakeup = 0;
                cfg->bmAttributes.reserved = 0;
                cfg->bMaxPower = 0;
            }
            /* there can be 1, 2 or more interfaces. interfaces offset depends on the previous
             * interfaces number, and are calculated depending on the previous interfaces
             * descriptors (iface+ep) size.
             * To do this, we start at offset 0 after configuration descriptor for the first
             * interface, and at the end of each interface, we increment the offset of the size
             * of the complete interface descriptor, including EP. */
            uint32_t curr_offset = 0;
            for (uint8_t iface_id = 0; iface_id < ctx->interface_num; ++iface_id) {
                if (ctx->interfaces[iface_id].cfg_id == ctx->curr_cfg) {
                    {
                        /* pointing to next field: interface descriptor */
                        usbctrl_interface_descriptor_t *cfg = (usbctrl_interface_descriptor_t*)
                            ((uint8_t*)(&(config_desc[0]) +
                                sizeof(usbctrl_configuration_descriptor_t)))
                            + curr_offset;
                        cfg->bLength = sizeof(usbctrl_interface_descriptor_t);
                        cfg->bDescriptorType = USB_DESC_INTERFACE;
                        cfg->bInterfaceNumber = 0;
                        cfg->bAlternateSetting = 0;
                        cfg->bNumEndpoints = ctx->interfaces[iface_id].usb_ep_number;
                        cfg->bInterfaceClass = ctx->interfaces[iface_id].usb_class;
                        cfg->bInterfaceSubClass = ctx->interfaces[iface_id].usb_subclass;
                        cfg->bInterfaceProtocol = ctx->interfaces[iface_id].usb_protocol;
                        cfg->iInterface = 1;
                    }
                    {
                        uint8_t i = 0;
                        /* and for this interface, handling each EP */
                        for (; i < ctx->interfaces[iface_id].usb_ep_number; ++i) {
                            usbctrl_endpoint_descriptor_t *cfg = (usbctrl_endpoint_descriptor_t*)
                                ((uint8_t*)(&(config_desc[0]) +
                                    sizeof(usbctrl_configuration_descriptor_t) +
                                    + curr_offset +
                                    sizeof(usbctrl_interface_descriptor_t) +
                                    i * (sizeof(usbctrl_endpoint_descriptor_t))));

                            cfg->bLength = sizeof(usbctrl_endpoint_descriptor_t);
                            cfg->bDescriptorType = USB_DESC_ENDPOINT;
                            ctx->interfaces[iface_id].eps[i].ep_num = i + 1;
                            cfg->bEndpointAddress = ctx->interfaces[iface_id].eps[i].ep_num;
                            if (ctx->interfaces[iface_id].eps[i].mode == USB_EP_MODE_WRITE) {
                                cfg->bEndpointAddress |= 0x80; /* set bit 7 to 1 for WRITE (i.e. IN) EPs */
                            }
                            cfg->bmAttributes =
                                ctx->interfaces[iface_id].eps[i].type       |
                                ctx->interfaces[iface_id].eps[i].attr << 2  |
                                ctx->interfaces[iface_id].eps[i].usage << 4;
                            cfg->wMaxPacketSize = ctx->interfaces[iface_id].eps[i].pkt_maxsize;
                            cfg->bInterval = 0;
                        }
                        curr_offset += sizeof(usbctrl_configuration_descriptor_t) +
                            i * sizeof(usbctrl_endpoint_descriptor_t);
                    }
                }
            /* returns the descriptor */
            }
            *desc_size = descriptor_size;
            break;
        }
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