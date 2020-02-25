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
mbed_error_t usbctrl_get_descriptor(__in usbctrl_descriptor_type_t  type,
                                    __out uint8_t                   *buf,
                                    __out uint32_t                  *desc_size,
                                    __in  usbctrl_context_t         *ctx,
                                    __in usbctrl_setup_pkt_t       *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitation */
    if (buf == NULL || ctx == NULL || desc_size == NULL || pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    switch (type) {
        case USB_DESC_DEVICE: {
            printf("[USBCTRL] request device desc (num cfg: %d)\n", ctx->num_cfg);
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
#if 0
            /* if we have only one cfg and one iface, we can set device-wide
             * information from iface */
            if (ctx->num_cfg == 1 && ctx->cfg[ctx->curr_cfg].interface_num == 1) {
                desc->bDeviceClass = ctx->cfg[ctx->curr_cfg].interfaces[0].usb_class;
                desc->bDeviceSubClass = ctx->cfg[ctx->curr_cfg].interfaces[0].usb_subclass;
                desc->bDeviceProtocol = ctx->cfg[ctx->curr_cfg].interfaces[0].usb_protocol;
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
            if (descriptor_size > MAX_DESCRIPTOR_LEN) {
                log_printf("[USBCTRL] not enough space for string descriptor !!!\n");
                errcode = MBED_ERROR_UNSUPORTED_CMD;
                *desc_size = 0;
                goto err;
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
            printf("[USBCTRL] request configuration desc\n");
            /* configuration descriptor is dynamic, depends on current config and its number of endpoints... */
            /* FIXME, we should be able to return a config descriptor with more
             * than one interface if needed, including potential successive
             * iface & EPs descriptors */
            /* 1) calculating desc size */
            //uint8_t requested_configuration = pkt->wValue; /* TODO to be used */
            uint8_t curr_cfg = ctx->curr_cfg;
            uint8_t iface_num = ctx->cfg[curr_cfg].interface_num;

            /* is there, at upper layer, an additional class descriptor for
             * current configuration ? if yes, we get back this descriptor
             * and add it to the complete configuration descriptor we send
             * to the host. */
            /* Here, we only calculate, for each interface, if there is a
             * class descriptor, its size. The effective descriptor will
             * be stored later, when the overall configuration descriptor
             * is forged. */
            uint32_t class_desc_size = 0;
            for (uint8_t i = 0; i < iface_num; ++i) {
                if (ctx->cfg[curr_cfg].interfaces[i].class_desc_handler != NULL) {
                    uint32_t max_buf_size = MAX_DESCRIPTOR_LEN;
                    errcode = ctx->cfg[curr_cfg].interfaces[i].class_desc_handler(buf, &max_buf_size, ctx);
                    if (errcode != MBED_ERROR_NONE) {
                        printf("[LIBCTRL] failure while getting class desc: %d\n", errcode);
                        goto err;
                    }
                    printf("[LIBCTRL] found one class level descriptor of size %d\n", max_buf_size);
                    class_desc_size += max_buf_size;
                }
            }

            /*
             * Calculate and generate the complete configuration descriptor
             */
            /* then calculate the overall descriptor size */
            uint32_t descriptor_size = sizeof(usbctrl_configuration_descriptor_t);
            for (uint8_t i = 0; i < iface_num; ++i) {
                /* for endpoint, we must not declare CONTROL eps in interface descriptor */
                uint8_t num_ep = 0;
                for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[i].usb_ep_number; ++ep) {
                    if (ctx->cfg[curr_cfg].interfaces[i].eps[ep].type != USB_EP_TYPE_CONTROL) {
                        ++num_ep;
                    }
                }
                descriptor_size += sizeof(usbctrl_interface_descriptor_t) +
                    num_ep * sizeof(usbctrl_endpoint_descriptor_t);
            }
            /* we add potential class descriptors found above ... From now on, the global descriptor size is
             * complete, and can be sanitized properly in comparison with the passed buffer size */
            descriptor_size += class_desc_size;

            if (descriptor_size > MAX_DESCRIPTOR_LEN) {
                printf("[USBCTRL] not enough space for config descriptor !!!\n");
                errcode = MBED_ERROR_UNSUPORTED_CMD;
                *desc_size = 0;
                goto err;
            }
            printf("[USBCTRL] create config desc of size %d with %d ifaces\n", descriptor_size, iface_num);
            uint32_t curr_offset = 0;
            uint8_t *config_desc = &(buf[curr_offset]);
            {
                usbctrl_configuration_descriptor_t *cfg = (usbctrl_configuration_descriptor_t *)&(config_desc[0]);
                cfg->bLength = sizeof(usbctrl_configuration_descriptor_t);
                cfg->wTotalLength = descriptor_size;
                cfg->bDescriptorType = USB_DESC_CONFIGURATION;
                cfg->bNumInterfaces = iface_num;
                cfg->bConfigurationValue = 1;
                cfg->iConfiguration = 0;
                cfg->bmAttributes.reserved7 = 1;
                cfg->bmAttributes.self_powered = 1;
                cfg->bmAttributes.remote_wakeup = 0;
                cfg->bmAttributes.reserved = 0;
                cfg->bMaxPower = 0;
                curr_offset += sizeof(usbctrl_configuration_descriptor_t);
            }
            /* there can be 1, 2 or more interfaces. interfaces offset depends on the previous
             * interfaces number, and are calculated depending on the previous interfaces
             * descriptors (iface+ep) size.
             * To do this, we start at offset 0 after configuration descriptor for the first
             * interface, and at the end of each interface, we increment the offset of the size
             * of the complete interface descriptor, including EP. */
            for (uint8_t iface_id = 0; iface_id < iface_num; ++iface_id) {
                    {
                        /* pointing to next field: interface descriptor */
                        usbctrl_interface_descriptor_t *cfg = (usbctrl_interface_descriptor_t*)&(buf[curr_offset]);
                        cfg->bLength = sizeof(usbctrl_interface_descriptor_t);
                        cfg->bDescriptorType = USB_DESC_INTERFACE;
                        cfg->bInterfaceNumber = iface_id;
                        cfg->bAlternateSetting = 0;

                        uint8_t num_ep = 0;
                        for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number; ++ep) {
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep].type != USB_EP_TYPE_CONTROL) {
                                ++num_ep;
                            }
                        }
                        cfg->bNumEndpoints = num_ep;

                        cfg->bInterfaceClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_class;
                        cfg->bInterfaceSubClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_subclass;
                        cfg->bInterfaceProtocol = ctx->cfg[curr_cfg].interfaces[iface_id].usb_protocol;
                        cfg->iInterface = 1;
                        curr_offset += sizeof(usbctrl_interface_descriptor_t);
                    }
                    {
                        /* class level descriptor of current interface */
                        if (ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler != NULL) {
                            uint8_t *cfg = &(buf[curr_offset]);
                            uint32_t max_buf_size = *desc_size - curr_offset;
                            errcode = ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler(cfg, &max_buf_size, ctx);
                            if (errcode != MBED_ERROR_NONE) {
                                goto err;
                            }
                            curr_offset += max_buf_size;
                        }
                    }
                    {
                        /* and for this interface, handling each EP */
                        for (uint8_t i = 0; i < ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number; ++i) {
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[i].type == USB_EP_TYPE_CONTROL) {
                                /* Control EP (EP0 usage) are not declared here */
                                continue;
                            }
                            usbctrl_endpoint_descriptor_t *cfg = (usbctrl_endpoint_descriptor_t*)&(buf[curr_offset]);

                            cfg->bLength = sizeof(usbctrl_endpoint_descriptor_t);
                            cfg->bDescriptorType = USB_DESC_ENDPOINT;
                            cfg->bEndpointAddress = ctx->cfg[curr_cfg].interfaces[iface_id].eps[i].ep_num;
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[i].dir == USB_EP_DIR_IN) {
                                cfg->bEndpointAddress |= 0x80; /* set bit 7 to 1 for IN EPs */
                            }
                            cfg->bmAttributes =
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[i].type       |
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[i].attr << 2  |
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[i].usage << 4;
                            cfg->wMaxPacketSize = ctx->cfg[curr_cfg].interfaces[iface_id].eps[i].pkt_maxsize;
                            cfg->bInterval = 0;
                            curr_offset += sizeof(usbctrl_endpoint_descriptor_t);
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
