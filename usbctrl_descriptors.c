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

/*@
    @ requires \separated(buf,desc_size,ctx,pkt);  // cyril : je ne pense pas que separated sans valid soit une utilisation correcte

    @ behavior invaparam:
    @   assumes  (buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ behavior USB_DESC_DEVICE:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_DEVICE ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == sizeof(usbctrl_device_descriptor_t) ;

    @ behavior USB_DESC_INTERFACE:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_INTERFACE ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;

    @ behavior USB_DESC_ENDPOINT:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_ENDPOINT ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;

    @ behavior USB_DESC_STRING:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_STRING ;
    @   ensures (\result == MBED_ERROR_UNSUPORTED_CMD &&  *desc_size == 0) ||
         (\result == MBED_ERROR_NONE && (*desc_size == 4 || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER))
                                    || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME)) || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL) ))) ;

    @ behavior USB_DESC_CONFIGURATION:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_CONFIGURATION ;
    @   ensures is_valid_error(\result) ;

    @ behavior USB_DESC_DEV_QUALIFIER:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_DEV_QUALIFIER ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;

    @ behavior USB_DESC_OTHER_SPEED_CFG:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_OTHER_SPEED_CFG ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;

    @ behavior USB_DESC_IFACE_POWER:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes type == USB_DESC_IFACE_POWER ;
    @   ensures  \result == MBED_ERROR_NONE && *desc_size == 0 ;

    @ behavior other_type:
    @   assumes !(buf == \null || ctx == \null || desc_size == \null || pkt == \null ) ;
    @   assumes (type != USB_DESC_DEVICE) && (type != USB_DESC_INTERFACE) && (type != USB_DESC_ENDPOINT) && (type != USB_DESC_STRING) && (type != USB_DESC_CONFIGURATION) &&
                (type != USB_DESC_DEV_QUALIFIER) && (type != USB_DESC_OTHER_SPEED_CFG) && (type != USB_DESC_IFACE_POWER) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;

    @ complete behaviors ;
    @ disjoint behaviors ;

*/

/*
    1 problemes pour finir de spécifier la fonction:  cast du type : usbctrl_device_descriptor_t *desc = (usbctrl_device_descriptor_t*)buf;
                            desc->bLength = sizeof(usbctrl_device_descriptor_t);
            wp est perdu, assigns *buf ne passe pas (en même temps, buf est de type uin8_t *...)

    un bug :   uint32_t max_buf_size = *desc_size - curr_offset
                *desc_size quand on arrive ici vaut 0... alors que curr_offset >0
                probleme pour EVA  assert rte: unsigned_overflow: 0 ≤ *desc_size - curr_offset;

    pour le compteur poll, eva n'arrive pas à prouver qu'il reste >= 0

    les loop assigns ne passent pas également

        @ requires is_valid_descriptor_type(type);  pas nécessaire comme il y a default dans le switch

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

    #if defined(__FRAMAC__)
    const char *USB_DEV_MANUFACTURER = CONFIG_USB_DEV_MANUFACTURER;
    const char *USB_DEV_PRODNAME = CONFIG_USB_DEV_PRODNAME;
    const char *USB_DEV_SERIAL = CONFIG_USB_DEV_SERIAL;
    #endif/*__FRAMAC__*/


    switch (type) {
        case USB_DESC_DEVICE: {
            log_printf("[USBCTRL] request device desc (num cfg: %d)\n", ctx->num_cfg);
            usbctrl_device_descriptor_t *desc = (usbctrl_device_descriptor_t*)buf;
            desc->bLength = sizeof(usbctrl_device_descriptor_t);
            desc->bDescriptorType = 0x1; /* USB Desc Device */
            desc->bcdUSB = 0x0200; /* USB 2.0 */
            desc->bDeviceClass = 0; /* replaced by default iface */
            desc->bDeviceSubClass = 0;
            desc->bDeviceProtocol = 0;
            desc->bMaxPacketSize = 64; /* on EP0 */
            desc->idVendor = CONFIG_USR_LIB_USBCTRL_DEV_VENDORID;
            desc->idProduct = CONFIG_USR_LIB_USBCTRL_DEV_PRODUCTID;
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
                #if defined(__FRAMAC__)

                switch (string_type) {
                    case 0:
                        cfg->bLength = 4;
                        cfg->wString[0] = LANGUAGE_ENGLISH;
                        *desc_size = 4;
                        break;


                    case CONFIG_USB_DEV_MANUFACTURER_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);

                        /*@
                            @ loop invariant \valid(cfg->wString + (0..(sizeof(USB_DEV_MANUFACTURER)-1)));
                            @ loop invariant \valid_read(USB_DEV_MANUFACTURER + (0..(sizeof(CONFIG_USB_DEV_MANUFACTURER)-1)));
                            @ loop invariant 0 <= i <= sizeof(CONFIG_USB_DEV_MANUFACTURER) ;
                            @ loop assigns i, *cfg ;
                            @ loop variant sizeof(CONFIG_USB_DEV_MANUFACTURER) - i ;
                        */

                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_MANUFACTURER); ++i) {
                            cfg->wString[i] = USB_DEV_MANUFACTURER[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER);
                        break;
                    case CONFIG_USB_DEV_PRODNAME_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);

                        /*@
                            @ loop invariant \valid(cfg->wString + (0..(sizeof(CONFIG_USB_DEV_PRODNAME)-1)));
                            @ loop invariant \valid_read(USB_DEV_PRODNAME + (0..(sizeof(CONFIG_USB_DEV_PRODNAME)-1)));
                            @ loop invariant 0 <= i <= sizeof(CONFIG_USB_DEV_PRODNAME) ;
                            @ loop assigns i, *cfg ;
                            @ loop variant sizeof(CONFIG_USB_DEV_PRODNAME) - i ;
                        */

                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_PRODNAME); ++i) {
                            cfg->wString[i] = USB_DEV_PRODNAME[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME);
                        break;
                    case CONFIG_USB_DEV_SERIAL_INDEX:
                        cfg->bLength = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);

                        /*@
                            @ loop invariant \valid(cfg->wString + (0..(sizeof(CONFIG_USB_DEV_SERIAL)-1)));
                            @ loop invariant \valid_read(USB_DEV_SERIAL + (0..(sizeof(CONFIG_USB_DEV_SERIAL)-1)));
                            @ loop invariant 0 <= i <= sizeof(CONFIG_USB_DEV_SERIAL) ;
                            @ loop assigns i, *cfg ;
                            @ loop variant sizeof(CONFIG_USB_DEV_SERIAL) - i ;
                        */
                        for (uint32_t i = 0; i < sizeof(CONFIG_USB_DEV_SERIAL); ++i) {
                            cfg->wString[i] = USB_DEV_SERIAL[i];
                        }
                        *desc_size = 2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL);
                        break;
                    default:
                        log_printf("[USBCTRL] Unsupported string index requested.\n");
                        errcode = MBED_ERROR_UNSUPORTED_CMD;
                        goto err;
                        break;
                }
            #else

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

            #endif/*__FRAMAC__*/
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
            uint32_t handler;

            if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
                log_printf("[LIBCTRL] didn't get back handler from ctx\n");
                goto err;
            }

            /* @
                @ loop invariant 0 <= i <= iface_num ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num-1)));
                @ loop invariant \separated(buf,ctx);
                @ loop assigns i, class_desc_size, errcode  ;
                @ loop variant (iface_num -i);
            */

            for (uint8_t i = 0; i < iface_num; ++i) {
                if (ctx->cfg[curr_cfg].interfaces[i].class_desc_handler != NULL) {
                    uint8_t max_buf_size = MAX_DESCRIPTOR_LEN-1 ;

                    #ifndef __FRAMAC__
                    if (handler_sanity_check_with_panic((physaddr_t)ctx->cfg[curr_cfg].interfaces[i].class_desc_handler)) {
                        goto err;
                    }
                    #endif

                    #if defined(__FRAMAC__)
                    FLAG = false ;
                    #endif/*__FRAMAC__*/

                    /*@ assert ctx->cfg[curr_cfg].interfaces[i].class_desc_handler ∈ {&class_get_descriptor}; */
                    /*@ calls class_get_descriptor; */
                    errcode = ctx->cfg[curr_cfg].interfaces[i].class_desc_handler(i, buf, &max_buf_size, handler);
                    if (errcode != MBED_ERROR_NONE) {
                        log_printf("[LIBCTRL] failure while getting class desc: %d\n", errcode);
                        goto err;
                    }
                    log_printf("[LIBCTRL] found one class level descriptor of size %d\n", max_buf_size);
                    class_desc_size += max_buf_size;
                }
            }

            /*
             * Calculate and generate the complete configuration descriptor
             */
            /* then calculate the overall descriptor size */
            uint32_t descriptor_size = sizeof(usbctrl_configuration_descriptor_t);

             /* @
                @ loop invariant 0 <= i <= iface_num ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num-1)));
                @ loop assigns i, descriptor_size  ;
                @ loop variant (iface_num -i);
            */

            for (uint8_t i = 0; i < iface_num; ++i) {
                /* for endpoint, we must not declare CONTROL eps in interface descriptor */
                uint8_t num_ep = 0;

                /* @
                    @ loop invariant 0 <= ep <= ctx->cfg[curr_cfg].interfaces[i].usb_ep_number ;
                    @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[i].eps + (0..(ctx->cfg[curr_cfg].interfaces[i].usb_ep_number -1))) ;
                    @ loop assigns num_ep, ep ;
                    @ loop variant (ctx->cfg[curr_cfg].interfaces[i].usb_ep_number - ep);
                */

                for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[i].usb_ep_number; ++ep) {
                    if (ctx->cfg[curr_cfg].interfaces[i].eps[ep].type != USB_EP_TYPE_CONTROL) {
                        ++num_ep;
                    }
                }
                descriptor_size += sizeof(usbctrl_interface_descriptor_t) + num_ep * sizeof(usbctrl_endpoint_descriptor_t);
            }

            /* we add potential class descriptors found above ... From now on, the global descriptor size is
             * complete, and can be sanitized properly in comparison with the passed buffer size */
            

            /* before starting to build descriptor, check that we have enough memory space in the given buffer */
            
            if( (descriptor_size + class_desc_size) > MAX_DESCRIPTOR_LEN    ){
                log_printf("[USBCTRL] not enough space for config descriptor !!!\n");
                errcode = MBED_ERROR_UNSUPORTED_CMD;
                *desc_size = 0;
                goto err;
            }

            descriptor_size += class_desc_size;
            #if defined(__FRAMAC__)
            SIZE_DESC_FIXED = class_desc_size ;
            #endif/*__FRAMAC__*/

            log_printf("[USBCTRL] create config desc of size %d with %d ifaces\n", descriptor_size, iface_num);
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

            /* @
                @ loop invariant 0 <= iface_id <= iface_num ;
                @ loop invariant 0 <= curr_offset <=  255 ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num -1))) ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1))) ;
                @ loop invariant \valid(buf + (0..255));
                @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1)),buf + (0..255));
                @ loop assigns iface_id, curr_offset, errcode, buf[0..255] ;
                @ loop variant (iface_num - iface_id) ;
            */

            for (uint8_t iface_id = 0; iface_id < iface_num; ++iface_id) {
                    {
                        /* pointing to next field: interface descriptor */
                        usbctrl_interface_descriptor_t *cfg = (usbctrl_interface_descriptor_t*)&(buf[curr_offset]);
                        /* @ assert &buf[curr_offset] ==  cfg ; */
                        cfg->bLength = sizeof(usbctrl_interface_descriptor_t);
                        cfg->bDescriptorType = USB_DESC_INTERFACE;
                        cfg->bInterfaceNumber = iface_id;
                        cfg->bAlternateSetting = 0;

                        uint8_t num_ep = 0;
                /* @
                    @ loop invariant 0 <= ep <= ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number ;
                    @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1))) ;
                    @ loop assigns num_ep, ep ;
                    @ loop variant (ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - ep);
                */

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
                        // class level descriptor of current interface

                        if (ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler) {
                            uint8_t *cfg = &(buf[curr_offset]);
                            uint32_t handler;
                            if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
                                log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
                            }

                            /* FIXME: there is a RTE here, to check if the semantic of __FRAMAC__ version is okay, using a noRTE statement globaly */
                            /* we need to get back class level descriptor from upper layer. Although, we have already consumed a part of the target buffer and
                             * thus we reduce the max allowed size for class descriptor.
                             * normally we can assert cur_offset >= MAX_DESCRIPTOR_LEN */
                            uint32_t max_buf_size = MAX_DESCRIPTOR_LEN - curr_offset;

                            // PTH: patch au dessus devrait corriger le RTE, à confirmer par EVA
                            // Cyril : bug : *desc_size quand on arrive ici vaut 0... alors que curr_offset >0
                            // Cyril : probleme pour EVA /*@ assert rte: unsigned_overflow: 0 ≤ *desc_size - curr_offset;

                        #ifndef __FRAMAC__
                            if (handler_sanity_check_with_panic((physaddr_t)ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler)) {
                                goto err;
                            }
                        #endif
                        
                        #if defined(__FRAMAC__)
                            FLAG = true ;
                        #endif/*__FRAMAC__*/

                            /*@ assert ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler ∈ {&class_get_descriptor}; */
                            /*@ calls class_get_descriptor; */
                            errcode = ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler(iface_id, cfg, &max_buf_size, handler);

                            if (errcode != MBED_ERROR_NONE) {
                                goto err;
                            }
                            curr_offset += max_buf_size;
                        }
                    }
                    {
                        /* and for this interface, handling each EP */

                        uint8_t poll ;
                /* @
                    @ loop invariant 0 <= ep_number <= ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number ;
                    @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - 1))) ;
                    @ loop invariant \valid(buf + (0..255));
                    @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - 1)),buf + (0..255));
                    @ loop invariant 0 <= curr_offset <=  255 ;
                    @ loop assigns ep_number, poll, curr_offset, buf[0..255];
                    @ loop variant (ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - ep_number);
                */

                        for (uint8_t ep_number = 0; ep_number < ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number; ++ep_number) {
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type == USB_EP_TYPE_CONTROL) {
                                /* Control EP (EP0 usage) are not declared here */
                                continue;
                            }
                            usbctrl_endpoint_descriptor_t *cfg = (usbctrl_endpoint_descriptor_t*)&(buf[curr_offset]); // modèle mémoire cast à tester, sinon assert
                            cfg->bLength = sizeof(usbctrl_endpoint_descriptor_t);
                            cfg->bDescriptorType = USB_DESC_ENDPOINT;
                            cfg->bEndpointAddress = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].ep_num;

                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].dir == USB_EP_DIR_IN) {
                                cfg->bEndpointAddress |= 0x80; /* set bit 7 to 1 for IN EPs */
                            }

                            cfg->bmAttributes =
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type       |
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].attr << 2  |
                                ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].usage << 4;
                            cfg->wMaxPacketSize = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].pkt_maxsize;

                            /* See table 9.3: microframe interval: bInterval specification */
                            if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type == USB_EP_TYPE_INTERRUPT) {
                                /* in case of HS driver, bInterval == 2^(interval-1), where interval is the
                                 * uframe length. In FS, the interval is free between 1 and 255. To simplify
                                 * the handling of bInterval, knowing that drivers both set uFrame interval to 3
                                 * we use the same 2^(interval-1) calculation for HS and FS */
                                /* TODO: here, we consider that the usb backend driver set the uFrame interval to 3,
                                 * it would be better to get back the uFrame interval from the driver and calculate
                                 * the bInterval value */
                                /* calculating interval depending on backend driver, to get
                                 * back the same polling interval (i.e. 64 ms, hardcoded by now */
                                poll = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].poll_interval;
                                /* falling back to 1ms polling, if not set */
                                if (poll == 0) {
                                    log_printf("[USBCTRL] invalid poll interval %d\n", poll);
                                    poll = 1;
                                }
                                if (usb_backend_drv_get_speed() == USB_BACKEND_DRV_PORT_HIGHSPEED) {
                                    /* value in poll is set in ms, in HS, value is 2^(interval-1)*125us
                                     * here, we get the position of the first bit at 1 in poll value, and add 2 to this
                                     * value, to get the same result as the above */
                                    uint8_t i = 0;  // Cyril : on a déjà une boucle avec i déclaré, je pense qu'il faut nommer deux variables différentes (variable renommé en ep_number)
                                    /* get back the position of the first '1' bit */

                                    uint8_t compteur_poll = 9;
                                    /* @
                                        @ loop invariant i >= 0 ;
                                        @ loop invariant poll >= 0 ;
                                        @ loop invariant compteur_poll >= 0 ;
                                        @ loop assigns poll, i, compteur_poll;
                                        @ loop variant compteur_poll;
                                    */
                                      // Cyril : pour faire passer frama, on peut faire un compteur max de 9 (poll a 8 bits) pour faire un variant sur ce compteur...
                                      // ou 9 -i en variant
                                    while (!(poll & 0x1) && compteur_poll > 0) {
                                        poll >>= 1;
                                        i++;
                                        compteur_poll -- ;
                                    }
                                    /* binary shift left by 2, to handle (interval-1)*125us from a value in milisecond */
                                    i+=2;
                                    cfg->bInterval = i;
                                 } else {
                                    /* in Fullspeed, the bInterval field is directly set in ms, between 1 and 255 */
                                    cfg->bInterval = poll;
                                  }
                            } else {
                                /* for BULK EP, we set bInterval to 0 */
                                cfg->bInterval = 0;
                            }
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
