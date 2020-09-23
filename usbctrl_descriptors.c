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

/*********************************************************************************
 * configuration descriptor related fonctions
 *
 * handling configuration descriptor is the harder part of this file, which requires
 * successive steps that are, in this implementation, separated in methods.
 *
 */

/*
 * Check that the required size to build the overall configuration descriptor is
 * short enough for the given buffer.
 */

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),desc_size+(..),ctx+(..),total_size);
    @ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx);

    @   ensures  \result == MBED_ERROR_NONE || \result == MBED_ERROR_UNKNOWN || \result ==  MBED_ERROR_INVPARAM || \result == MBED_ERROR_UNSUPORTED_CMD ;
    @ ensures 0 <= *total_size <=  MAX_DESCRIPTOR_LEN ;
    @ assigns *total_size, *desc_size, SIZE_DESC_FIXED, FLAG ;
*/

/*
  TODO : be more precise with invparam behavior (but dead code with total_size == null and impossible to reach usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE )
*/

static mbed_error_t usbctrl_handle_configuration_size(__out uint8_t                  *buf,
                                                      __out uint32_t                 *desc_size,
                                                      __in  usbctrl_context_t        * ctx,
                                                      __out uint32_t                 *total_size)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t class_desc_size = 0;
    uint8_t curr_cfg = ctx->curr_cfg;
    uint8_t iface_num = ctx->cfg[curr_cfg].interface_num;
    uint32_t handler;

    if (total_size == NULL) {
        /*INFO: this should be dead code */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*
     * Calculate and generate the complete configuration descriptor
     */
    /* then calculate the overall descriptor size */
    uint32_t descriptor_size = sizeof(usbctrl_configuration_descriptor_t);

    if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
        log_printf("[LIBCTRL] didn't get back handler from ctx\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /*@
      @ loop invariant 0 <= i <= iface_num ;
      @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num-1)));
      @ loop assigns i, descriptor_size, FLAG, errcode,  class_desc_size ;
      @ loop variant (iface_num -i);
      */

    for (uint8_t i = 0; i < iface_num; ++i) {
        uint32_t local_iface_desc_size = 0;
        /* first calculating class descriptor size */
        if (ctx->cfg[curr_cfg].interfaces[i].class_desc_handler != NULL) {
            uint8_t max_buf_size = 255 ; /* max for uint8_t, still smaller than current MAX_BUF_SIZE */

#ifndef __FRAMAC__
            if (handler_sanity_check_with_panic((physaddr_t)ctx->cfg[curr_cfg].interfaces[i].class_desc_handler)) {
                errcode = MBED_ERROR_INVSTATE;
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
                errcode = MBED_ERROR_UNKNOWN;
                goto err;
            }
            log_printf("[LIBCTRL] found one class level descriptor of size %d\n", max_buf_size);
            class_desc_size += max_buf_size; // CDE in order to calculate size of all class descriptor
        } else {
            class_desc_size += 0;
        }
        /* now we can add the potential class descriptor size to the current amount of bytes of the global
         * configuration descriptor */

        //local_iface_desc_size += class_desc_size;

        /* for endpoint, we must not declare CONTROL eps in interface descriptor */
        uint8_t num_ep = 0;

        /* TODO: we should assert that usb_ep_number is smaller or equal to than 8 */
        /*@
          @ loop invariant 0 <= ep <= ctx->cfg[curr_cfg].interfaces[i].usb_ep_number ;
          @ loop assigns num_ep, ep ;
          @ loop variant (ctx->cfg[curr_cfg].interfaces[i].usb_ep_number - ep);
          */

        for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[i].usb_ep_number; ++ep) {
            if (ctx->cfg[curr_cfg].interfaces[i].eps[ep].type != USB_EP_TYPE_CONTROL) {
                ++num_ep;
            }
            /* a full-duplex endpoint consume 2 descriptors */
            if (ctx->cfg[curr_cfg].interfaces[i].eps[ep].dir == USB_EP_DIR_BOTH) {
                ++num_ep;
            }
        }
        /* here we should assert that current size (local_iface_desc_size) is smaller than:
         * sizeof(usbctrl_interface_descriptor_t) + 16*(usbctrl_endpoint_descriptor_t)
         * because num_ep is <= 8 (case EP_DIR=BOTH) */

        local_iface_desc_size += sizeof(usbctrl_interface_descriptor_t) + num_ep * sizeof(usbctrl_endpoint_descriptor_t);
        descriptor_size += local_iface_desc_size;  // CDE : descriptor size without class size

    }

    /* TODO: here we should assert that local_iface_desc_size * num_iface + usbctrl_configuration_descriptor_t is smaller than
     * uint32_t size (4G) to avoid any u32 overflow*/

    /* we add potential class descriptors found above ... From now on, the global descriptor size is
     * complete, and can be sanitized properly in comparison with the passed buffer size */


    /* now, we have calculated the total amount of bytes required:
     * - configuration descriptor
     * - for each iface:
     *   * iface descriptor
     *   * class descriptor (if exists)
     *   * for each endpoint other than control:
     *     x endpoint descriptor
     *
     * the overall descriptor size in bytes must be smaller or equal to the given buffer size (MAX_DESCRIPTOR_LEN).
     */

    //@ split descriptor_size ;
    if(descriptor_size + class_desc_size > MAX_DESCRIPTOR_LEN) {
        log_printf("[USBCTRL] not enough space for config descriptor !!!\n");
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        *desc_size = 0;
        goto err;
    }

    *total_size = descriptor_size + class_desc_size ;
#if defined(__FRAMAC__)
            SIZE_DESC_FIXED = class_desc_size ;
            /*@ assert class_desc_size + descriptor_size <= MAX_DESCRIPTOR_LEN; */
#endif/*__FRAMAC__*/

err:
    return errcode;

}

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),curr_offset);

    @ behavior INVPARAM:
    @   assumes (curr_offset == \null || buf == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing ;

    @ behavior NOSTORAGE:
    @   assumes !(curr_offset == \null || buf == \null) ;
    @   assumes (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   ensures \result == MBED_ERROR_NOSTORAGE ;
    @   assigns \nothing ;

    @ behavior OK:
    @   assumes !(curr_offset == \null || buf == \null) ;
    @   assumes !(*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures *curr_offset == \old(*curr_offset) + (uint32_t)sizeof(usbctrl_configuration_descriptor_t) ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
  CDE : not possible to validate assigns clause because of cast : (usbctrl_configuration_descriptor_t *)&(buf[*curr_offset]) (WP memory model)
*/

static mbed_error_t usbctrl_handle_configuration_write_config_desc(uint8_t *buf,
                                                           uint32_t descriptor_size,
                                                           uint8_t  iface_num,
                                                           uint32_t *curr_offset)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* DEFENSIVE POGRAMMING:
     * these sanitation functions should not be needed when the execution flow
     * is preserved. Thus, in case of execution corruption, this code is keeped */
    if (curr_offset == NULL || buf == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) {
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    usbctrl_configuration_descriptor_t *cfg = (usbctrl_configuration_descriptor_t *)&(buf[*curr_offset]);
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
    *curr_offset += sizeof(usbctrl_configuration_descriptor_t);

err:
    return errcode;
}

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),curr_offset, ctx + (..));

    @ behavior INVPARAM:
    @   assumes (curr_offset == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing ;

    @ behavior NOSTORAGE:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   ensures \result == MBED_ERROR_NOSTORAGE ;
    @   assigns \nothing ;

    @ behavior bad_iface:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes !(*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   assumes iface_id == 255 ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing ;

    @ behavior OK:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes !(*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   assumes iface_id != 255 ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures *curr_offset == \old(*curr_offset) + sizeof(usbctrl_interface_descriptor_t) ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
  CDE : not possible to validate assigns clause because of cast : (usbctrl_interface_descriptor_t*)&(buf[*curr_offset]) (WP memory model)
*/

static mbed_error_t usbctrl_handle_configuration_write_iface_desc(uint8_t *buf,
                                                                  usbctrl_context_t const * const ctx,
                                                                  uint8_t iface_id,
                                                                  uint32_t * curr_offset)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t num_ep = 0;
    uint8_t curr_cfg = ctx->curr_cfg;

    if (buf == NULL || curr_offset == NULL || ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_interface_descriptor_t))) {
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (iface_id == 255) {
        /* DEFENSIVE PROGRAMMING:
         * the expected number of interfaces is limited to a small number, thus, to avoid an u8
         * overflow below, we check its value here */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* pointing to next field: interface descriptor */
    usbctrl_interface_descriptor_t *cfg = (usbctrl_interface_descriptor_t*)&(buf[*curr_offset]);
    cfg->bLength = sizeof(usbctrl_interface_descriptor_t);
    cfg->bDescriptorType = USB_DESC_INTERFACE;
    cfg->bInterfaceNumber = iface_id;
    cfg->bAlternateSetting = 0;

    /*@
       @ loop invariant 0 <= ep <= ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number ;
       @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1))) ;
       @ loop assigns num_ep, ep ;
       @ loop variant (ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - ep);
    */

    for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number; ++ep) {
        if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep].type != USB_EP_TYPE_CONTROL) {
            ++num_ep;
        }
        if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep].dir == USB_EP_DIR_BOTH) {
            ++num_ep;
        }
    }
    cfg->bNumEndpoints = num_ep;
    cfg->bInterfaceClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_class;
    cfg->bInterfaceSubClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_subclass;
    cfg->bInterfaceProtocol = ctx->cfg[curr_cfg].interfaces[iface_id].usb_protocol;
    cfg->iInterface = iface_id + 1;
    *curr_offset += sizeof(usbctrl_interface_descriptor_t);

err:
    return errcode;
}

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),curr_offset, ctx + (..));

    @ behavior INVPARAM:
    @   assumes (curr_offset == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing ;

    @ behavior bad_iface:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes iface_id == 255 ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing ;

    @ behavior OTHER:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes iface_id != 255 ;
    @   ensures \result == MBED_ERROR_NONE ||
                (\result == MBED_ERROR_NOBACKEND && (*curr_offset == \old(*curr_offset))) ||
                (\result == MBED_ERROR_INVPARAM && (*curr_offset == \old(*curr_offset))) ;
    @   assigns  *curr_offset, FLAG ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
  TODO : be more precise with OTHER behavior (pb is with get_handler errcode and class_desc_handler errcode : not possible to try errcode != MBED_ERROR_NONE )
*/

static mbed_error_t usbctrl_handle_configuration_write_class_desc(usbctrl_context_t * ctx,
                                                                  uint8_t  * buf,
                                                                  uint8_t    iface_id,
                                                                  uint32_t * curr_offset)
{

    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t curr_cfg = ctx->curr_cfg;
    uint32_t handler;
    uint32_t max_buf_size;
    uint8_t class_desc_max_size = 0;

    if (buf == NULL || curr_offset == NULL || ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (iface_id == 255) {
        /* DEFENSIVE PROGRAMMING:
         * the expected number of interfaces is limited to a small number, thus, to avoid an u8
         * overflow below, we check its value here */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    max_buf_size = MAX_DESCRIPTOR_LEN - *curr_offset;
    // class level descriptor of current interface

    if (ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler) {
        /* get back the buffer address to pass to the upper handler, so that the upper
         * handler directly forge its descriptor into the buffer */
        uint8_t *cfg = &(buf[*curr_offset]);
        if (usbctrl_get_handler(ctx, &handler) != MBED_ERROR_NONE) {
            log_printf("[LIBCTRL] Unable to get back handler from ctx\n");
            errcode = MBED_ERROR_NOBACKEND;
            goto err;
        }

        /* FIXME: there is a RTE here, to check if the semantic of __FRAMAC__ version is okay, using a noRTE statement globaly */
        /* we need to get back class level descriptor from upper layer. Although, we have already consumed a part of the target buffer and
         * thus we reduce the max allowed size for class descriptor.
         * normally we can assert cur_offset >= MAX_DESCRIPTOR_LEN */
        if (max_buf_size > 256) {
            class_desc_max_size = 255;
        } else {
            /* reducing buffer to effective max buf size if shorter than uint8_t size */
            class_desc_max_size = (uint8_t)(max_buf_size & 0xff);
        }

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
        errcode = ctx->cfg[curr_cfg].interfaces[iface_id].class_desc_handler(iface_id, cfg, &class_desc_max_size, handler);

        if (errcode != MBED_ERROR_NONE) {
            goto err;
        }
        *curr_offset += class_desc_max_size;
    }

err:
    return errcode;
}

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),curr_offset, ctx + (..));

    @ behavior INVPARAM:
    @   assumes (curr_offset == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing ;

    @ behavior OK:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures *curr_offset == \old(*curr_offset) + sizeof(usbctrl_endpoint_descriptor_t) ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
  CDE : not possible to validate assigns clause because of cast : (usbctrl_endpoint_descriptor_t*)&(buf[*curr_offset]) (WP memory model)
*/

static mbed_error_t usbctrl_handle_configuration_write_ep_desc(usbctrl_context_t const * const ctx,
                                                               uint8_t  * buf,
                                                               uint8_t    ep_number,
                                                               usb_ep_dir_t ep_dir,
                                                               uint8_t    iface_id,
                                                               uint8_t    curr_cfg,
                                                               uint32_t * curr_offset)
{

    mbed_error_t errcode = MBED_ERROR_NONE;

    uint8_t poll ;

    if (buf == NULL || curr_offset == NULL || ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    usbctrl_endpoint_descriptor_t *cfg = (usbctrl_endpoint_descriptor_t*)&(buf[*curr_offset]);
    cfg->bLength = sizeof(usbctrl_endpoint_descriptor_t);
    cfg->bDescriptorType = USB_DESC_ENDPOINT;
    cfg->bEndpointAddress = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].ep_num;
    if (ep_dir == USB_EP_DIR_IN) {
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
            uint8_t i = 0;
            /* get back the position of the first '1' bit */

            uint8_t compteur_poll = 9;
            /*@
               @ loop invariant i >= 0 ;
               @ loop invariant poll >= 0 ;
               @ loop invariant 0 <= compteur_poll <= 9 ;
               @ loop assigns poll, i, compteur_poll;
               @ loop variant compteur_poll;
               */
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
    *curr_offset += sizeof(usbctrl_endpoint_descriptor_t);
    /*@ assert *curr_offset == \at(*curr_offset,Pre) + sizeof(usbctrl_endpoint_descriptor_t) ; */

err:
    return errcode;
}



/*********************************************************************************
 * device descriptor handling fonction
 */

/*
 * It is considered here that the buffer is large enough to hold the
 * requested descriptor. The buffer size is under the control of the
 * get_descriptor standard request handler
 */

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),desc_size+(..),ctx+(..));
    @ ensures *desc_size == sizeof(usbctrl_device_descriptor_t);
*/

/*
  CDE : not possible to validate assigns clause because of cast : (usbctrl_device_descriptor_t*)buf (WP memory model)
*/


static void usbctrl_handle_device_desc(uint8_t                   *buf,
                                       uint32_t                  *desc_size,
                                       usbctrl_context_t const   * const ctx)
{
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

    *desc_size = sizeof(usbctrl_device_descriptor_t);
}


/*********************************************************************************
 * string descriptor handling fonction
 */

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),desc_size+(..),pkt+(..));
    @ ensures (\result == MBED_ERROR_UNSUPORTED_CMD &&  *desc_size == 0) ||
         (\result == MBED_ERROR_NONE && (*desc_size == 4 || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER))
                                    || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME)) || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL) ))) ;
*/

/*
  TODO : be more precise with (pkt->wValue & 0xff) behavior
  not possible to validate assigns clause because of cast : (usbctrl_string_descriptor_t *)&(string_desc[0]) (WP memory model)
*/

static mbed_error_t usbctrl_handle_string_desc(__out uint8_t    *buf,
                                    __out uint32_t              *desc_size,
                                    __in usbctrl_setup_pkt_t    *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    const char *USB_DEV_MANUFACTURER = CONFIG_USB_DEV_MANUFACTURER;
    const char *USB_DEV_PRODNAME = CONFIG_USB_DEV_PRODNAME;
    const char *USB_DEV_SERIAL = CONFIG_USB_DEV_SERIAL;
    *desc_size = 0;
    uint32_t descriptor_size = sizeof(usbctrl_string_descriptor_t);
    if (descriptor_size > MAX_DESCRIPTOR_LEN) {
        log_printf("[USBCTRL] not enough space for string descriptor !!!\n");
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        *desc_size = 0;
        goto err;
    }
    log_printf("[USBCTRL] create string desc of size %d\n", descriptor_size);
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
err:
    return errcode;
}


/*********************************************************************************
 * head function, handling all descriptor types.
 * This is the only function exported.
 */

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),desc_size+(..),ctx+(..),pkt+(..));

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
  TODO : be more precise with ensures clause for \result on some behaviors
  clause assigns is impossible to validate because of some casts (and so, loop assigns and loop variant too cannot be validated)
  consequence : partial correction for this function
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
            usbctrl_handle_device_desc(buf, desc_size, ctx);
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
            errcode = usbctrl_handle_string_desc(buf, desc_size, pkt);
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
            uint32_t descriptor_size = 0;

            errcode = usbctrl_handle_configuration_size(buf, desc_size, ctx, &descriptor_size);
            if (errcode != MBED_ERROR_NONE) {
                log_printf("[USBCTRL] failure while calculating total desc size\h");
                goto err;
            }


            /*
             * From now on, we *know* that the overall descriptor size is smaller than the buffer max supported
             * length. We can add successive descriptors into it without risking to overflow the buffer.
             * Descriptors are concatenated with regard to the USB configuration descriptor standard hierarchy,
             * using the same list of descriptor as calculated above.
             *
             * The input buffer is a uint8_t* generic buffer as USB descriptor content is a dynamic, runtime
             * caclucated, list of structure. To handle this, as unions can't be used due to dynamicity, we
             * use an offset in the buffer (a uint8_t * pointer) which always target the begining of the currently
             * being written descriptor. This pointer is explicitely casted into the descriptor that need to be
             * written in order to properly handle the descriptor fields. The offset is then incremented using
             * the descriptor size.
             *
             * C scoping is used for each descriptor handling to avoid any variable shadowing. Each typed
             * descriptor pointer is named 'cfg' and its scope is reduced to the currently being handled descriptor
             * only.
             *
             * FIXME: move each block (configuration, iface desc, class desc and ep desc) to a dedicated small function.
             * This should be easy to do.
             */
            uint32_t curr_offset = 0;

            log_printf("[USBCTRL] create config desc of size %d with %d ifaces\n", descriptor_size, iface_num);
            /*
             * First, creating the configuration descriptor
             */
            errcode = usbctrl_handle_configuration_write_config_desc(buf, descriptor_size, iface_num, &curr_offset);
            if (errcode != MBED_ERROR_NONE) {
                /* by now, this should be dead code as the above function should  never fails*/
                goto err;
            }

            /* there can be 1, 2 or more interfaces. interfaces offset depends on the previous
             * interfaces number, and are calculated depending on the previous interfaces
             * descriptors (iface+ep) size.
             * To do this, we start at offset 0 after configuration descriptor for the first
             * interface, and at the end of each interface, we increment the offset of the size
             * of the complete interface descriptor, including EP. */
            uint8_t max_ep_number ;  // new variable for variant and invariant proof

            /* @
                @ loop invariant 0 <= iface_id <= iface_num ;
                @ loop invariant 0 <= curr_offset <=  255 ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num -1))) ;
                @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1))) ;
                @ loop invariant \valid(buf + (0..255));
                @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number -1)),buf + (0..255));
            */

            for (uint8_t iface_id = 0; iface_id < iface_num; ++iface_id) {
                /*
                 * for each interface, we first need to add the interface descriptor
                 */
                errcode = usbctrl_handle_configuration_write_iface_desc(buf, ctx, iface_id, &curr_offset);
                if (errcode != MBED_ERROR_NONE) {
                    /* by now, this should be dead code as the above function should  never fails*/
                    goto err;
                }

                /*
                 * for each interface, we may then add the associated class descriptor, if it exsists
                 */
                errcode = usbctrl_handle_configuration_write_class_desc(ctx, buf, iface_id, &curr_offset);
                if (errcode != MBED_ERROR_NONE) {
                    goto err;
                }

                /*
                 * for each interface, we finish with each endpoint descriptor, for all non-control EP
                 * INFO: libusbctrl consider that the device handle a signe control EP: EP0
                 */
                /* and for this interface, handling each EP */


                max_ep_number = ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number ;  // variable change in loop

                /* @
                    @ loop invariant \at(max_ep_number,LoopEntry) == \at(max_ep_number,LoopCurrent) ;
                    @ loop invariant 0 <= ep_number <= max_ep_number ;
                    @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - 1))) ;
                    @ loop invariant \valid(buf + (0..255));
                    @ loop invariant \separated(ctx->cfg[curr_cfg].interfaces[iface_id].eps + (0..(ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number - 1)),buf + (0..255));
                */

                for (uint8_t ep_number = 0; ep_number < max_ep_number; ++ep_number) {

                    usb_ep_dir_t ep_dir = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].dir;

                    if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type == USB_EP_TYPE_CONTROL) {
                        /* Control EP (EP0 usage) are not declared here */
                        continue;
                    }
                    switch (ep_dir) {
                        case USB_EP_DIR_BOTH:
                            /* full duplex EP, first handling IP EP descriptor, then handling OUT just after */
                            errcode = usbctrl_handle_configuration_write_ep_desc(ctx, buf, ep_number, USB_EP_DIR_IN, iface_id, curr_cfg, &curr_offset);
                            if (errcode != MBED_ERROR_NONE) {
                                goto err;
                            }
                            errcode = usbctrl_handle_configuration_write_ep_desc(ctx, buf, ep_number, USB_EP_DIR_OUT, iface_id, curr_cfg, &curr_offset);
                            if (errcode != MBED_ERROR_NONE) {
                                goto err;
                            }
                            break;
                        case USB_EP_DIR_IN:
                            errcode = usbctrl_handle_configuration_write_ep_desc(ctx, buf, ep_number, USB_EP_DIR_IN, iface_id, curr_cfg, &curr_offset);
                            if (errcode != MBED_ERROR_NONE) {
                                goto err;
                            }
                            break;
                        case USB_EP_DIR_OUT:
                            errcode = usbctrl_handle_configuration_write_ep_desc(ctx, buf, ep_number, USB_EP_DIR_OUT, iface_id, curr_cfg, &curr_offset);
                            if (errcode != MBED_ERROR_NONE) {
                                goto err;
                            }
                            break;
                        default:
                            errcode = MBED_ERROR_INVPARAM;
                            goto err;

                    }
                }

            /* returns the descriptor */
            }
            /* total configuration descriptor has be forged, update the size */
            if (descriptor_size != curr_offset) {
                /* This SHOULD NOT be possible !!! */
                log_printf("[USBCTRL] forged descriptor size (%d) different from the calculated one (%d) !!!\n", curr_offset, descriptor_size);
            }
            /*@ assert descriptor_size == curr_offset ; */
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
