#include "libc/string.h"
#include "libc/nostd.h"
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

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_configuration_size(__out uint8_t                  *buf,
                                               __out uint32_t                 *desc_size,
                                               __in  usbctrl_context_t        * ctx,
                                               __out uint32_t                 *total_size)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t class_desc_size = 0;
    uint8_t iad_size = 0;
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

    bool composite = false;
    uint8_t curr_composite = 0;
    /*@
      @ loop invariant 0 <= i <= iface_num ;
      @ loop invariant \valid_read(ctx->cfg[curr_cfg].interfaces + (0..(iface_num-1)));
      @ loop assigns i, descriptor_size, FLAG, errcode,  class_desc_size, composite, curr_composite, iad_size ;
      @ loop variant (iface_num -i);
      */
    for (uint8_t i = 0; i < iface_num; ++i) {
        uint32_t local_iface_desc_size = 0;
        /* first calculating class descriptor size */
        if (ctx->cfg[curr_cfg].interfaces[i].composite_function == true) {
            composite = true;
            if (curr_composite != ctx->cfg[curr_cfg].interfaces[i].composite_function_id) {
                /* new composite function */
                curr_composite = ctx->cfg[curr_cfg].interfaces[i].composite_function_id;
                iad_size = sizeof(usbctrl_iad_descriptor_t);
            } else {
                /* continuing composite */
                iad_size = 0;
            }
        } else {
            iad_size = 0;
            composite = false;
        }
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
            if (max_buf_size > (255 - class_desc_size)) {
                /* uint8_t overflow check */
                log_printf("[LIBCTRL] class descriptor len too long!\n");
                errcode = MBED_ERROR_UNSUPORTED_CMD;
                goto err;
            }
            /*@ assert max_buf_size <= (255 - class_desc_size); */
            class_desc_size += (uint8_t)(max_buf_size & 0xff); // CDE in order to calculate size of all class descriptor
        } else {
            class_desc_size += 0;
        }
        /* now we can add the potential class descriptor size to the current amount of bytes of the global
         * configuration descriptor */

        //local_iface_desc_size += class_desc_size;

        /* for endpoint, we must not declare CONTROL eps in interface descriptor */
        uint8_t num_ep = 0;

        /*@
          @ loop invariant 0 <= ep <= ctx->cfg[curr_cfg].interfaces[i].usb_ep_number ;
          @ loop assigns num_ep, ep ;
          @ loop variant (ctx->cfg[curr_cfg].interfaces[i].usb_ep_number - ep);
          */

        for (uint8_t ep = 0; ep < ctx->cfg[curr_cfg].interfaces[i].usb_ep_number; ++ep) {
            if (ctx->cfg[curr_cfg].interfaces[i].eps[ep].type == USB_EP_TYPE_CONTROL) {
                /* Control EP is out of scope */
                continue;
            }
            /* a full-duplex endpoint consume 2 descriptors */
            if (ctx->cfg[curr_cfg].interfaces[i].eps[ep].dir == USB_EP_DIR_BOTH) {
                ++num_ep;
            }
            ++num_ep;
        }
        /* here we should assert that current size (local_iface_desc_size) is smaller than:
         * sizeof(usbctrl_interface_descriptor_t) + 16*(usbctrl_endpoint_descriptor_t)
         * because num_ep is <= 8 (case EP_DIR=BOTH) */

        local_iface_desc_size += sizeof(usbctrl_interface_descriptor_t) + num_ep * sizeof(usbctrl_endpoint_descriptor_t);
        descriptor_size += local_iface_desc_size;  // CDE : descriptor size without class size
        descriptor_size += iad_size;

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
    if((descriptor_size + class_desc_size) >= MAX_DESCRIPTOR_LEN) {
        log_printf("[USBCTRL] not enough space for config descriptor !!!\n");
        errcode = MBED_ERROR_UNSUPORTED_CMD;
        *desc_size = 0;
        /*@ assert ((class_desc_size + descriptor_size) >= MAX_DESCRIPTOR_LEN); */
        goto err;
    }
    /*@ assert class_desc_size + descriptor_size <= MAX_DESCRIPTOR_LEN; */
    *total_size = descriptor_size + class_desc_size ;

#if defined(__FRAMAC__)
            SIZE_DESC_FIXED = class_desc_size ;

#endif/*__FRAMAC__*/
err:
    return errcode;

}

/*@
    @ requires \valid(cfg) && \valid_read(buf + (0 .. sizeof(usbctrl_configuration_descriptor_t)-1)) ;
    @ assigns *cfg ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_configuration_desc_from_buff(__out usbctrl_configuration_descriptor_t *cfg, __in const uint8_t *buf)
{
    cfg->bLength                      = buf[0];
    cfg->bDescriptorType              = buf[1];
    cfg->wTotalLength                 = ((uint16_t)buf[3] << 8) | buf[2];
    cfg->bNumInterfaces               = buf[4];
    cfg->bConfigurationValue          = buf[5];
    cfg->iConfiguration               = buf[6];
    cfg->bmAttributes.reserved        = (buf[7] & 0x1f);
    cfg->bmAttributes.remote_wakeup   = (buf[7] >> 5) & 0x1;
    cfg->bmAttributes.self_powered    = (buf[7] >> 6) & 0x1;
    cfg->bmAttributes.reserved7       = (buf[7] >> 7) & 0x1;
    cfg->bMaxPower                    = buf[8];

    return;
}


/*@
    @ requires \valid_read(cfg) && \valid(buf + (0 .. sizeof(usbctrl_configuration_descriptor_t)-1)) ;
    @ assigns buf[0 .. sizeof(usbctrl_configuration_descriptor_t)-1] ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_configuration_desc_to_buff(__in const usbctrl_configuration_descriptor_t *cfg, __out uint8_t *buf)
{
    buf[0] = cfg->bLength;
    buf[1] = cfg->bDescriptorType;
    buf[2] = (uint8_t)(cfg->wTotalLength & 0xff);
    buf[3] = (uint8_t)(cfg->wTotalLength >> 8) & 0xff;
    buf[4] = cfg->bNumInterfaces;
    buf[5] = cfg->bConfigurationValue;
    buf[6] = cfg->iConfiguration;
    buf[7] = (cfg->bmAttributes.reserved) | (cfg->bmAttributes.remote_wakeup << 5) | (cfg->bmAttributes.self_powered << 6) | (cfg->bmAttributes.reserved7 << 7);
    buf[8] = cfg->bMaxPower;

    return;
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
  RBE : fix attempt
*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_configuration_write_config_desc(uint8_t *buf,
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
    //usbctrl_configuration_descriptor_t *cfg = (usbctrl_configuration_descriptor_t *)&(buf[*curr_offset]);
    usbctrl_configuration_descriptor_t _cfg;
    usbctrl_configuration_descriptor_t *cfg = &_cfg;
    usbctrl_configuration_desc_from_buff(cfg, (uint8_t*)&(buf[*curr_offset]));

    cfg->bLength = sizeof(usbctrl_configuration_descriptor_t);
    if (descriptor_size > 65535) {
        /* This should never happen */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    cfg->wTotalLength = descriptor_size & 0xffff;
    cfg->bDescriptorType = USB_DESC_CONFIGURATION;
    cfg->bNumInterfaces = iface_num;
    cfg->bConfigurationValue = 1;
    cfg->iConfiguration = 0;
    cfg->bmAttributes.reserved7 = 1;
    cfg->bmAttributes.self_powered = 1;
    cfg->bmAttributes.remote_wakeup = 0;
    cfg->bmAttributes.reserved = 0;
    cfg->bMaxPower = 0;

    usbctrl_configuration_desc_to_buff(cfg, (uint8_t*)&(buf[*curr_offset]));

    *curr_offset += sizeof(usbctrl_configuration_descriptor_t);
    /*@ assert *curr_offset == \at(*curr_offset,Pre) + sizeof(usbctrl_configuration_descriptor_t) ; */

err:
    return errcode;
}

/*@
  @ requires \separated(&SIZE_DESC_FIXED, &FLAG, composite, buf+(0 .. MAX_DESCRIPTOR_LEN-1),curr_offset, ctx + (..));
  @ requires \valid(composite);
  @ requires iface_id < ctx->cfg[ctx->curr_cfg].interface_num;
  @ requires \valid(buf + (0 .. MAX_DESCRIPTOR_LEN-1));
  @ assigns *composite;
  @ assigns buf[0 .. MAX_DESCRIPTOR_LEN-1 ];
  @ assigns *curr_offset;

  @ behavior INVPARAM:
  @   assumes (curr_offset == \null || buf == \null || ctx == \null) ;
  @   ensures *composite == \old(*composite);
  @   ensures \result == MBED_ERROR_INVPARAM ;

  @ behavior notcomposite:
  @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
  @   assumes (ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function == \false);
  @   assigns *composite;
  @   ensures \result == MBED_ERROR_NONE ;
  @   ensures *composite == \false;

  @ behavior alreadycomposite:
  @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
  @   assumes (ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function == \true);
  @   assumes (*composite == \true);
  @   assumes (composite_id == ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function_id) ;
  @   ensures \result == MBED_ERROR_NONE ;

  @ behavior newcomposite_NOSTORAGE:
  @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
  @   assumes (ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function == \true);
  @   assumes (*composite == \false);
  @   assumes (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_endpoint_descriptor_t))) ;
  @   ensures *composite == \old(*composite);
  @   ensures \result == MBED_ERROR_NOSTORAGE ;

  @ behavior newcomposite_OK:
  @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
  @   assumes (ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function == \true);
  @   assumes (*composite == \false);
  @   assumes (*curr_offset <= (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_endpoint_descriptor_t))) ;
  @   ensures \result == MBED_ERROR_NONE ;

  @ behavior curcomposite_NOSTORAGE:
  @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
  @   assumes (ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function == \true);
  @   assumes (*composite == \true);
  @   assumes (composite_id != ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function_id) ;
  @   assumes (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_endpoint_descriptor_t))) ;
  @   ensures \result == MBED_ERROR_NOSTORAGE ;

  @ behavior curcomposite_OK:
  @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
  @   assumes (ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function == \true);
  @   assumes (*composite == \true);
  @   assumes (composite_id != ctx->cfg[ctx->curr_cfg].interfaces[iface_id].composite_function_id) ;
  @   assumes (*curr_offset <= (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_endpoint_descriptor_t))) ;
  @   ensures \result == MBED_ERROR_NONE ;

  @ complete behaviors ;
  @ disjoint behaviors ;
*/


#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_configuration_write_iad_desc(uint8_t *buf,
                                                         usbctrl_context_t const * const ctx,
                                                         bool *composite,
                                                         uint8_t composite_id,
                                                         uint8_t iface_id,
                                                         uint32_t * curr_offset)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t curr_cfg = ctx->curr_cfg;

    if (curr_offset == NULL || buf == NULL || ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    /* current iface is a part of a composite function  */
    if (ctx->cfg[curr_cfg].interfaces[iface_id].composite_function == true) {
        /* the composite function associated to current iface already has its header... */
        if (*composite == true && composite_id == ctx->cfg[curr_cfg].interfaces[iface_id].composite_function_id) {
            goto err;
        }
        /* overflow check */
        if (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_iad_descriptor_t))) {
            errcode = MBED_ERROR_NOSTORAGE;
            goto err;
        }

        /* new function: new IAD */
        /* composite ifaces start with 0 */
        /*@ assert *curr_offset < (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_iad_descriptor_t));*/
        usbctrl_iad_descriptor_t *cfg = (usbctrl_iad_descriptor_t*)&(buf[*curr_offset]);
        cfg->bLength = sizeof(usbctrl_iad_descriptor_t);
        cfg->bDescriptorType = USB_DESC_IAD;
        cfg->bFirstInterface = iface_id;
        /* specify number of interfaces of this composite function */
        cfg->bInterfaceCount = 0;
        uint8_t count = 0;
        /*@
          @ loop invariant iface_id <= i <= ctx->cfg[curr_cfg].interface_num;
          @ loop assigns i, count;
          @ loop variant ctx->cfg[curr_cfg].interface_num - i;
          */
        for (uint8_t i = iface_id; i < ctx->cfg[curr_cfg].interface_num; ++i) {
            if (ctx->cfg[curr_cfg].interfaces[i].composite_function && ctx->cfg[curr_cfg].interfaces[i].composite_function_id == composite_id) {
                count++;
            }
        }
        cfg->bInterfaceCount = count;
        /* composite parent class, subclass and protocol is the one of the master interface of the composite device */
        cfg->bFunctionClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_class;
        cfg->bFunctionSubClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_subclass;
        cfg->bFunctionProtocol = ctx->cfg[curr_cfg].interfaces[iface_id].usb_protocol;
        cfg->iFunction = 0x04;
        *curr_offset += sizeof(usbctrl_iad_descriptor_t);
        /*@ assert *curr_offset == \at(*curr_offset,Pre) + sizeof(usbctrl_iad_descriptor_t) ; */
    } else {
        /* current iface is not composite ? */
        *composite = false;
    }
err:
    return errcode;
}

/*@
    @ requires \valid(cfg) && \valid_read(buf + (0 .. sizeof(usbctrl_interface_descriptor_t)-1)) ;
    @ assigns *cfg ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_interface_desc_from_buff(__out usbctrl_interface_descriptor_t *cfg, __in const uint8_t *buf)
{
    cfg->bLength             = buf[0];
    cfg->bDescriptorType     = buf[1];
    cfg->bInterfaceNumber    = buf[2];
    cfg->bAlternateSetting   = buf[3];
    cfg->bNumEndpoints       = buf[4];
    cfg->bInterfaceClass     = buf[5];
    cfg->bInterfaceSubClass  = buf[6];
    cfg->bInterfaceProtocol  = buf[7];
    cfg->iInterface          = buf[8];

    return;
}


/*@
    @ requires \valid_read(cfg) && \valid(buf + (0 .. sizeof(usbctrl_interface_descriptor_t)-1)) ;
    @ assigns buf[0 .. sizeof(usbctrl_interface_descriptor_t)-1] ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_interface_desc_to_buff(__in const usbctrl_interface_descriptor_t *cfg, __out uint8_t *buf)
{
    buf[0] = cfg->bLength;
    buf[1] = cfg->bDescriptorType;
    buf[2] = cfg->bInterfaceNumber;
    buf[3] = cfg->bAlternateSetting;
    buf[4] = cfg->bNumEndpoints;
    buf[5] = cfg->bInterfaceClass;  
    buf[6] = cfg->bInterfaceSubClass;
    buf[7] = cfg->bInterfaceProtocol;
    buf[8] = cfg->iInterface;

    return;
}



/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),curr_offset, ctx + (..));
    @ assigns buf[0 .. MAX_DESCRIPTOR_LEN-1 ];
    @ assigns *curr_offset;

    @ behavior INVPARAM:
    @   assumes (curr_offset == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   ensures *curr_offset == \old(*curr_offset);

    @ behavior NOSTORAGE:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes (*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   ensures \result == MBED_ERROR_NOSTORAGE ;
    @   ensures *curr_offset == \old(*curr_offset);

    @ behavior bad_iface:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes !(*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   assumes iface_id >= MAX_INTERFACES_PER_DEVICE ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   ensures *curr_offset == \old(*curr_offset);

    @ behavior OK:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes !(*curr_offset > (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_configuration_descriptor_t))) ;
    @   assumes iface_id < MAX_INTERFACES_PER_DEVICE ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   ensures *curr_offset == \old(*curr_offset) + sizeof(usbctrl_interface_descriptor_t) ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
  CDE : not possible to validate assigns clause for behavior OK because of cast : (usbctrl_interface_descriptor_t*)&(buf[*curr_offset]) (WP memory model)
  RBE : fix attempt
*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_configuration_write_iface_desc(uint8_t *buf,
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

    //if (iface_id == 255) {  // cyril : rte here, if iface_id >= MAX_INTERFACES_PER_DEVICE
    if (iface_id >= MAX_INTERFACES_PER_DEVICE) {
        /* DEFENSIVE PROGRAMMING:
         * the expected number of interfaces is limited to a small number, thus, to avoid an u8
         * overflow below, we check its value here */
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* pointing to next field: interface descriptor */
    //usbctrl_interface_descriptor_t *cfg = (usbctrl_interface_descriptor_t*)&(buf[*curr_offset]);
    usbctrl_interface_descriptor_t _cfg;
    usbctrl_interface_descriptor_t *cfg = &_cfg;
    usbctrl_interface_desc_from_buff(cfg, (uint8_t*)&(buf[*curr_offset]));

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
    cfg->bInterfaceClass = (uint8_t)ctx->cfg[curr_cfg].interfaces[iface_id].usb_class;
    cfg->bInterfaceSubClass = ctx->cfg[curr_cfg].interfaces[iface_id].usb_subclass;
    cfg->bInterfaceProtocol = ctx->cfg[curr_cfg].interfaces[iface_id].usb_protocol;
    cfg->iInterface = iface_id;

    usbctrl_interface_desc_to_buff(cfg, (uint8_t*)&(buf[*curr_offset]));

    *curr_offset += sizeof(usbctrl_interface_descriptor_t);
    /*@ assert *curr_offset == \at(*curr_offset,Pre) + sizeof(usbctrl_interface_descriptor_t) ; */

err:
    return errcode;
}

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(..),curr_offset, ctx + (..));
    @ assigns buf[0 .. MAX_DESCRIPTOR_LEN-1 ];
    @ assigns *curr_offset, FLAG;

    @ behavior INVPARAM:
    @   assumes (curr_offset == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   ensures *curr_offset == \old(*curr_offset);
    @   ensures FLAG == \old(FLAG);

    @ behavior bad_iface:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes iface_id == 255 ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   ensures *curr_offset == \old(*curr_offset);
    @   ensures FLAG == \old(FLAG);

    @ behavior OTHER:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes iface_id != 255 ;
    @   ensures \result == MBED_ERROR_NONE ||
                (\result == MBED_ERROR_NOBACKEND && (*curr_offset == \old(*curr_offset))) ||
                (\result == MBED_ERROR_INVPARAM && (*curr_offset == \old(*curr_offset))) ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
  TODO : be more precise with OTHER behavior (pb is with get_handler errcode and class_desc_handler errcode : not possible to try errcode != MBED_ERROR_NONE )
*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_configuration_write_class_desc(usbctrl_context_t * ctx,
                                                           uint8_t  * buf,
                                                           uint8_t    iface_id,
                                                           uint32_t * curr_offset)
{

    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t curr_cfg = ctx->curr_cfg;
    uint32_t handler;
    uint32_t max_buf_size = 0;
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
    @ requires \valid(cfg) && \valid_read(buf + (0 .. sizeof(usbctrl_endpoint_descriptor_t)-1)) ;
    @ assigns *cfg ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_ep_desc_from_buff(__out usbctrl_endpoint_descriptor_t *cfg, __in const uint8_t *buf)
{
    cfg->bLength          = buf[0];
    cfg->bDescriptorType  = buf[1];
    cfg->bEndpointAddress = buf[2];
    cfg->bmAttributes     = buf[3];
    cfg->wMaxPacketSize   = ((uint16_t)buf[5] << 8) | buf[4];
    cfg->bInterval        = buf[6];

    return;
}


/*@
    @ requires \valid_read(cfg) && \valid(buf + (0 .. sizeof(usbctrl_endpoint_descriptor_t)-1)) ;
    @ assigns buf[0 .. sizeof(usbctrl_endpoint_descriptor_t)-1] ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_ep_desc_to_buff(__in const usbctrl_endpoint_descriptor_t *cfg, __out uint8_t *buf)
{
    buf[0] = cfg->bLength;
    buf[1] = cfg->bDescriptorType;
    buf[2] = cfg->bEndpointAddress;
    buf[3] = cfg->bmAttributes;
    buf[4] = (uint8_t)(cfg->wMaxPacketSize & 0xff);
    buf[5] = (uint8_t)(cfg->wMaxPacketSize >> 8) & 0xff;
    buf[6] = cfg->bInterval;

    return;
}

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(0 .. MAX_DESCRIPTOR_LEN-1),curr_offset, ctx + (..));
    @ requires iface_id < ctx->cfg[ctx->curr_cfg].interface_num;
    @ requires \valid(buf + (0 .. MAX_DESCRIPTOR_LEN-1));

    @ behavior INVPARAM:
    @   assumes (curr_offset == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing;

    @ behavior NOSTORAGE:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes (*curr_offset >= (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_endpoint_descriptor_t))) ;
    @   ensures \result == MBED_ERROR_NOSTORAGE ;
    @   assigns \nothing;

    @ behavior OK:
    @   assumes !(curr_offset == \null || buf == \null || ctx == \null) ;
    @   assumes !(*curr_offset >= (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_endpoint_descriptor_t))) ;
    @   ensures \result == MBED_ERROR_NONE ;
    @   assigns buf[0 .. MAX_DESCRIPTOR_LEN-1 ];
    @   assigns *curr_offset;
    @   ensures *curr_offset == \old(*curr_offset) + sizeof(usbctrl_endpoint_descriptor_t) ;

    @ complete behaviors ;
    @ disjoint behaviors ;
*/

/*
  CDE : not possible to validate assigns clause because of cast : (usbctrl_endpoint_descriptor_t*)&(buf[*curr_offset]) (WP memory model)
  RBE : fix attempt
*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_configuration_write_ep_desc(usbctrl_context_t const * const ctx,
                                                        uint8_t  * buf,
                                                        uint8_t    ep_number,
                                                        usb_ep_dir_t ep_dir,
                                                        uint8_t    iface_id,
                                                        uint8_t    curr_cfg,
                                                        uint32_t * curr_offset)
{

    mbed_error_t errcode = MBED_ERROR_NONE;

    uint8_t poll = 0;

    if (buf == NULL || curr_offset == NULL || ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (*curr_offset >= (MAX_DESCRIPTOR_LEN - sizeof(usbctrl_endpoint_descriptor_t))) {
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }

    //usbctrl_endpoint_descriptor_t *cfg = (usbctrl_endpoint_descriptor_t*)&(buf[*curr_offset]);
    usbctrl_endpoint_descriptor_t _cfg;
    usbctrl_endpoint_descriptor_t *cfg = &_cfg;
    usbctrl_ep_desc_from_buff(cfg, (uint8_t*)&(buf[*curr_offset]));
    
    
    cfg->bLength = sizeof(usbctrl_endpoint_descriptor_t);
    cfg->bDescriptorType = USB_DESC_ENDPOINT;
    cfg->bEndpointAddress = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].ep_num;
    if (ep_dir == USB_EP_DIR_IN) {
        cfg->bEndpointAddress |= 0x80; /* set bit 7 to 1 for IN EPs */
    }
    cfg->bmAttributes = (uint8_t)
        (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].type       |
         ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].attr << 2  |
         ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].usage << 4);
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
            poll = i;
        } else {
            /* in Fullspeed, the bInterval field is directly set in ms, between 1 and 255 */
        }
    } else {
        /* for BULK EP, we set bInterval to 0 */
        poll = 0;
    }
    cfg->bInterval = poll;

    usbctrl_ep_desc_to_buff(cfg, (uint8_t*)&(buf[*curr_offset]));

    *curr_offset += sizeof(usbctrl_endpoint_descriptor_t);
    /*@ assert *curr_offset == \at(*curr_offset,Pre) + sizeof(usbctrl_endpoint_descriptor_t) ; */

err:
    return errcode;
}



/*********************************************************************************
 * device descriptor handling fonction
 */

/*@
    @ requires \valid(cfg) && \valid_read(buf + (0 .. sizeof(usbctrl_device_descriptor_t)-1)) ;
    @ assigns *cfg ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_device_desc_from_buff(__out usbctrl_device_descriptor_t *cfg, __in const uint8_t *buf)
{
    cfg->bLength             = buf[0];
    cfg->bDescriptorType     = buf[1];
    cfg->bcdUSB              = ((uint16_t)buf[3] << 8) | buf[2];
    cfg->bDeviceClass        = buf[4];
    cfg->bDeviceSubClass     = buf[5];
    cfg->bDeviceProtocol     = buf[6];
    cfg->bMaxPacketSize      = buf[7];
    cfg->idVendor            = ((uint16_t)buf[9] << 8) | buf[8];
    cfg->idProduct           = ((uint16_t)buf[11] << 8) | buf[10]; 
    cfg->bcdDevice           = ((uint16_t)buf[13] << 8) | buf[12];
    cfg->iManufacturer       = buf[14];
    cfg->iProduct            = buf[15];
    cfg->iSerialNumber       = buf[16];
    cfg->bNumConfigurations  = buf[17];    

    return;
}


/*@
    @ requires \valid_read(cfg) && \valid(buf + (0 .. sizeof(usbctrl_device_descriptor_t)-1)) ;
    @ assigns buf[0 .. sizeof(usbctrl_device_descriptor_t)-1] ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_device_desc_to_buff(__in const usbctrl_device_descriptor_t *cfg, __out uint8_t *buf)
{
    buf[0]  = cfg->bLength;
    buf[1]  = cfg->bDescriptorType;
    buf[2]  = (uint8_t)(cfg->bcdUSB & 0xff);
    buf[3]  = (uint8_t)(cfg->bcdUSB >> 8) & 0xff;
    buf[4]  = cfg->bDeviceClass;
    buf[5]  = cfg->bDeviceSubClass;
    buf[6]  = cfg->bDeviceProtocol;
    buf[7]  = cfg->bMaxPacketSize;
    buf[8]  = (uint8_t)(cfg->idVendor & 0xff);
    buf[9]  = (uint8_t)(cfg->idVendor >> 8) & 0xff;
    buf[10] = (uint8_t)(cfg->idProduct & 0xff);
    buf[11] = (uint8_t)(cfg->idProduct >> 8) & 0xff;
    buf[12] = (uint8_t)(cfg->bcdDevice & 0xff);
    buf[13] = (uint8_t)(cfg->bcdDevice >> 8) & 0xff;
    buf[14] = cfg->iManufacturer;
    buf[15] = cfg->iProduct;
    buf[16] = cfg->iSerialNumber;
    buf[17] = cfg->bNumConfigurations;
    
    return;
}



/*
 * It is considered here that the buffer is large enough to hold the
 * requested descriptor. The buffer size is under the control of the
 * get_descriptor standard request handler
 */

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(0 .. MAX_DESCRIPTOR_LEN-1),desc_size,ctx+(..));
    @ requires \valid(buf + (0 .. MAX_DESCRIPTOR_LEN-1));
    @ assigns buf[0 .. MAX_DESCRIPTOR_LEN-1];
    @ assigns *desc_size;

    @ behavior INVPARAM:
    @   assumes (desc_size == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing;

    @ behavior ok:
    @   assumes !(desc_size == \null || buf == \null || ctx == \null) ;
    @   ensures \result == MBED_ERROR_NONE;

    @ disjoint behaviors;
    @ complete behaviors;

*/

/*
  CDE : not possible to validate assigns clause because of cast : (usbctrl_device_descriptor_t*)buf (WP memory model)
*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_device_desc(uint8_t                   *buf,
                                        uint32_t                  *desc_size,
                                        usbctrl_context_t const   * const ctx)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    if (buf == NULL || desc_size == NULL || ctx == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert \valid(buf + (0 .. MAX_DESCRIPTOR_LEN-1)); */
    /*@ assert \valid(desc_size); */
    /*@ assert \valid_read(ctx); */

    /*@ assert sizeof(usbctrl_device_descriptor_t) < MAX_DESCRIPTOR_LEN; */

    log_printf("[USBCTRL] request device desc (num cfg: %d)\n", ctx->num_cfg);
    /*@ assert MAX_DESCRIPTOR_LEN > sizeof(usbctrl_device_descriptor_t); */
    //usbctrl_device_descriptor_t *desc = (usbctrl_device_descriptor_t*)&(buf[0]);
    usbctrl_device_descriptor_t _desc;
    usbctrl_device_descriptor_t *desc = &_desc;
    usbctrl_device_desc_from_buff(desc, buf);

    desc->bLength = sizeof(usbctrl_device_descriptor_t);
    desc->bDescriptorType = 0x1; /* USB Desc Device */
    desc->bcdUSB = 0x0200; /* USB 2.0 */
    desc->bDeviceClass = 0; /* replaced by default iface */
    desc->bDeviceSubClass = 0;
    desc->bDeviceProtocol = 0;
    desc->bMaxPacketSize = 64; /* on EP0. TODO: requests MPsize from driver, depends on speed negociation,
                                  HS & FS supports 64, but FS allows smaller mpsize. */
    desc->idVendor = CONFIG_USR_LIB_USBCTRL_DEV_VENDORID;
    desc->idProduct = CONFIG_USR_LIB_USBCTRL_DEV_PRODUCTID;
    desc->bcdDevice = 0x000;
    desc->iManufacturer = CONFIG_USB_DEV_MANUFACTURER_INDEX;
    desc->iProduct = CONFIG_USB_DEV_PRODNAME_INDEX;
    desc->iSerialNumber = CONFIG_USB_DEV_SERIAL_INDEX;
    desc->bNumConfigurations = ctx->num_cfg;

    *desc_size = sizeof(usbctrl_device_descriptor_t);
    
    usbctrl_device_desc_to_buff(desc, buf);

err:
    return errcode;
}

/*@
    @ requires \valid(cfg) && \valid_read(buf + (0 .. sizeof(usbctrl_string_descriptor_t)-1)) ;
    @ assigns *cfg ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_string_desc_from_buff(__out usbctrl_string_descriptor_t *cfg, __in const uint8_t *buf)
{
    cfg->bLength          = buf[0];
    cfg->bDescriptorType  = buf[1];
    /*@
      @ loop invariant 0 <= i <= MAX_DESC_STRING_SIZE ;
      @ loop assigns i, cfg->wString[0 .. (MAX_DESC_STRING_SIZE-1)] ;
      @ loop variant MAX_DESC_STRING_SIZE - i ;
     */
    for(uint32_t i = 0; i < MAX_DESC_STRING_SIZE; i++){
        cfg->wString[i] =  ((uint16_t)buf[2 + i + 1] << 8) | buf[2 + i];
    }
    return;
}


/*@
    @ requires \valid_read(cfg) && \valid(buf + (0 .. sizeof(usbctrl_string_descriptor_t)-1)) ;
    @ assigns buf[0 .. sizeof(usbctrl_string_descriptor_t)-1] ;
 */
#ifndef __FRAMAC__
static inline
#endif
void usbctrl_string_desc_to_buff(__in const usbctrl_string_descriptor_t *cfg, __out uint8_t *buf)
{
    buf[0] = cfg->bLength;
    buf[1] = cfg->bDescriptorType;
    /*@
      @ loop invariant 0 <= i <= MAX_DESC_STRING_SIZE ;
      @ loop assigns i, buf[2 .. (2 + (2*(MAX_DESC_STRING_SIZE-1)))] ;
      @ loop variant MAX_DESC_STRING_SIZE - i ;
     */
    for(uint32_t i = 0; i < MAX_DESC_STRING_SIZE; i++){
        buf[2 + i]   = (uint8_t)(cfg->wString[i] & 0xff);
        buf[2 + i + 1] = (uint8_t)(cfg->wString[i] >> 8) & 0xff;
    }

    return;
}



/*********************************************************************************
 * string descriptor handling fonction
 */

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(0 .. MAX_DESCRIPTOR_LEN-1),desc_size+(..),pkt+(..));
//    @ ensures (\result == MBED_ERROR_UNSUPORTED_CMD &&  *desc_size == 0) ||
//         (\result == MBED_ERROR_NONE && (*desc_size == 4 || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_MANUFACTURER))
//                                    || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_PRODNAME)) || *desc_size == (2 + 2 * sizeof(CONFIG_USB_DEV_SERIAL) ))) ;

    @ behavior INVPARAM:
    @   assumes (desc_size == \null || buf == \null || pkt == \null) ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   assigns \nothing;

    @ behavior INVCMD:
    @ assumes !(desc_size == \null || buf == \null || pkt == \null) ;
    @ assumes (((pkt->wValue & 0xff) != (uint16_t)0x0) &&
               ((pkt->wValue & 0xff) != (uint16_t)CONFIG_USB_DEV_MANUFACTURER_INDEX) &&
               ((pkt->wValue & 0xff) != (uint16_t)CONFIG_USB_DEV_PRODNAME_INDEX) &&
               ((pkt->wValue & 0xff) != (uint16_t)CONFIG_USB_DEV_SERIAL_INDEX));
    @ ensures \result == MBED_ERROR_UNSUPORTED_CMD;
    @ assigns \nothing;

    @ behavior ok:
    @   assumes !(desc_size == \null || buf == \null || pkt == \null) ;
    @   assumes !(((pkt->wValue & 0xff) != (uint16_t)0x0) &&
                ((pkt->wValue & 0xff) != (uint16_t)CONFIG_USB_DEV_MANUFACTURER_INDEX) &&
                ((pkt->wValue & 0xff) != (uint16_t)CONFIG_USB_DEV_PRODNAME_INDEX) &&
                ((pkt->wValue & 0xff) != (uint16_t)CONFIG_USB_DEV_SERIAL_INDEX));
    @   ensures \result == MBED_ERROR_NONE;
    @   assigns buf[0 .. sizeof(usbctrl_string_descriptor_t)-1], *desc_size;

    @ complete behaviors;
    @ disjoint behaviors;

*/

/*
  TODO : be more precise with (pkt->wValue & 0xff) behavior
  not possible to validate assigns clause because of cast : (usbctrl_string_descriptor_t *)&(string_desc[0]) (WP memory model)
*/

#ifndef __FRAMAC__
static
#endif
mbed_error_t usbctrl_handle_string_desc(__out uint8_t    *buf,
                                        __out uint32_t              *desc_size,
                                        __in  usbctrl_setup_pkt_t  const  * const pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (buf == NULL || desc_size == NULL || pkt == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert \valid(buf + (0 .. MAX_DESCRIPTOR_LEN-1)); */
    /*@ assert \valid(desc_size); */
    /*@ assert \valid_read(pkt); */

    /*@ assert sizeof(usbctrl_string_descriptor_t) < MAX_DESCRIPTOR_LEN; */
    const char *USB_DEV_MANUFACTURER = CONFIG_USB_DEV_MANUFACTURER;
    const char *USB_DEV_PRODNAME = CONFIG_USB_DEV_PRODNAME;
    const char *USB_DEV_SERIAL = CONFIG_USB_DEV_SERIAL;
    uint8_t string_type = pkt->wValue & 0xff;

    log_printf("[USBCTRL] create string desc of size %d\n", descriptor_size);
    //usbctrl_string_descriptor_t *cfg = (usbctrl_string_descriptor_t *)&(buf[0]);
    usbctrl_string_descriptor_t _cfg;
    usbctrl_string_descriptor_t *cfg = &_cfg;
    usbctrl_string_desc_from_buff(cfg, buf);

    uint32_t maxlen = 0;
    /* INFO:  UTF16 double each size */

    switch (string_type) {
        case 0:
            cfg->bDescriptorType = USB_DESC_STRING;
            cfg->bLength = 4;
            cfg->wString[0] = LANGUAGE_ENGLISH;
            *desc_size = 4;
            break;

        case CONFIG_USB_DEV_MANUFACTURER_INDEX:
            maxlen = (sizeof(CONFIG_USB_DEV_MANUFACTURER) > 32 ? 32 : sizeof(CONFIG_USB_DEV_MANUFACTURER));
            cfg->bDescriptorType = USB_DESC_STRING;
            cfg->bLength = 2 + 2 * maxlen;

            /*@
              @ loop invariant 0 <= i <= maxlen ;
              @ loop assigns i, *cfg ;
              @ loop variant maxlen - i ;
              */
            for (uint32_t i = 0; i < maxlen; ++i) {
                cfg->wString[i] = USB_DEV_MANUFACTURER[i];
            }
            *desc_size = 2 + 2 * maxlen;
            goto err;
            break;

        case CONFIG_USB_DEV_PRODNAME_INDEX:
            maxlen = (sizeof(CONFIG_USB_DEV_PRODNAME) > 32 ? 32 : sizeof(CONFIG_USB_DEV_PRODNAME));
            cfg->bDescriptorType = USB_DESC_STRING;
            cfg->bLength = 2 + 2 * maxlen;

            /*@
              @ loop invariant 0 <= i <= maxlen ;
              @ loop assigns i, *cfg ;
              @ loop variant maxlen - i ;
              */
            for (uint32_t i = 0; i < maxlen; ++i) {
                cfg->wString[i] = USB_DEV_PRODNAME[i];
            }
            *desc_size = 2 + 2 * maxlen;
            goto err;
            break;

        case CONFIG_USB_DEV_SERIAL_INDEX:
            maxlen = (sizeof(CONFIG_USB_DEV_SERIAL) > 32 ? 32 : sizeof(CONFIG_USB_DEV_SERIAL));
            cfg->bDescriptorType = USB_DESC_STRING;
            cfg->bLength = 2 + 2 * maxlen;

            /*@
              @ loop invariant 0 <= i <= maxlen ;
              @ loop assigns i, *cfg ;
              @ loop variant maxlen - i ;
              */
            for (uint32_t i = 0; i < maxlen; ++i) {
                cfg->wString[i] = USB_DEV_SERIAL[i];
            }
            *desc_size = 2 + 2 * maxlen;
            goto err;
            break;

        default:
            log_printf("[USBCTRL] Unsupported string index requested.\n");
            errcode = MBED_ERROR_UNSUPORTED_CMD;
            goto err;
            break;
    }
    usbctrl_string_desc_to_buff(cfg, buf);
err:
    return errcode;
}


/*********************************************************************************
 * head function, handling all descriptor types.
 * This is the only function exported.
 */

/*@
    @ requires \separated(&SIZE_DESC_FIXED, &FLAG, buf+(0 .. MAX_DESCRIPTOR_LEN-1),desc_size+(..),ctx+(..),pkt+(..));
    @ assigns ctx->curr_cfg;
    @ assigns buf[0 .. MAX_DESCRIPTOR_LEN-1];
    @ assigns *desc_size;
    @ assigns SIZE_DESC_FIXED, FLAG;

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
            uint8_t iface_id = (pkt->wValue & 0xff);
            errcode = usbctrl_handle_configuration_write_iface_desc(buf, ctx, iface_id, desc_size);
            break;
        case USB_DESC_ENDPOINT:
            log_printf("[USBCTRL] request EP desc\n");
            uint8_t curr_cfg = ctx->curr_cfg;
            uint8_t iface_num = ctx->cfg[curr_cfg].interface_num;
            uint8_t max_ep_number;  // new variable for variant and invariant proof
            uint8_t target_ep = (pkt->wValue & 0xff);

            for (uint8_t iface_id = 0; iface_id < iface_num; ++iface_id) {

                /*
                 * FRAMAC todo
                 */
                max_ep_number = ctx->cfg[curr_cfg].interfaces[iface_id].usb_ep_number ;  // variable change in loop
                for (uint8_t ep_number = 0; ep_number < max_ep_number; ++ep_number) {
                    if (ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].ep_num == target_ep) {
                        uint8_t ep_dir = ctx->cfg[curr_cfg].interfaces[iface_id].eps[ep_number].dir;
                        errcode = usbctrl_handle_configuration_write_ep_desc(ctx, buf, target_ep, ep_dir, iface_id, curr_cfg, desc_size);
                    }
                }
            }
            break;
        case USB_DESC_STRING: {
            log_printf("[USBCTRL] request string desc\n");
            errcode = usbctrl_handle_string_desc(buf, desc_size, pkt);
            break;
        }
        case USB_DESC_CONFIGURATION: {
            log_printf("[USBCTRL] request configuration desc\n");
            /* configuration descriptor is dynamic, depends on current config and its number of endpoints... */
            /* 1) calculating desc size */
            //uint8_t requested_configuration = pkt->wValue; /* TODO to be used */

            /* is there, at upper layer, an additional class descriptor for
             * current configuration ? if yes, we get back this descriptor
             * and add it to the complete configuration descriptor we send
             * to the host. */
            /* Here, we only calculate, for each interface, if there is a
             * class descriptor, its size. The effective descriptor will
             * be stored later, when the overall configuration descriptor
             * is forged. */
            uint32_t descriptor_size = 0;
            /* desriptor index is set in WValue low byte. Its value is between 1 and num_cfg */
            uint8_t curr_cfg = pkt->wValue & 0xff;
            if (curr_cfg >= ctx->num_cfg) {
                log_printf("[USBCTRL] invalid descriptor id received !\n");
                goto err;
            }
            /* setting current_cfg to requested cfg in get_descriptor */
            ctx->curr_cfg = curr_cfg;

            errcode = usbctrl_handle_configuration_size(buf, desc_size, ctx, &descriptor_size);
            if (errcode != MBED_ERROR_NONE) {
                log_printf("[USBCTRL] failure while calculating total desc size\n");
                goto err;
            }
            /*@ assert descriptor_size < MAX_DESCRIPTOR_LEN; */

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
             */
            uint32_t curr_offset = 0;
            uint8_t iface_num = ctx->cfg[curr_cfg].interface_num;

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

            bool composite = false;
            uint8_t composite_id = 0;
            // XXX: see iad descriptor function comment
            // uint8_t effective_iface_id = 0;
            for (uint8_t iface_id = 0; iface_id < iface_num; ++iface_id) {
                /*
                 * for each interface, we first need to add the interface descriptor
                 */
                // COMPOSITE IAD header
                errcode = usbctrl_handle_configuration_write_iad_desc(buf, ctx, &composite, composite_id, iface_id, &curr_offset);
                if (errcode != MBED_ERROR_NONE) {
                    /* by now, this should be dead code as the above function should  never fails*/
                    goto err;
                }
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
                errcode = MBED_ERROR_UNKNOWN;
                goto err;
            }
            /*@ assert descriptor_size == curr_offset ; */
            *desc_size = descriptor_size;
            //@ merge SIZE_DESC_FIXED ;
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
