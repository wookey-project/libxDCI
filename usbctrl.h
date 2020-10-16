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
#ifndef USBCTRL_H_
#define USBCTRL_H_

#include "libc/types.h"
#include "libc/stdio.h"
#include "api/libusbctrl.h"

#ifndef __FRAMAC__
#include "libc/sanhandlers.h"

/*
 * Here, we handle the case of differenciated FW/DFU mode.
 * Is set (and only if set) we redefine unified macro value from the currently being
 * compiled mode. If not, nothing is to be done here.
 */
#if defined(CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD)
/* in that case, unified DEBUG, MAX_CFG and MAX_CTX are not defined, let's define them
 * here. To differenciate DFU from FW mode, -DMODE_DFU is passed for DFU profile
 * compilation units */
# if defined(MODE_DFU)


#  define CONFIG_USBCTRL_MAX_CFG                CONFIG_USBCTRL_DFU_MAX_CFG
#  define CONFIG_USBCTRL_MAX_CTX                CONFIG_USBCTRL_DFU_MAX_CTX
#  define CONFIG_USR_LIB_USBCTRL_DEBUG          CONFIG_USR_LIB_USBCTRL_DFU_DEBUG
#  define CONFIG_USR_LIB_USBCTRL_DEV_PRODUCTID  CONFIG_USR_LIB_USBCTRL_DFU_DEV_PRODUCTID
# else
#  define CONFIG_USBCTRL_MAX_CFG                CONFIG_USBCTRL_FW_MAX_CFG
#  define CONFIG_USBCTRL_MAX_CTX                CONFIG_USBCTRL_FW_MAX_CTX
#  define CONFIG_USR_LIB_USBCTRL_DEBUG          CONFIG_USR_LIB_USBCTRL_FW_DEBUG
#  define CONFIG_USR_LIB_USBCTRL_DEV_PRODUCTID  CONFIG_USR_LIB_USBCTRL_FW_DEV_PRODUCTID
# endif

#else
# define CONFIG_USR_LIB_USBCTRL_DEV_PRODUCTID  CONFIG_USR_LIB_USBCTRL_DFU_DEV_PRODUCTID
#endif

#endif


/*********************************************************
 * General tooling
 */

#if CONFIG_USR_LIB_USBCTRL_DEBUG
# define log_printf(...) printf(__VA_ARGS__)
#else
# define log_printf(...)
#endif

/************************************************
 * about libctrl context
 ***********************************************/

#ifndef __FRAMAC__

#define MAX_INTERFACES_PER_DEVICE 4

typedef struct {
    uint8_t                first_free_epid;   /* first free EP identifier (starting with 1, as 0 is control) */
    uint8_t                interface_num;     /*< Number of interfaces registered */
    usbctrl_interface_t    interfaces[MAX_INTERFACES_PER_DEVICE];     /*< For each registered interface */
} usbctrl_configuration_t;


typedef enum {
   USB_CTRL_RCV_FIFO_SATE_NOSTORAGE, /*< No receive FIFO set yet */
   USB_CTRL_RCV_FIFO_SATE_FREE,  /*< Receive FIFO is free (no active content in it) */
   USB_CTRL_RCV_FIFO_SATE_BUSY,  /*< Receive FIFO is locked. A provider is writing
                                     data in it (DMA, trigger...) */
   USB_CTRL_RCV_FIFO_SATE_READY  /*< Receive FIFO is ready. There is content to get from
                                     it, no provider is accessing it */
} ctrl_plane_rx_fifo_state_t;


typedef struct usbctrl_context {
    /* first, about device driver interactions */
    uint32_t               dev_id;              /*< device id, from the USB device driver */
    uint16_t               address;             /*< device address, to be set by std req */
    /* then current context state, associated to the USB standard state automaton  */
    uint8_t                 num_cfg;        /*< number of different onfigurations */
    uint8_t                 curr_cfg;       /*< current configuration */
    usbctrl_configuration_t cfg[CONFIG_USBCTRL_MAX_CFG]; /* configurations list */
    uint8_t                 state;          /*< USB state machine current state */
    uint8_t                 ctrl_fifo[CONFIG_USBCTRL_EP0_FIFO_SIZE]; /* RECV FIFO for EP0 */
    ctrl_plane_rx_fifo_state_t ctrl_fifo_state; /*< RECV FIFO of control plane state */
    bool           ctrl_req_processing; /* a control level request is being processed */
} usbctrl_context_t;


#endif


#if defined(__FRAMAC__)

/*@
    @ requires \valid(packet);
    @ assigns \nothing ;
    @ ensures is_valid_error(\result);
*/

mbed_error_t class_rqst_handler(uint32_t usbxdci_handler,
                                       usbctrl_setup_pkt_t *packet);

/*@
    @ assigns \nothing ;
    @ ensures is_valid_error(\result);
*/
mbed_error_t handler_ep(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    return errcode;
}

void test_fcn_driver_eva(void) ;



/*@
    @ assigns reset_requested ;
    @ ensures reset_requested == true ;
*/

void usbctrl_reset_received(void){
    reset_requested = true;
}


/*@
    @ requires \separated(buf,desc_size,&ctx_list, &FLAG,&SIZE_DESC_FIXED);
    @ assigns *desc_size ;
    @ ensures (buf == \null || desc_size == \null) ==> \result == MBED_ERROR_INVPARAM ;
    @ ensures (!(buf == \null || desc_size == \null) && FLAG == \false)
             ==> (\result == MBED_ERROR_NONE && 0 <= *desc_size <=  255) ;
    @ ensures (!(buf == \null || desc_size == \null) && FLAG == \true)
             ==> (\result == MBED_ERROR_NONE && *desc_size ==  SIZE_DESC_FIXED) ;
*/
mbed_error_t  class_get_descriptor(uint8_t             iface_id,
                                        uint8_t            *buf,
                                        uint8_t           *desc_size,
                                        uint32_t            usbdci_handler ) ;


#endif/*!__FRAMAC__*/

/*********************************************************
 * Core API
 */
mbed_error_t usbctrl_get_context(uint32_t device_id,
                                 usbctrl_context_t **ctx);

bool usbctrl_is_endpoint_exists(usbctrl_context_t *ctx, uint8_t ep);

usb_ep_dir_t usbctrl_get_endpoint_direction(usbctrl_context_t *ctx, uint8_t ep);

bool usbctrl_is_interface_exists(usbctrl_context_t *ctx, uint8_t iface);

usbctrl_interface_t* usbctrl_get_interface(usbctrl_context_t *ctx, uint8_t iface);

mbed_error_t usbctrl_get_handler(usbctrl_context_t *ctx,
                                 uint32_t *handler);


#endif/*!USBCTRL_H_*/
