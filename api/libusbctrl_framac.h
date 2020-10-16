/*
 *
 * Copyright 2019 The wookey project team <wookey@ssi.gouv.fr>
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
#ifndef LIBUSBCTRL_FRAMAC_H_
#define LIBUSBCTRL_FRAMAC_H_

#ifdef __FRAMAC__

#include "usbotghs.h"
#include "usbotghs_fifos.h"
#include "api/libusbotghs.h"
#include "generated/devlist.h"

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
#  define CONFIG_USR_LIB_USBCTRL_DEV_PRODUCTID  CONFIG_USR_LIB_USBCTRL_DFU_DEV_PRODUCTID
# endif
#endif

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


/*
    this variable must be global and no static for eva (so that entrypoint can modify it)
    but for WP proof, it must be considered as a static variable (and thus, be replaced with ghost variable in function specifications for WP)
*/
  uint8_t num_ctx = 0;
// pmo init ghost
//@ ghost  uint8_t GHOST_num_ctx = num_ctx;

//pmo init todo? 
//@ ghost  uint8_t GHOST_idx_ctx = 0;


/*@ lemma u16_and_is_u16:
    \forall unsigned short s, m ; 0 <= (s & m) <= 65535 ;
*/

/*@ predicate is_valid_error(mbed_error_t i) =
    i == MBED_ERROR_NONE ||
    i == MBED_ERROR_NOMEM ||
    i == MBED_ERROR_NOSTORAGE ||
    i == MBED_ERROR_NOBACKEND ||
    i == MBED_ERROR_INVCREDENCIALS ||
    i == MBED_ERROR_UNSUPORTED_CMD ||
    i == MBED_ERROR_INVSTATE ||
    i == MBED_ERROR_NOTREADY ||
    i == MBED_ERROR_BUSY ||
    i == MBED_ERROR_DENIED ||
    i == MBED_ERROR_UNKNOWN ||
    i == MBED_ERROR_INVPARAM ||
    i == MBED_ERROR_WRERROR ||
    i == MBED_ERROR_RDERROR ||
    i == MBED_ERROR_INITFAIL ||
    i == MBED_ERROR_TOOBIG ||
    i == MBED_ERROR_NOTFOUND  ;
*/


#define usb_backend_drv_declare usbotghs_declare
#define usb_backend_drv_get_speed usbotghs_get_speed
#define usb_backend_drv_stall usbotghs_endpoint_stall
#define usb_backend_drv_send_data usbotghs_send_data
#define usb_backend_drv_ack usbotghs_endpoint_clear_nak
#define usb_backend_drv_nak usbotghs_endpoint_set_nak
#define usb_backend_drv_set_address usbotghs_set_address
#define usb_backend_drv_send_zlp usbotghs_send_zlp
#define usb_backend_drv_configure_endpoint usbotghs_configure_endpoint
#define usb_backend_drv_deconfigure_endpoint usbotghs_deconfigure_endpoint
#define usb_backend_drv_set_recv_fifo usbotghs_set_recv_fifo
#define usb_backend_drv_get_ep_state usbotghs_get_ep_state
#define usb_backend_drv_configure usbotghs_configure
#define usb_backend_get_ep_mpsize usbotghs_get_ep_mpsize

#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX
#define MAX_USB_CTRL_CFG CONFIG_USBCTRL_MAX_CFG



bool reset_requested = false;

uint8_t SIZE_DESC_FIXED ;
bool FLAG ;

/* avoid Ghosting for getters in other files than usbctrl.c */
usbctrl_context_t  ctx_list[MAX_USB_CTRL_CTX] = {0} ;

/* this enumerate is declared in libusbctrl_framac.h to handle specs usage
 * of libusbctrl proof
 */

typedef enum {
    USB_DEVICE_STATE_ATTACHED = 0,         /* Attached but not powered. Should never be reached from device side */
    USB_DEVICE_STATE_POWERED,              /* Attached and powered, first reset not received yet */
    USB_DEVICE_STATE_SUSPENDED_POWER,      /* Suspended, from the Power state */
    USB_DEVICE_STATE_SUSPENDED_DEFAULT,    /* Suspended, from the default state */
    USB_DEVICE_STATE_SUSPENDED_ADDRESS,    /* Suspended, from the address state */
    USB_DEVICE_STATE_SUSPENDED_CONFIGURED, /* Suspended, from the configured state */
    USB_DEVICE_STATE_DEFAULT,              /* First reset received, unique address not yet assigned */
    USB_DEVICE_STATE_ADDRESS,              /* First reset received, address asigned, not yet configured */
    USB_DEVICE_STATE_CONFIGURED,           /* First reset received, address asigned, configured, functions provided by the device can now be used */
    USB_DEVICE_STATE_INVALID               /* Not defined in the USB standard. exists as an INVALID case. Should not be reached */
} usb_device_state_t;

/*@ predicate is_valid_state(usb_device_state_t i) =
        i == USB_DEVICE_STATE_ATTACHED ||
        i == USB_DEVICE_STATE_POWERED ||
        i == USB_DEVICE_STATE_SUSPENDED_POWER ||
        i == USB_DEVICE_STATE_SUSPENDED_DEFAULT ||
        i == USB_DEVICE_STATE_SUSPENDED_ADDRESS ||
        i == USB_DEVICE_STATE_SUSPENDED_CONFIGURED ||
        i == USB_DEVICE_STATE_DEFAULT ||
        i == USB_DEVICE_STATE_ADDRESS ||
        i == USB_DEVICE_STATE_CONFIGURED ||
        i == USB_DEVICE_STATE_INVALID ;
*/

/*****************************************************************
 * Initially unexported API, used in order to simulate triggers
 * for upper layers. The goal here is to handle full coverage with EVA,
 * by calling various triggers that driver & control plane should have
 * executed on external events, manually. To handle this, upper layer
 * framaC entrypoints need to emulate the control plane and driver plane
 * internal structures updates as if effective interrupts had risen.
 */

/*@
    @ requires GHOST_num_ctx == num_ctx ;
    @ requires \separated(&ctx_list + (0..(GHOST_num_ctx-1)),&GHOST_num_ctx);
    @ requires \valid_read(ctx_list + (0..(GHOST_num_ctx-1))) ;
    @ assigns *ctx, GHOST_idx_ctx;

    @ behavior bad_pointer :
    @   assumes ctx == \null ;
    @   ensures \result == MBED_ERROR_INVPARAM ;
    @   ensures GHOST_idx_ctx == MAX_USB_CTRL_CTX ;

    @ behavior not_found :
    @   assumes ctx != \null ;
    @   assumes !(\exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id) ;
    @   ensures \result == MBED_ERROR_NOTFOUND ;
    @   ensures GHOST_idx_ctx == MAX_USB_CTRL_CTX ;

    @ behavior found :
    @   assumes ctx != \null ;
    @   assumes \exists integer i ; 0 <= i < GHOST_num_ctx && ctx_list[i].dev_id == device_id ;
    @   ensures \exists integer i ; 0 <= i < GHOST_num_ctx && \old(ctx_list[i].dev_id) == device_id && GHOST_idx_ctx==i ;
    @   ensures 0 <= GHOST_idx_ctx < GHOST_num_ctx ;
    @   ensures \result == MBED_ERROR_NONE ;
    @	ensures *ctx == &ctx_list[GHOST_idx_ctx];

    @ complete behaviors ;
    @ disjoint behaviors ;
*/
mbed_error_t usbctrl_get_context(uint32_t device_id,
                                 usbctrl_context_t **ctx);


#endif/*!__FRAMAC__*/

#endif/*!LIBUSBCTRL_FRAMAC_H_*/
