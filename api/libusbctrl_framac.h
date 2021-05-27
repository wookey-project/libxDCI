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

#include "libusbotghs.h"
#include "generated/devlist.h"

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
#define usb_backend_drv_get_ep_mpsize usbotghs_get_ep_mpsize
#define usb_backend_drv_activate_endpoint usbotghs_activate_endpoint



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



#define MAX_USB_CTRL_CTX CONFIG_USBCTRL_MAX_CTX
#define MAX_USB_CTRL_CFG CONFIG_USBCTRL_MAX_CFG

/*@
  logic boolean devid_is_valid(uint32_t devid) =
    (devid == USB_OTG_HS_ID || devid == USB_OTG_FS_ID);
*/

/*
 * This ghost variable is set each time one of the libusbdci private globals is set by one of the exported API.
 * In the API public function contracts, this variable is set as assigned, and private assigns are specified in private contracts.
 * The goal is to simplify and help composed proofs between various library.
 */
/*@ ghost uint32_t GHOST_opaque_libusbdci_privates = 0; */

/*
    this variable must be global and no static for eva (so that entrypoint can modify it)
    but for WP proof, it must be considered as a static variable (and thus, be replaced with ghost variable in function specifications for WP)
*/
  uint8_t num_ctx = 0;
//@ ghost  uint8_t GHOST_num_ctx = num_ctx;

/*@ lemma u16_and_is_u16:
    \forall unsigned short s, m ; 0 <= (s & m) <= 65535 ;
*/

#endif/*!__FRAMAC__*/

#endif/*!LIBUSBCTRL_FRAMAC_H_*/
