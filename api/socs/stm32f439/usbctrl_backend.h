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
#ifndef USBCTRL_BACKEND_H_
#define USBCTRL_BACKEND_H_

/*
 * This file is an abstraction of the backend USB driver API, which permits to
 * interact with various USB drivers on various boards, while they keep the same
 * upper layer API.
 * The libusbctrl consider that a USB driver should respect a generic USB driver
 * API which permits to handle:
 * - driver initialization
 * - driver configuration
 * - endpoint manipulation (configuration, activation, deactivation, deconfiguration)
 * - USB relacted action on endpoints (ACK, NAK, STALL actions)
 * - data reception and transmission on endpoint (sending and receiving data,
 *   depending on the endpoint direction)
 *
 * If there is variation between driver enumerates (MPSIZE, EP type, etc.), the enumerates
 * must be overloaded here, through an abstracted type.
 *
 * If the abstraction API only use preprocessing substitution (i.e. the fastest mechanism
 * as it does not generate runtime modification), the driver must be compatible with the
 * libusbctrl API usage (return type, arguments types).
 *
 * On the other side, the abstraction layer must define volatile functions that translate
 * the libusbctrl usage of the driver API into a driver-compliant usage.
 * This will add some supplementary instructions at runtime.
 */

#include "autoconf.h"
#include "libc/types.h"

/*
 * First, specify the effective driver header to load
 */

/*
 * Abstraction layer for the STM32F4 USB OTG HS driver
 * Here, only preprocessing usage is enough.
 *
 * TODO: by now, abstraction is mutually exclusive for multiple backend IP.
 * The goal is to allow the usage of per-context, independent IP handling,
 * even for the same application. The libctrl API is enough for that
 * (device ID is passed to handler and associated to each context).
 */

#if CONFIG_USR_DRV_USB_HS
#include "libusbotghs.h"

/*
 * EP name abstraction
 */
#define EP0 USBOTG_HS_EP0
#define EP1 USBOTG_HS_EP1
#define EP2 USBOTG_HS_EP2
#define EP3 USBOTG_HS_EP3
#define EP4 USBOTG_HS_EP4
#define EP5 USBOTG_HS_EP5
#define EP6 USBOTG_HS_EP6
#define EP7 USBOTG_HS_EP7


/*
 * About driver's API types.
 * Here we keep the enumerates 'as-is' (no modification of the enumeration in the
 * abstraction layer).
 */
#define usb_backend_drv_ep_dir_t usbotghs_ep_dir_t
#define USB_BACKEND_DRV_MODE_DEVICE USBOTGHS_MODE_DEVICE

#define USB_BACKEND_DRV_EP_DIR_IN   USBOTG_HS_EP_DIR_IN
#define USB_BACKEND_DRV_EP_DIR_OUT  USBOTG_HS_EP_DIR_OUT


#define USB_BACKEND_DRV_EP_TYPE_CONTROL     USBOTG_HS_EP_TYPE_CONTROL
#define USB_BACKEND_DRV_EP_TYPE_ISOCHRONOUS USBOTG_HS_EP_TYPE_ISOCHRONOUS
#define USB_BACKEND_DRV_EP_TYPE_BULK        USBOTG_HS_EP_TYPE_BULK
#define USB_BACKEND_DRV_EP_TYPE_INT         USBOTG_HS_EP_TYPE_INT


#define USB_BACKEND_DRV_EP_STATE_IDLE      USBOTG_HS_EP_STATE_IDLE
#define USB_BACKEND_DRV_EP_STATE_SETUP_WIP USBOTG_HS_EP_STATE_SETUP_WIP
#define USB_BACKEND_DRV_EP_STATE_SETUP     USBOTG_HS_EP_STATE_SETUP
#define USB_BACKEND_DRV_EP_STATE_STATUS    USBOTG_HS_EP_STATE_STATUS
#define USB_BACKEND_DRV_EP_STATE_STALL     USBOTG_HS_EP_STATE_STALL
#define USB_BACKEND_DRV_EP_STATE_DATA_IN_WIP USBOTG_HS_EP_STATE_DATA_IN_WIP
#define USB_BACKEND_DRV_EP_STATE_DATA_in   USBOTG_HS_EP_STATE_DATA_IN
#define USB_BACKEND_DRV_EP_STATE_DATA_OUT_WIP   USBOTG_HS_EP_STATE_DATA_OUT_WIP
#define USB_BACKEND_DRV_EP_STATE_DATA_OUT  USBOTG_HS_EP_STATE_DATA_OUT
#define USB_BACKEND_DRV_EP_STATE_INVALID   USBOTG_HS_EP_STATE_INVALID

#define USB_BACKEND_EP_EVENFRAME   USB_HS_DXEPCTL_SD0PID_SEVNFRM
#define USB_BACKEND_EP_ODDFRAME    USB_HS_DXEPCTL_SD1PID_SODDFRM



/*
 * About driver's API prototypes
 */
#define usb_backend_drv_configure           usbotghs_configure
#define usb_backend_drv_declare             usbotghs_declare
#define usb_backend_drv_activate_endpoint   usbotghs_activate_endpoint
#define usb_backend_drv_configure_endpoint  usbotghs_configure_endpoint
#define usb_backend_drv_get_ep_state        usbotghs_get_ep_state
#define usb_backend_drv_send_data           usbotghs_send_data
#define usb_backend_drv_send_zlp            usbotghs_send_zlp
#define usb_backend_drv_set_address         usbotghs_set_address
#define usb_backend_drv_set_recv_fifo       usbotghs_set_recv_fifo
/* USB protocol standard handshaking */
#define usb_backend_drv_ack                 usbotghs_endpoint_clear_nak
#define usb_backend_drv_nak                 usbotghs_endpoint_set_nak
#define usb_backend_drv_stall               usbotghs_endpoint_stall

#define usb_backend_get_ep_mpsize           usbotghs_get_ep_mpsize

#else


#include "libusbotgfs.h"

/*
 * EP name abstraction
 */
#define EP0 USBOTG_FS_EP0
#define EP1 USBOTG_FS_EP1
#define EP2 USBOTG_FS_EP2
#define EP3 USBOTG_FS_EP3
#define EP4 USBOTG_FS_EP4
#define EP5 USBOTG_FS_EP5
#define EP6 USBOTG_FS_EP6
#define EP7 USBOTG_FS_EP7



#define usb_backend_drv_ep_dir_t usbotgfs_ep_dir_t
#define USB_BACKEND_DRV_MODE_DEVICE USBOTGFS_MODE_DEVICE

#define USB_BACKEND_DRV_EP_DIR_IN   USBOTG_FS_EP_DIR_IN
#define USB_BACKEND_DRV_EP_DIR_OUT  USBOTG_FS_EP_DIR_OUT

#define USB_BACKEND_DRV_EP_TYPE_CONTROL     USBOTG_FS_EP_TYPE_CONTROL
#define USB_BACKEND_DRV_EP_TYPE_ISOCHRONOUS USBOTG_FS_EP_TYPE_ISOCHRONOUS
#define USB_BACKEND_DRV_EP_TYPE_BULK        USBOTG_FS_EP_TYPE_BULK
#define USB_BACKEND_DRV_EP_TYPE_INT         USBOTG_FS_EP_TYPE_INT


#define USB_BACKEND_DRV_EP_STATE_IDLE      USBOTG_FS_EP_STATE_IDLE
#define USB_BACKEND_DRV_EP_STATE_SETUP_WIP USBOTG_FS_EP_STATE_SETUP_WIP
#define USB_BACKEND_DRV_EP_STATE_SETUP     USBOTG_FS_EP_STATE_SETUP
#define USB_BACKEND_DRV_EP_STATE_STATUS    USBOTG_FS_EP_STATE_STATUS
#define USB_BACKEND_DRV_EP_STATE_STALL     USBOTG_FS_EP_STATE_STALL
#define USB_BACKEND_DRV_EP_STATE_DATA_IN_WIP USBOTG_FS_EP_STATE_DATA_IN_WIP
#define USB_BACKEND_DRV_EP_STATE_DATA_IN   USBOTG_FS_EP_STATE_DATA_IN
#define USB_BACKEND_DRV_EP_STATE_DATA_OUT_WIP   USBOTG_FS_EP_STATE_DATA_OUT_WIP
#define USB_BACKEND_DRV_EP_STATE_DATA_OUT  USBOTG_FS_EP_STATE_DATA_OUT
#define USB_BACKEND_DRV_EP_STATE_INVALID   USBOTG_FS_EP_STATE_INVALID

#define USB_BACKEND_EP_EVENFRAME   USB_FS_DXEPCTL_SD0PID_SEVNFRM
#define USB_BACKEND_EP_ODDFRAME    USB_FS_DXEPCTL_SD1PID_SODDFRM
/*
 * About driver's API prototypes
 */
#define usb_backend_drv_configure           usbotgfs_configure
#define usb_backend_drv_declare             usbotgfs_declare
#define usb_backend_drv_activate_endpoint   usbotgfs_activate_endpoint
#define usb_backend_drv_configure_endpoint  usbotgfs_configure_endpoint
#define usb_backend_drv_get_ep_state        usbotgfs_get_ep_state
#define usb_backend_drv_send_data           usbotgfs_send_data
#define usb_backend_drv_send_zlp            usbotgfs_send_zlp
#define usb_backend_drv_set_address         usbotgfs_set_address
#define usb_backend_drv_set_recv_fifo       usbotgfs_set_recv_fifo
/* USB protocol standard handshaking */
#define usb_backend_drv_ack                 usbotgfs_endpoint_clear_nak
#define usb_backend_drv_nak                 usbotgfs_endpoint_set_nak
#define usb_backend_drv_stall               usbotgfs_endpoint_stall

#define usb_backend_get_ep_mpsize           usbotgfs_get_ep_mpsize

#endif

#endif/*!USBCTRL_BACKEND_H_*/
