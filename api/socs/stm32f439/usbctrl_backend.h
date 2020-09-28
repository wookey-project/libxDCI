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

/*
 * Generic typedefs. each device driver is responsible for:
 * 1. use the same enumerate values
 * 2. handle the translation in its generic abstraction, if needed.
 *    In this last case, the driver upper abstraction is responsible for
 *    defining inline functions that translate below types into local driver
 *    types. For a given SoC, please try to handle these time in the same way
 *    to avoid such constraint, which may generate overcost.
 *
 *
 * In the case of usbotghs and usbotgfs, this part does not require
 * translation from the drivers are both of them use the same enumerations
 * and types as both IP are nearly the same.
 * We can directly use preprocessing values that will be passed to forward-declarated
 * prototypes.
 */

#define USB_BACKEND_MEMORY_BASE 0x40040000
#define USB_BACKEND_MEMORY_END  0x40044000

typedef enum {
    USB_BACKEND_DRV_PORT_LOWSPEED = 0,
    USB_BACKEND_DRV_PORT_FULLSPEED = 1,
    USB_BACKEND_DRV_PORT_HIGHSPEED = 2
} usb_backend_drv_port_speed_t;



typedef enum {
    EP0 = 0,
    EP1 = 1,
    EP2 = 2,
    EP3 = 3,
    EP4 = 4,
    EP5 = 5,
    EP6 = 6,
    EP7 = 7,
    EP8 = 8
} usb_backend_drv_ep_nb_t;

typedef enum {
    USB_BACKEND_DRV_MODE_HOST = 0,
    USB_BACKEND_DRV_MODE_DEVICE = 1
} usb_backend_drv_mode_t;


typedef enum {
    USB_BACKEND_DRV_EP_DIR_IN  = 0,
    USB_BACKEND_DRV_EP_DIR_OUT = 1,
    USB_BACKEND_DRV_EP_DIR_BOTH = 2
} usb_backend_drv_ep_dir_t;

typedef enum {
    USB_BACKEND_DRV_EP_TYPE_CONTROL     = 0,
    USB_BACKEND_DRV_EP_TYPE_ISOCHRONOUS = 1,
    USB_BACKEND_DRV_EP_TYPE_BULK        = 2,
    USB_BACKEND_DRV_EP_TYPE_INT         = 3
} usb_backend_drv_ep_type_t;

typedef enum {
    USB_BACKEND_DRV_EP_STATE_IDLE         = 0,
    USB_BACKEND_DRV_EP_STATE_SETUP_WIP    = 1,
    USB_BACKEND_DRV_EP_STATE_SETUP        = 2,
    USB_BACKEND_DRV_EP_STATE_STATUS       = 3,
    USB_BACKEND_DRV_EP_STATE_STALL        = 4,
    USB_BACKEND_DRV_EP_STATE_DATA_IN_WIP  = 5,
    USB_BACKEND_DRV_EP_STATE_DATA_IN      = 6,
    USB_BACKEND_DRV_EP_STATE_DATA_OUT_WIP = 7,
    USB_BACKEND_DRV_EP_STATE_DATA_OUT     = 8,
    USB_BACKEND_DRV_EP_STATE_INVALID      = 9
} usb_backend_drv_ep_state_t;

typedef enum {
    USB_BACKEND_DRV_EPx_MPSIZE_64BYTES = 64,
    USB_BACKEND_DRV_EPx_MPSIZE_128BYTES = 128,
    USB_BACKEND_DRV_EPx_MPSIZE_512BYTES = 512,
    USB_BACKEND_DRV_EPx_MPSIZE_1024BYTES  = 1024,
} usb_backend_drv_epx_mpsize_t;



typedef enum {
    USB_BACKEND_EP_EVENFRAME  = 0,
    USB_BACKEND_EP_ODDFRAME   = 1
} usb_backend_drv_ep_toggle_t;

typedef mbed_error_t (*usb_backend_drv_ioep_handler_t)(uint32_t dev_id, uint32_t size, uint8_t ep);
/*
 * About driver's API prototypes
 * Here, we only define symbols. These symbols are resolved by the generic
 * frontend part of the corresponding driver (usb otg hs or usb otg fs
 * are responsible for aliasing their symbols with the generic symbols.
 * At link time, symbols are resolved by the linker, which finish the
 * association between the generic backend and the selected driver.
 */
mbed_error_t usb_backend_drv_configure(usb_backend_drv_mode_t mode,
                                       usb_backend_drv_ioep_handler_t ieph,
                                       usb_backend_drv_ioep_handler_t oeph);

mbed_error_t usb_backend_drv_declare(void);
mbed_error_t usb_backend_drv_activate_endpoint(uint8_t               id,
                                         usb_backend_drv_ep_dir_t     dir);
mbed_error_t usb_backend_drv_configure_endpoint(uint8_t               ep,
                                         usb_backend_drv_ep_type_t    type,
                                         usb_backend_drv_ep_dir_t     dir,
                                         usb_backend_drv_epx_mpsize_t mpsize,
                                         usb_backend_drv_ep_toggle_t  dtoggle,
                                         usb_backend_drv_ioep_handler_t handler);

mbed_error_t usb_backend_drv_deconfigure_endpoint(uint8_t ep);

/* needed for full-duplex EP */
usb_backend_drv_ep_state_t usb_backend_drv_get_ep_state(uint8_t epnum, usb_backend_drv_ep_dir_t dir);
mbed_error_t usb_backend_drv_send_data(uint8_t *src, uint32_t size, uint8_t ep);
mbed_error_t usb_backend_drv_send_zlp(uint8_t ep);
void         usb_backend_drv_set_address(uint16_t addr);
mbed_error_t usb_backend_drv_set_recv_fifo(uint8_t *dst, uint32_t size, uint8_t ep);
/* USB protocol standard handshaking */
mbed_error_t usb_backend_drv_ack(uint8_t ep_id, usb_backend_drv_ep_dir_t dir);
mbed_error_t usb_backend_drv_nak(uint8_t ep_id, usb_backend_drv_ep_dir_t dir);
mbed_error_t usb_backend_drv_stall(uint8_t ep_id, usb_backend_drv_ep_dir_t dir);

mbed_error_t usb_backend_drv_endpoint_disable(uint8_t ep_id, usb_backend_drv_ep_dir_t dir);
mbed_error_t usb_backend_drv_endpoint_enable(uint8_t ep_id, usb_backend_drv_ep_dir_t dir);

uint16_t usb_backend_get_ep_mpsize(void);

usb_backend_drv_port_speed_t usb_backend_drv_get_speed(void);

#endif/*!USBCTRL_BACKEND_H_*/
