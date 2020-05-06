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

#ifndef USBOTGHS_FRAMA_H_
#define USBOTGHS_FRAMA_H_

#include "autoconf.h"


#if defined(__FRAMAC__)
#include "libc/regutils.h"
#else
#include "libc/regutils.h"
#endif/*!__FRAMAC__*/

#include "libc/types.h"
#include "libc/stdio.h"

#include "socs/stm32f439/usbotghs_regs.h"
#include "socs/stm32f439/usbctrl_backend.h"

#include "socs/stm32f439/libusbotghs.h"


#define USBOTGHS_REG_CHECK_TIMEOUT 50

#define MAX_TIME_DETACH     4000

#define USB_GLOBAL_OUT_NAK        0b0001 /* Global OUT NAK (triggers an interrupt) */
#define USB_OUT_PACKET_RECEIVED   0b0010 /* OUT data packet received */
#define USB_OUT_TRANSFERT_COMPLETED   0b0011 /* OUT transfer completed (triggers an interrupt) */
#define USB_SETUP_TRANS_COMPLETED 0b0100 /* SETUP transaction completed (triggers an interrupt) */
#define USB_SETUP_PACKET_RECEIVED 0b0110 /* SETUP data packet received */


/*********************************************************
 * General tooling
 */

#if CONFIG_USR_DRV_USBOTGHS_DEBUG
# define log_printf(...) printf(__VA_ARGS__)
#else
# define log_printf(...)
#endif

/********************************************************
 * Driver private structures and types
 */

typedef enum {
    USBOTG_HS_SPEED_LS = 0, /* aka Low speed (USB 1.0) */
    USBOTG_HS_SPEED_FS = 1, /* aka Full Speed (USB 1.1) */
    USBOTG_HS_SPEED_HS = 2, /* aka High speed (USB 2.0) */
} usbotghs_speed_t;

/*
 * local context hold by the driver
 */
#if defined(__FRAMAC__)
typedef struct {
    uint8_t                      id;           /* EP id (libusbctrl view) */
    bool                         configured;   /* is EP configured in current configuration ? */
    uint16_t                     mpsize;       /* max packet size (bitfield, 11 bits, in bytes) */
    usbotghs_ep_type_t           type;         /* EP type */
    usbotghs_ep_state_t state;        /* EP current state */
    usbotghs_ep_dir_t   dir;
    usbotghs_ioep_handler_t      handler;      /* EP Handler for (I|O)EPEVENT */

    uint8_t            *fifo;         /* associated RAM FIFO (recv) */
    uint32_t            fifo_idx;     /* current FIFO index  (recv) */
    uint32_t            fifo_size;    /* associated RAM FIFO max size (recv) */
    bool                fifo_lck;     /* DMA, locking mechanism (recv) */
    bool                core_txfifo_empty; /* core TxFIFO (Half) empty */
} usbotghs_ep_t;
#else
typedef struct {
    uint8_t                      id;           /* EP id (libusbctrl view) */
    bool                         configured;   /* is EP configured in current configuration ? */
    uint16_t                     mpsize;       /* max packet size (bitfield, 11 bits, in bytes) */
    usbotghs_ep_type_t           type;         /* EP type */
    volatile usbotghs_ep_state_t state;        /* EP current state */
    volatile usbotghs_ep_dir_t   dir;
    usbotghs_ioep_handler_t      handler;      /* EP Handler for (I|O)EPEVENT */

    volatile uint8_t            *fifo;         /* associated RAM FIFO (recv) */
    volatile uint32_t            fifo_idx;     /* current FIFO index  (recv) */
    volatile uint32_t            fifo_size;    /* associated RAM FIFO max size (recv) */
    volatile bool                fifo_lck;     /* DMA, locking mechanism (recv) */
    volatile bool                core_txfifo_empty; /* core TxFIFO (Half) empty */
} usbotghs_ep_t;
#endif/*!__FRAMAC__*/

#define USBOTGHS_MAX_IN_EP   8
#define USBOTGHS_MAX_OUT_EP  3

/* current context of the USB OTG HS Core */
#if defined(__FRAMAC__)
typedef struct {
    device_t            dev;             /* associated device_t structure */
    int                 dev_desc;        /* device descriptor */
    usbotghs_dev_mode_t mode;            /* current OTG mode (host or device) */
    bool                gonak_req;       /* global OUT NAK requested */
    bool                gonak_active;    /* global OUT NAK effective */
    uint16_t            fifo_idx;        /* consumed Core FIFO */
    usbotghs_ep_t       in_eps[USBOTGHS_MAX_IN_EP];       /* list of HW supported IN EPs */
    usbotghs_ep_t       out_eps[USBOTGHS_MAX_OUT_EP];      /* list of HW supported OUT EPs */
    usbotghs_speed_t    speed;        /* device enumerated speed, default HS */
} usbotghs_context_t;
#else
typedef struct {
    device_t            dev;             /* associated device_t structure */
    int                 dev_desc;        /* device descriptor */
    usbotghs_dev_mode_t mode;            /* current OTG mode (host or device) */
    bool                gonak_req;       /* global OUT NAK requested */
    bool                gonak_active;    /* global OUT NAK effective */
    uint16_t            fifo_idx;        /* consumed Core FIFO */
    usbotghs_ep_t       in_eps[USBOTGHS_MAX_IN_EP];       /* list of HW supported IN EPs */
    usbotghs_ep_t       out_eps[USBOTGHS_MAX_OUT_EP];      /* list of HW supported OUT EPs */
    volatile usbotghs_speed_t    speed;        /* device enumerated speed, default HS */
} usbotghs_context_t;
#endif/*!__FRAMAC__*/


usbotghs_context_t *usbotghs_get_context(void);

/*
 * Declaring the device against EwoK
 */
mbed_error_t usbotghs_declare(void);

/*
 * Core initial setup and config. At the end of the initialization, the Core should
 * have its USB control pipe ready to receive the first requests from the host.
 */
mbed_error_t usbotghs_configure(usbotghs_dev_mode_t mode,
                                usbotghs_ioep_handler_t ieph,
                                usbotghs_ioep_handler_t oeph);

/*
 * Sending data (whatever data type is (i.e. status on control pipe or data on
 * data (Bulk, IT or isochronous) pipe)
 * This is not a syncrhonous request, i.e. data are stored into the USB OTG HS
 * interanal FIFO, waiting for bus transmission. When data are fully transmitted,
 * a iepint (device mode) or oepint (host mode) is triggered to inform the upper
 * layer that the content has been sent. Although, it is possible to push some
 * other data in the internal FIFO if needed, while this FIFO is not full
 * (check for this function return value)
 *
 * @src the RAM FIFO from which the data are read
 * @size the amount of data bytes to send
 * @ep the endpoint on which the data are to be sent
 *
 * @return MBED_ERROR_NONE if data has been correctly transmitted into the internal
 * core FIFO, or MBED_ERROR_BUSY if the interal core FIFO for the given EP is full
 */
mbed_error_t usbotghs_send_data(uint8_t *src, uint32_t size, uint8_t ep);

/*
 * Configure for receiving data. Receiving data is a triggering event, not a direct call.
 * As a consequence, the upper layers have to specify the amount of data requested for
 * the next USB transaction on the given OUT (device mode) or IN (host mode) enpoint.
 *
 * @dst is the destination buffer that will be used to hold  @size amount of data bytes
 * @size is the amount of data bytes to load before await the upper stack
 * @ep is the active endpoint on which this action is done
 *
 * On data reception:
 * - if there is enough data loaded in the output buffer, the upper stack is awoken
 * - If not, data is silently stored in FIFO RAM (targetted by dst), and the driver waits
 *   for the next content while 'size' amount of data is not reached
 *
 * @return MBED_ERROR_NONE if setup is ok, or various possible other errors (INVSTATE
 * for invalid enpoint type, INVPARAM if dst is NULL or size invalid)
 */

mbed_error_t usbotghs_set_recv_fifo(uint8_t *dst, uint32_t size, uint8_t ep); // Cyril : cette fonction est également définie dans usbotghs_fifos.h. Pourquoi 2 fois la définition?


/*
 * Send a special zero-length packet on EP ep
 */
mbed_error_t usbotghs_send_zlp(uint8_t ep);

/*
 * Activate the configuration global stall mode. If any EP has its stall mode configured,
 * it can override the global stall mode
 * INFO: stall mode for Control and data EP don't have the same meaning. See datasheet,
 * chap 35.13.7
 */
mbed_error_t usbotghs_global_stall(void);

/*
 * Clear the global stall mode.
 */
mbed_error_t usbotghs_global_stall_clear(void);

/*
 * Set the STALL mode for the given EP
 */
mbed_error_t usbotghs_endpoint_stall(uint8_t ep_id, usbotghs_ep_dir_t dir);

/*
 * Clear the STALL mode for the given EP
 */
mbed_error_t usbotghs_endpoint_stall_clear(uint8_t ep, usbotghs_ep_dir_t dir);

mbed_error_t usbotghs_endpoint_set_nak(uint8_t ep_id, usbotghs_ep_dir_t dir);

mbed_error_t usbotghs_endpoint_clear_nak(uint8_t ep_id, usbotghs_ep_dir_t dir);

/*
 * Activate the given EP (for e.g. to transmit data)
 */
mbed_error_t usbotghs_configure_endpoint(uint8_t               ep,
                                         usbotghs_ep_type_t    type,
                                         usbotghs_ep_dir_t     dir,
                                         usbotghs_epx_mpsize_t mpsize,
                                         usbotghs_ep_toggle_t  dtoggle,
                                         usbotghs_ioep_handler_t handler);

/*
 * Deactivate the given EP (Its configuration is keeped, the EP is *not* deconfigured)
 */
mbed_error_t usbotghs_deconfigure_endpoint(uint8_t ep);

/*
 * Configure the given EP in order to be ready to work
 */
mbed_error_t usbotghs_activate_endpoint(uint8_t               id,
                                        usbotghs_ep_dir_t     dir);

/*
 * Deconfigure the given EP. The EP is no more usable after this call. A new configuration
 * of the EP must be done before reuse it.
 * This function is typically used on SetConfiguration Requests schedule, or on
 * Reset frame reception to reconfigure the Core in a known clear state.
 */
mbed_error_t usbotghs_deactivate_endpoint(uint8_t ep,
                                          usbotghs_ep_dir_t     dir);

/*
 * Temporarily disable Endpoint (Endpoint is not deconfigured but neither emit
 * nor receive data (including IN Token or OUT handshakes)
 */
mbed_error_t usbotghs_endpoint_disable(uint8_t ep,
                                       usbotghs_ep_dir_t     dir);



/*
 * Reenable Endpoint previously disabled
 */
mbed_error_t usbotghs_endpoint_enable(uint8_t ep,
                                      usbotghs_ep_dir_t     dir);

/**
 * usb_driver_set_address - Set the address of the device
 * @addr: Device's address
 */
void usbotghs_set_address(uint16_t addr);

/* Map USB device. TODO */
void usbotghs_bind(void);

void usbotghs_unbind(void);

usbotghs_ep_state_t usbotghs_get_ep_state(uint8_t epnum, usbotghs_ep_dir_t dir);

uint32_t usbotghs_get_ep_mpsize(void);

usbotghs_port_speed_t usbotgfs_get_speed(void);


#endif /*!USBOTGHS_FRAMA_H_ */