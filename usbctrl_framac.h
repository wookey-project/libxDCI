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
#ifndef USBCTRL_FRAMAC_H_
#define USBCTRL_FRAMAC_H_

#ifdef __FRAMAC__

//pmo init todo?
//@ ghost  uint8_t GHOST_idx_ctx = 0;



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
        i == USB_DEVICE_STATE_CONFIGURED ;
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


/*
 * These prototypes are transition functions prototypes.
 * They are required by state automaton MetaCSL specifications in usbctrl_state.c file.
 */
mbed_error_t usbctrl_std_req_handle_set_address(usbctrl_setup_pkt_t const * const pkt,
                                                       usbctrl_context_t *ctx);

mbed_error_t usbctrl_std_req_handle_set_configuration(usbctrl_setup_pkt_t const * const pkt,
                                                             usbctrl_context_t *ctx);

mbed_error_t usbctrl_handle_reset(uint32_t dev_id);

mbed_error_t usbctrl_handle_usbsuspend(uint32_t dev_id __attribute__((unused)));

mbed_error_t usbctrl_handle_wakeup(uint32_t dev_id __attribute__((unused)));



#endif/*!__FRAMAC__*/

#endif/*!USBCTRL_FRAMAC_H_*/

