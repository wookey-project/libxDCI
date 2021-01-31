#ifndef ENTRY_H_
#define ENTRY_H_

#include "libc/types.h"

bool reset_requested = false;

#define MAX_EPx_PKT_SIZE 512

extern volatile uint8_t Frama_C_entropy_source_8 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint16_t Frama_C_entropy_source_16 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
extern volatile uint32_t Frama_C_entropy_source_32 __attribute__((unused)) __attribute__((FRAMA_C_MODEL));

/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */
uint8_t Frama_C_interval_8(uint8_t min, uint8_t max);

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */
uint16_t Frama_C_interval_16(uint16_t min, uint16_t max);

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */
uint32_t Frama_C_interval_32(uint32_t min, uint32_t max);

void usbctrl_reset_received(void);

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



/*@
    @ requires \valid(packet);
    @ assigns \nothing ;
    @ ensures is_valid_error(\result);
*/

mbed_error_t class_rqst_handler(uint32_t usbxdci_handler,
                                       usbctrl_setup_pkt_t *packet);


mbed_error_t handler_ep(uint32_t dev_id, uint32_t size, uint8_t ep_id);

void test_fcn_driver_eva(void) ;



#endif/*!ENTRY_H_*/
