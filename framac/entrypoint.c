#include "generated/devlist.h"
#include "api/libusbctrl.h"
#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
//#include <string.h>
#include "usbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl_handlers.h"
#include "usbctrl_requests.h"
#include "usbctrl_descriptors.h"
#include "framac/entrypoint.h"

/*
 * Support for Frama-C testing
 */

//@ assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
void Frama_C_update_entropy_8(void) {
  Frama_C_entropy_source_8 = Frama_C_entropy_source_8;
}

//@ assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
void Frama_C_update_entropy_16(void) {
  Frama_C_entropy_source_16 = Frama_C_entropy_source_16;
}

//@ assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
void Frama_C_update_entropy_32(void) {
  Frama_C_entropy_source_32 = Frama_C_entropy_source_32;
}

/*@ requires order: 0 <= min <= max <= 255;
    assigns \result \from min, max, Frama_C_entropy_source_8;
    assigns Frama_C_entropy_source_8 \from Frama_C_entropy_source_8;
    ensures result_bounded: min <= \result <= max ;
 */

uint8_t Frama_C_interval_8(uint8_t min, uint8_t max)
{
  uint8_t r,aux;
  Frama_C_update_entropy_8();
  aux = Frama_C_entropy_source_8;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 65535;
    assigns \result \from min, max, Frama_C_entropy_source_16;
    assigns Frama_C_entropy_source_16 \from Frama_C_entropy_source_16;
    ensures result_bounded: min <= \result <= max ;
 */

uint16_t Frama_C_interval_16(uint16_t min, uint16_t max)
{
  uint16_t r,aux;
  Frama_C_update_entropy_16();
  aux = Frama_C_entropy_source_16;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@ requires order: 0 <= min <= max <= 4294967295;
    assigns \result \from min, max, Frama_C_entropy_source_32;
    assigns Frama_C_entropy_source_32 \from Frama_C_entropy_source_32;
    ensures result_bounded: min <= \result <= max ;
 */

uint32_t Frama_C_interval_32(uint32_t min, uint32_t max)
{
  uint32_t r,aux;
  Frama_C_update_entropy_32();
  aux = Frama_C_entropy_source_32;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*
 test_fcn_usbctrl : test functions defined in usbctrl.c, generally with correct parameters
*/

void test_fcn_usbctrl(){


    uint32_t dev_id = (uint32_t)Frama_C_interval_32(0,4294967295) ;
    uint32_t size = Frama_C_interval_32(0,4294967295) ;
    uint32_t handler ;
    uint8_t ep = Frama_C_interval_8(0,255);
    uint8_t iface = Frama_C_interval_8(0,MAX_INTERFACES_PER_DEVICE-1);
    uint8_t ep_number = Frama_C_interval_8(0,MAX_EP_PER_INTERFACE);
    uint8_t EP_type = Frama_C_interval_8(0,3);
    uint8_t EP_dir = Frama_C_interval_8(0,2);
    uint8_t USB_class = Frama_C_interval_8(0,17);
    uint32_t USBdci_handler = Frama_C_interval_32(0,4294967295) ;
    usb_device_trans_t transition = Frama_C_interval_8(0,MAX_TRANSITION_STATE-1) ;
    usb_device_state_t current_state = Frama_C_interval_8(0,9);
    usbctrl_request_code_t request = Frama_C_interval_8(0x0,0xc);
    uint8_t interval = Frama_C_interval_8(0,255);


    uint8_t RequestType = Frama_C_interval_8(0,255);
    uint8_t Request = Frama_C_interval_8(0,0xd);
    uint16_t Value = Frama_C_interval_16(0,65535);
    uint16_t Index = Frama_C_interval_16(0,65535);
    uint16_t Length = Frama_C_interval_16(0,65535);

/*
    interface definition with variable parameters
*/

    usbctrl_interface_t iface_1 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep, .eps[0].poll_interval = interval ,
                                  .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor};

    usbctrl_interface_t iface_2 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep, .eps[0].poll_interval = interval ,
                                  .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor};

    usbctrl_interface_t iface_3 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = false,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep, .eps[0].poll_interval = interval ,
                                  .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor};

    usbctrl_setup_pkt_t pkt = { .bmRequestType = RequestType, .bRequest = Request, .wValue = Value, .wIndex = Index, .wLength = Length };
    usbctrl_context_t *ctx1 = NULL;
    usbctrl_context_t *ctx2 = NULL;

    uint32_t ctxh1=0;
    uint32_t ctxh2=0;



    ///////////////////////////////////////////////////
    //        first context
    ///////////////////////////////////////////////////
    usbctrl_declare(8, &ctxh1);  // in order to check dev_id !=6 and != 7 ;
    usbctrl_declare(6, &ctxh1);
    /*@ assert ctxh1 == 0 ; */
    usbctrl_initialize(ctxh1);
    /*@ assert ctxh1 == 0 ; */
    usbctrl_get_context(6, &ctx1);

    usbctrl_declare_interface(ctxh1, &iface_1);
    usbctrl_declare_interface(ctxh1, &iface_2);
    //usbctrl_declare_interface(ctxh1, &iface_3);  // this should be decommented only for test in usbctrl_descriptors.c, but very costly to analyse with EVA
    usbctrl_get_interface(ctx1, iface);
    usbctrl_get_handler(ctx1, &handler);
    usbctrl_is_interface_exists(ctx1, iface);
    usbctrl_is_endpoint_exists(ctx1, ep);
    usbctrl_start_device(ctxh1) ;
    usbctrl_stop_device(ctxh1) ;

    if(ctx1 != NULL){
        ctx1->state = Frama_C_interval_8(0,9);
            usbctrl_is_valid_transition(ctx1->state,transition,ctx1);
            usbctrl_handle_class_requests(&pkt,ctx1) ;
    }


    ///////////////////////////////////////////////////
    //        2nd context
    ///////////////////////////////////////////////////

    usbctrl_declare(7, &ctxh2);
    usbctrl_initialize(ctxh2);
    usbctrl_get_context(7, &ctx2);
    usbctrl_get_handler(ctx2, &handler);
    usbctrl_declare_interface(ctxh2, &iface_1) ;
    usbctrl_declare_interface(ctxh2, &iface_2);
    //usbctrl_declare_interface(ctxh2, &iface_3);
    usbctrl_get_interface(ctx2, iface);

    usbctrl_is_interface_exists(ctx2, iface);
    usbctrl_is_endpoint_exists(ctx2, ep);
    usbctrl_start_device(ctxh2) ;

    /*@ assert ctx2 != 0 ; */
     usb_device_state_t state = usbctrl_get_state(ctx2);
     /*@ assert state == ctx2->state ; */

    usbctrl_stop_device(ctxh2) ;

    if(ctx2 != NULL){
        ctx2->state = Frama_C_interval_8(0,9);
        usbctrl_is_valid_transition(ctx2->state,transition,ctx2);
        usbctrl_handle_class_requests(&pkt,ctx2) ;
    }

    ////////////////////////////////////////////////
    //        functions that use both contexts
    ////////////////////////////////////////////////

    ctx_list[0].ctrl_req_processing = true;  // to reach a state with EVA
    usbctrl_handle_inepevent(dev_id, size, ep);

    usbotghs_ctx.out_eps[0].state = Frama_C_interval_8(0,9);

    // after inepevent, dev_id is 6 or 7, i don't know why... so i declare a new dev_id variable in order to reach ctx_not_found behavior
    uint32_t dev_id_2 = (uint32_t)Frama_C_interval_32(0,4294967295) ;

    usbctrl_handle_outepevent(dev_id_2, size, ep);
    usbctrl_handle_earlysuspend(dev_id) ;
    usbctrl_handle_usbsuspend(dev_id);
    usbctrl_handle_wakeup(dev_id) ;

    // after outepevent, dev_id_2 is 6 or 7, i don't know why... so i declare a new dev_id variable in order to reach ctx_not_found behavior
    uint32_t dev_id_3 = (uint32_t)Frama_C_interval_32(0,4294967295) ;
    usbctrl_handle_reset(dev_id_3);

    usbctrl_next_state(current_state,request);

    uint32_t dev_id_4 = (uint32_t)Frama_C_interval_32(0,4294967295) ;
    // after reset, dev_id_3 is 6 or 7, i don't know why... so i declare a new dev_id
    usbctrl_handle_requests(&pkt, dev_id_4) ;
}

/*
 test_fcn_usbctrl_erreur : test functions defined in usbctrl.c, with bad parameters (error code, defensif code to be checked)
*/

void test_fcn_usbctrl_erreur(){

    uint32_t dev_id =(uint32_t) Frama_C_interval_32(0,4294967295) ;
    uint32_t size = Frama_C_interval_32(0,4294967295) ;
    uint32_t ctxh = Frama_C_interval_32(0,4294967295);
    uint32_t handler = Frama_C_interval_32(0,4294967295);
    uint8_t ep = Frama_C_interval_8(0,255);
    uint8_t iface = Frama_C_interval_8(0,MAX_INTERFACES_PER_DEVICE-1);
    uint8_t ep_number = Frama_C_interval_8(0,MAX_EP_PER_INTERFACE);
    uint8_t EP_type = Frama_C_interval_8(0,3);
    uint8_t EP_dir = Frama_C_interval_8(0,1);
    uint8_t  USB_class = Frama_C_interval_8(0,17);
    uint32_t USBdci_handler = Frama_C_interval_32(0,4294967295) ;


    uint8_t RequestType = Frama_C_interval_8(0,255);
    uint8_t Request = Frama_C_interval_8(0,255);
    uint16_t Value = Frama_C_interval_16(0,65535);
    uint16_t Index = Frama_C_interval_16(0,65535);
    uint16_t Length = Frama_C_interval_16(0,65535);

    usbctrl_setup_pkt_t pkt = { .bmRequestType = RequestType, .bRequest = Request, .wValue = Value, .wIndex = Index, .wLength = Length };
    usbctrl_interface_t iface_1 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep,
                                  .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor};
    usbctrl_interface_t iface_2 = { .usb_class = USB_class, .usb_ep_number = ep_number, .dedicated = true,
                                  .eps[0].type = EP_type, .eps[0].dir = EP_dir, .eps[0].handler = handler_ep,
                                   .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor};

/*
    ctx_test : context different from ctx_list, to trigger some cases in get_handler
*/
    usbctrl_context_t ctx_test = { .dev_id = 8, .address= 2};

    /*
        usbctrl_declare : error case - null pointer ctxh null
                                       - num_ctx >= 2
    */

    uint32_t *bad_ctxh = NULL;
    usbctrl_declare(dev_id, bad_ctxh);

    ctxh = 1 ;
    num_ctx = 3;
    //@ ghost GHOST_num_ctx = num_ctx ;
    usbctrl_declare(dev_id, &ctxh);

    /*
        usbctrl_initialize : error case : ctxh >= num_ctx
    */

    ctxh = 0 ;
    num_ctx = 1 ;
    //@ ghost GHOST_num_ctx = num_ctx ;
    usbctrl_initialize(ctxh);


    ctxh = 5 ;
    usbctrl_initialize(ctxh);

    /*
        usbctrl_declare_interface : error case - ctxh >= num_ctx
                                                 - null pointer iface
                                                 - interface_num >= MAX_INTERFACES_PER_DEVICE
                                                 - pkt_maxsize > usbotghs_get_ep_mpsize()
    */


    ctxh = 2 ;
    num_ctx = 1 ;
    //@ ghost GHOST_num_ctx = num_ctx ;
    usbctrl_declare_interface(ctxh, &iface_1) ;

    ctxh = 0 ;
    num_ctx = 1 ;
    //@ ghost GHOST_num_ctx = num_ctx ;
    usbctrl_interface_t *iface_null = NULL ;
    usbctrl_declare_interface(ctxh, iface_null) ;

    usbctrl_interface_t iface_3 = {.usb_class = 0, .usb_ep_number = 2, .dedicated = true,
        .eps[0].type = 3, .eps[0].handler = handler_ep,  .eps[0].pkt_maxsize = MAX_EPx_PKT_SIZE + 1,
        .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor };
    ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE ;
    usbctrl_declare_interface(ctxh, &iface_3) ;

    usbctrl_interface_t iface_4 = {.usb_class = 0, .usb_ep_number = 2, .dedicated = false,
        .eps[0].type = 3, .eps[0].handler = handler_ep, .eps[0].pkt_maxsize = MAX_EPx_PKT_SIZE + 1,
        .rqst_handler = class_rqst_handler, .class_desc_handler = class_get_descriptor };
    ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE - 1 ;
    usbctrl_declare_interface(ctxh, &iface_4) ;




    /*
        usbctrl_get_interface : error case - null pointer ctx null
        case iface < ctx->cfg[ctx->curr_cfg].interface_num not reached in nominal case
    */
    usbctrl_context_t *bad_ctx = NULL ;
    usbctrl_get_interface(bad_ctx, iface);

    ctx_list[ctxh].cfg[0].interface_num = MAX_INTERFACES_PER_DEVICE ;
    usbctrl_get_interface((usbctrl_context_t *)&(ctx_list[ctxh]), iface);

    /*
        usbctrl_get_handler: error case - null pointer ctx null
                                           - null pointer handler null
    */

    usbctrl_get_handler(bad_ctx, &handler);
    usbctrl_get_handler(&ctx_test, &handler);


    /*
        usbctrl_get_context, usbctrl_is_endpoint_exists &&  usbctrl_is_interface_exists  : null pointer - pointeur ctx null
    */

    usbctrl_get_context(dev_id,     NULL);
    usbctrl_is_endpoint_exists(bad_ctx, ep);
    usbctrl_is_interface_exists(bad_ctx, iface);

    /*
        error case with ctx >= num_ctx
    */

    usbctrl_start_device(4) ;
    usbctrl_stop_device(4) ;

    /*
        error case on get_descriptor : reach all possible types, including false one
                                         pointeurs null
                                         ctx != ctx_list[i] for error_not_found in get_handler
    */

    uint8_t buf[255] = {0} ;
    uint32_t desc_size = 0 ;
    usbctrl_context_t ctx1 = {1} ;

    usbctrl_get_descriptor(9,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(USB_DESC_DEV_QUALIFIER,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(USB_DESC_OTHER_SPEED_CFG,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(USB_DESC_IFACE_POWER,&buf[0],&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(1,NULL,&desc_size,&ctx1, &pkt);
    usbctrl_get_descriptor(1,&buf[0],NULL,&ctx1, &pkt);
    usbctrl_get_descriptor(1,&buf[0],&desc_size,NULL, &pkt);
    usbctrl_get_descriptor(1,&buf[0],&desc_size,&ctx1, NULL);



/*
    test functions in usbctrl_state with null pointers or invalid state (>= 10)
*/

    usbctrl_get_state(NULL) ;
    usbctrl_set_state(&ctx1,10);
    usbctrl_set_state(NULL,10);


/*
    usbctrl_handle_class_requests : test with get_handler returning error not found
*/
usbctrl_context_t ctx2 = ctx_list[0] ;
ctx2.state = Frama_C_interval_8(0,9);
usbctrl_handle_class_requests(&pkt, &ctx2);

usbctrl_handle_requests(NULL, dev_id);


}

/*
    test for functions defined in driver USB (not all function analysed, only the functions needed for libxDCI)
    nominal and bad parameters

*/

void test_fcn_driver_eva(){

    uint8_t ep_id = Frama_C_interval_8(0,255);
    uint8_t ep_num = Frama_C_interval_8(0,255);
    uint8_t dir8 = Frama_C_interval_8(0,255);
    uint8_t dst = Frama_C_interval_8(0,255);
    uint32_t size = Frama_C_interval_32(0,4294967295);
    uint8_t fifo = Frama_C_interval_8(0,255);
    uint32_t fifo_idx = Frama_C_interval_32(0,4294967295);
    uint32_t fifo_size = Frama_C_interval_32(0,4294967295);
    usbotghs_epx_mpsize_t size_ep = Frama_C_interval_8(0,3);

    uint8_t src = 1 ;

    usbotghs_ep_dir_t dir = Frama_C_interval_8(0,1);
    usbotghs_ep_type_t type = Frama_C_interval_8(0,3);
    usbotghs_ep_state_t state = Frama_C_interval_8(0,9) ;
    usbotghs_dev_mode_t mode = Frama_C_interval_8(0,1);

    usbotghs_global_stall() ;
    usbotghs_endpoint_set_nak(ep_id, dir) ;
    usbotghs_global_stall_clear();
    usbotghs_endpoint_stall_clear(ep_id, dir);
    usbotghs_deconfigure_endpoint(ep_id);
    usbotghs_activate_endpoint(ep_id,dir);
    usbotghs_deactivate_endpoint( ep_id,dir);
    usbotghs_enpoint_nak( ep_id);
    usbotghs_enpoint_nak_clear( ep_id);
    usbotghs_endpoint_disable( ep_id,     dir);
    usbotghs_endpoint_enable( ep_id,     dir);
    usbotghs_endpoint_clear_nak(ep_id, dir) ;
    usbotghs_endpoint_stall(ep_id, dir) ;
    usbotghs_get_ep_state(ep_id, dir) ;

    usbotghs_ctx.in_eps[EP0].mpsize = Frama_C_interval_16(0,65535);
    uint8_t resp[1024] = { 0 };
    usbotghs_ctx.in_eps[EP0].fifo_lck = 1 ;
    usb_backend_drv_send_data((uint8_t *)&resp, size, EP0);
    usbotghs_ctx.in_eps[EP0].fifo_lck = 0 ;
    usb_backend_drv_send_data((uint8_t *)&resp, 514, EP0);
    usbotghs_ctx.in_eps[4].mpsize = Frama_C_interval_16(0,65535);
    usbotghs_ctx.in_eps[4].id = 4 ;
    usbotghs_ctx.in_eps[4].fifo_lck = 0 ;
    usbotghs_ctx.in_eps[4].configured = 1 ;
    usb_backend_drv_send_data((uint8_t *)&resp, size, 4);
    usb_backend_drv_send_data((uint8_t *)&resp, size, 8);
    usbotghs_send_zlp(ep_id);
    usbotghs_txfifo_flush(ep_id);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,64,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,128,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,512,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usb_backend_drv_configure_endpoint(ep_id,type,dir,1024,USB_BACKEND_EP_ODDFRAME,&handler_ep);
    usbotghs_configure(mode, & usbctrl_handle_inepevent,& usbctrl_handle_outepevent);
    usbotghs_set_recv_fifo((uint8_t *)&resp, size, 0);
    usbotghs_set_recv_fifo((uint8_t *)&resp, size, 1);

    /*
        TODO : send_data analyse is not enough generalised
    */

}

void main(void)
{

    test_fcn_usbctrl() ;
    test_fcn_usbctrl_erreur() ;
    test_fcn_driver_eva() ;

}
