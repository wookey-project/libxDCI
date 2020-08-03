#include "libc/types.h"
#include "libc/stdio.h"
#include "usbctrl.h"
#include "usbctrl_state.h"
#include "usbctrl_requests.h"

/*
 * all allowed transitions and target states for each current state
 * empty fields are set as 0xff/0xff for request/state couple, which is
 * an inexistent state and request
 *
 * This table associate each state of the DFU automaton with up to
 * 5 potential allowed transitions/next_state couples. This permit to
 * easily detect:
 *    1) authorized transitions, based on the current state
 *    2) next state, based on the current state and current transition
 *
 * If the next_state for the current transision is keeped to 0xff, this
 * means that the current transition for the current state may lead to
 * multiple next state depending on other informations. In this case,
 * the transition handler has to handle this manually.
 */


#if defined(__FRAMAC__)
 // CYRIL : ce qu'il y a dans le #else est reporté dans le .h, dans un if defined(__FRAMAC__). Car les variables déclarées dans les .c sont ignorées par frama dans les autres .c...
#else

/*
 * Association between a request and a transition to a next state. This couple
 * depend on the current state and is use in the following structure
 */


#define MAX_TRANSITION_STATE 10
typedef struct usb_operation_code_transition {
    uint8_t request;
    uint8_t target_state;
} usb_request_code_transition_t;


static const struct {
    usb_device_state_t state;
    usb_request_code_transition_t   req_trans[MAX_TRANSITION_STATE];
} usb_automaton[] = {
    {USB_DEVICE_STATE_ATTACHED, {
                 {USB_DEVICE_TRANS_HUB_CONFIGURED, USB_DEVICE_STATE_POWERED},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 {0xff, 0xff},
                 }
     },
    {USB_DEVICE_STATE_POWERED, {
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_POWER},
                  {USB_DEVICE_TRANS_HUB_RESET, USB_DEVICE_STATE_ATTACHED},
                  {USB_DEVICE_TRANS_HUB_DECONFIGURED, USB_DEVICE_STATE_ATTACHED},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                 }
     },
    {USB_DEVICE_STATE_SUSPENDED_POWER, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_POWERED},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_SUSPENDED_DEFAULT, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_DEFAULT},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_SUSPENDED_ADDRESS, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_ADDRESS},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_SUSPENDED_CONFIGURED, {
                  {USB_DEVICE_TRANS_BUS_ACTIVE, USB_DEVICE_STATE_CONFIGURED},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  }
     },
    {USB_DEVICE_STATE_DEFAULT, {
                  {USB_DEVICE_TRANS_ADDRESS_ASSIGNED, USB_DEVICE_STATE_ADDRESS},
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_DEFAULT},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },
    {USB_DEVICE_STATE_ADDRESS, {
                  {USB_DEVICE_TRANS_DEV_CONFIGURED, USB_DEVICE_STATE_CONFIGURED},
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_ADDRESS},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },
    {USB_DEVICE_STATE_CONFIGURED, {
                  {USB_DEVICE_TRANS_DEV_DECONFIGURED, USB_DEVICE_STATE_ADDRESS},
                  {USB_DEVICE_TRANS_BUS_INACTIVE, USB_DEVICE_STATE_SUSPENDED_CONFIGURED},
                  {USB_DEVICE_TRANS_RESET, USB_DEVICE_STATE_DEFAULT},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },
    {USB_DEVICE_STATE_INVALID, {
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  {0xff, 0xff},
                  },
     },

};

#endif/*__FRAMAC__*/

/**********************************************
 * USB CTRL State automaton getters and setters
 *********************************************/


/*@
  @ assigns \nothing ;
  @ ensures (ctx == \null) ==> \result == USB_DEVICE_STATE_INVALID ;
  @ ensures (ctx != \null) ==> \result == ctx->state ;
*/

usb_device_state_t usbctrl_get_state(const usbctrl_context_t *ctx)
{
   if (ctx == NULL) {
       return USB_DEVICE_STATE_INVALID;
   }
   return ctx->state;
}

/*
 * This function is eligible in both main thread and ISR
 * mode (through trigger execution). Please use aprintf only
 * here.
 */

/*@
  @ assigns ctx->state ;
  @ ensures (ctx == \null) ==> (\result == MBED_ERROR_INVPARAM) ;
  @ ensures (newstate > USB_DEVICE_STATE_INVALID ) ==> (\result == MBED_ERROR_INVPARAM) ;
  @ ensures (ctx != \null && is_valid_state(ctx->state) && newstate <= USB_DEVICE_STATE_INVALID)  ==> (\result == MBED_ERROR_NONE && ctx->state == newstate) ;
*/

#if defined(__FRAMAC__)
mbed_error_t usbctrl_set_state(__out usbctrl_context_t *ctx,
                               __in usb_device_state_t newstate)
{
    /* FIXME: transient, maybe we need to lock here. */
   if (ctx == NULL) {
       return MBED_ERROR_INVPARAM;
   }
    if (newstate > USB_DEVICE_STATE_INVALID) {
        log_printf("[USBCTRL] invalid state transition !\n");
        return MBED_ERROR_INVPARAM;
    }
    log_printf("[USBCTRL] changing from state %x to %x\n", ctx->state, newstate);
    ctx->state = newstate;

      /* assert ctx->state == newstate; */

    return MBED_ERROR_NONE;
}
#else
mbed_error_t usbctrl_set_state(__out volatile usbctrl_context_t *ctx,
                               __in usb_device_state_t newstate)
{
    /* FIXME: transient, maybe we need to lock here. */
   if (ctx == NULL) {
       return MBED_ERROR_INVPARAM;
   }
    if (newstate > USB_DEVICE_STATE_INVALID) {
        log_printf("[USBCTRL] invalid state transition !\n");
        return MBED_ERROR_INVPARAM;
    }
    log_printf("[USBCTRL] changing from state %x to %x\n", ctx->state, newstate);
    ctx->state = newstate;

    return MBED_ERROR_NONE;
}
#endif/*!__FRAMAC__*/



/******************************************************
 * USBCTRL automaton management function (transition and
 * state check)
 *****************************************************/

/*!
 * \brief return the next automaton state
 *
 * The next state is returned depending on the current state
 * and the current request. In some case, it can be 0xff if multiple
 * next states are possible.
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return the next state, or 0xff
 */

/*@
  @ requires is_valid_state(current_state);
  @ requires is_valid_request_code(request);
  @ assigns \nothing ;
  @ ensures (\forall integer i; 0 <= i < MAX_TRANSITION_STATE ==> usb_automaton[current_state].req_trans[i].request != request)
            ==> \result == 0xff ;
  @ ensures (\result != 0xff) ==> \exists integer i; 0 <= i < MAX_TRANSITION_STATE && usb_automaton[current_state].req_trans[i].request == request
            && \result == usb_automaton[current_state].req_trans[i].target_state ;
*/

uint8_t usbctrl_next_state(usb_device_state_t current_state,
                           usbctrl_request_code_t request)
{

  /*@
      @ loop invariant 0 <= i <= MAX_TRANSITION_STATE ;
      @ loop invariant \valid_read(usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)));
      @ loop invariant (\forall integer prei ; 0 <= prei < i ==> usb_automaton[current_state].req_trans[prei].request != request) ;
      @ loop assigns i ;
      @ loop variant MAX_TRANSITION_STATE -i ;
  */

    for (uint8_t i = 0; i < MAX_TRANSITION_STATE; ++i) {
        if (usb_automaton[current_state].req_trans[i].request == request) {
            return (usb_automaton[current_state].req_trans[i].target_state);
        }
    }
    /* fallback, no corresponding request found for  this state */
    return 0xff;
}

/*!
 * \brief Specify if the current request is valid for the current state
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return true if the transition request is allowed for this state, or false
 */

/*@
    @ requires \valid(ctx);
    @ requires is_valid_state(current_state) ;
    @ requires is_valid_transition(transition);
    @ requires \valid_read(GHOST_usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)));
    @ requires \separated(GHOST_usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)),ctx);
    @ requires \separated(usb_automaton+(..),ctx+(..));
    @ assigns ctx->state;
    @ ensures \result == \true ==> (\exists integer i ; 0 <= i < MAX_TRANSITION_STATE && GHOST_usb_automaton[current_state].req_trans[i].request == transition)&&(ctx->state == \at(ctx->state, Pre) );
    @ ensures \result != \true ==> (\forall integer i ; 0 <= i < MAX_TRANSITION_STATE ==> GHOST_usb_automaton[current_state].req_trans[i].request != transition ) && (ctx->state == USB_DEVICE_STATE_INVALID);
    @ ensures \result == \true && transition == USB_DEVICE_TRANS_RESET ==>
                      (ctx->state == \at(ctx->state, Pre)) && !(current_state == USB_DEVICE_STATE_INVALID
                                                        || current_state == USB_DEVICE_STATE_SUSPENDED_POWER
                                                        || current_state == USB_DEVICE_STATE_ATTACHED)   ;
    @ ensures \result == \false && transition == USB_DEVICE_TRANS_RESET ==>
        (current_state == USB_DEVICE_STATE_INVALID || current_state == USB_DEVICE_STATE_SUSPENDED_POWER || current_state == USB_DEVICE_STATE_ATTACHED)   ;

*/
// PMO trop precis ici faux dans le cas général
/*
 @ behavior true:
    @   assumes \exists integer i ; 0 <= i < MAX_TRANSITION_STATE && usb_automaton[current_state].req_trans[i].request == transition ;
    @   assigns \nothing ;
    @   ensures \result == \true ;

    @ behavior false:
    @   assumes \forall integer i ; 0 <= i < MAX_TRANSITION_STATE ==> usb_automaton[current_state].req_trans[i].request != transition ;
    @   assigns ctx->state;
    @   ensures \result == \false  ;
    @   ensures ctx->state == USB_DEVICE_STATE_INVALID  ;


    @ complete behaviors ;
    @ disjoint behaviors ;
*/

bool usbctrl_is_valid_transition(usb_device_state_t current_state,
                                 usb_device_trans_t transition,
                                 usbctrl_context_t *ctx)
{
  /*@
      @ loop invariant 0 <= i <= MAX_TRANSITION_STATE ;
      @ loop invariant \valid_read(usb_automaton[current_state].req_trans + (0..(MAX_TRANSITION_STATE -1)));
      @ loop invariant (\forall integer prei ; 0 <= prei < i ==> usb_automaton[current_state].req_trans[prei].request != transition) ;
      @ loop assigns i ;
      @ loop variant MAX_TRANSITION_STATE -i ;
  */

    for (uint8_t i = 0; i < MAX_TRANSITION_STATE; ++i) {
        if (usb_automaton[current_state].req_trans[i].request == transition) {
          /*@ assert is_valid_state(current_state) ; */
          /*@ assert (transition == USB_DEVICE_TRANS_RESET) ==> !(current_state == USB_DEVICE_STATE_INVALID
                                                        || current_state == USB_DEVICE_STATE_SUSPENDED_POWER
                                                        || current_state == USB_DEVICE_STATE_ATTACHED) ; */
          /*@ assert current_state != USB_DEVICE_STATE_INVALID ; */
          /*@ assert ctx->state ==\at(ctx->state, Pre); */
            return true;
        }
    }
    /*
     * Didn't find any request associated to current state. This is not a
     * valid transition. We should stall the request.
     */
    log_printf("%s: invalid transition from state %d, request %d\n", __func__, current_state, transition);

    /*@ assert (transition == USB_DEVICE_TRANS_RESET) ==> (current_state == USB_DEVICE_STATE_INVALID
                                                        || current_state == USB_DEVICE_STATE_SUSPENDED_POWER
                                                        || current_state == USB_DEVICE_STATE_ATTACHED) ; */

    usbctrl_set_state(ctx, USB_DEVICE_STATE_INVALID);
    /*@ assert ctx->state ==  USB_DEVICE_STATE_INVALID; */

    return false;
}
