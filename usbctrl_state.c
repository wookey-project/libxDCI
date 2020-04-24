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

#define MAX_TRANSITION_STATE 10

/*
 * Association between a request and a transition to a next state. This couple
 * depend on the current state and is use in the following structure
 */
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

/**********************************************
 * USB CTRL State automaton getters and setters
 *********************************************/

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


/*@
  @ requires \valid_read(ctx) ;
  @ requires is_valid_state(ctx->state) ;
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
  @ requires \valid(ctx) ;
  @ requires is_valid_state(newstate) ;
  @ assigns ctx->state ;
  @ ensures (ctx == \null) ==> (\result == MBED_ERROR_INVPARAM) ;
  @ ensures (newstate >= USB_DEVICE_STATE_INVALID ) ==> (\result == MBED_ERROR_INVPARAM) ;
  @ ensures (ctx != \null && newstate < USB_DEVICE_STATE_INVALID)  ==> (\result == MBED_ERROR_NONE && ctx->state == newstate) ;
*/

#if defined(__FRAMAC__)
mbed_error_t usbctrl_set_state(__out usbctrl_context_t *ctx,
                               __in usb_device_state_t newstate)
{
    /* FIXME: transient, maybe we need to lock here. */
   if (ctx == NULL) {
       return MBED_ERROR_INVPARAM;
   }
    if (newstate >= USB_DEVICE_STATE_INVALID) {
        //log_printf("[USBCTRL] invalid state transition !\n");
        return MBED_ERROR_INVPARAM;
    }
    //log_printf("[USBCTRL] changing from state %x to %x\n", ctx->state, newstate);
    ctx->state = newstate;

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
    if (newstate >= USB_DEVICE_STATE_INVALID) {
        //log_printf("[USBCTRL] invalid state transition !\n");
        return MBED_ERROR_INVPARAM;
    }
    //log_printf("[USBCTRL] changing from state %x to %x\n", ctx->state, newstate);
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
uint8_t usbctrl_next_state(usb_device_state_t current_state,
                           usbctrl_request_code_t request)
{
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
bool usbctrl_is_valid_transition(usb_device_state_t current_state,
                                 usb_device_trans_t transition,
                                 usbctrl_context_t *ctx)
{
    /*@
        @ loop unroll MAX_TRANSITION_STATE;
    */

    for (uint8_t i = 0; i < MAX_TRANSITION_STATE; ++i) {
        if (usb_automaton[current_state].req_trans[i].request == transition) {
            return true;
        }
    }
    /*
     * Didn't find any request associated to current state. This is not a
     * valid transition. We should stall the request.
     */
    log_printf("%s: invalid transition from state %d, request %d\n", __func__,
           current_state, transition);
    usbctrl_set_state(ctx, USB_DEVICE_STATE_INVALID);
    return false;
}
