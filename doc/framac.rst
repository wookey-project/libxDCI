libxDCI FramaC annotations
--------------------------


Functional proof state
----------------------

The following requests of the USB device control stack has function contracts that validate that their behaviors
are conform to the USB standard specification (functional contract):

   * Get_Configuration
   * Get_Status
   * Set_Address
   * Set_Configuration

Others requests and handlers (reset, wakeup, etc.), like the overall USB stack, have basic contracts (border effects) and are formallu checked as noRTE
