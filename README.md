Device Controle plane for USB devices
-------------------------------------

Any USB 2.0 compliant device must implement a USB 2.0 control stack. THis control
stack interacts with the xHCI USB stack of the host, in order to negociate the
overall USB communication channel properties, speed, and to declare the device
capacities.

This control stack can be hard-coded or intelligent enough to support configuration
and interface registration (i.e. multiple USB interface over USB standard control plane),
defining an hybrid device, handling multiple USB classes and subclasses in the same time.

This library is designed in order to:
   - support any USB class and handle the corresponding stack registration easily
   - handling correctly the USB stack automaton without requiring complex action from
     upper level classes
   - supports one or more interfaces in the same time
   - support both high speed (USB 2.0) and full speed (USB 1.1) backend drivers and control plane

This library is full software and does not directly handle the hardware USB device.
This device is handled by a USB device driver with which this library interact in
order to handle the control plane properly. Though, this library handle the driver choice
and provide fast and efficient USB driver access abstraction to allow a complete portability of all USB classes implementations.


For more information on the library API, see the doc/ directory.
