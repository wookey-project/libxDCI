.. _lib_usbctrl:


.. highlight:: c

The USB 2.0 Control stack
=========================

.. contents::

Overview
--------

Any USB 2.0 compliant device must implement a USB 2.0 control stack. This
control stack can be hard-coded or intelligent enough to support interface
registration (i.e. multiple USB device type over USB 2.0 standard control plane)

This library is designed in order to support such dynamicity.

This library is full software and does not directly handle the hardware USB device.
This device is handled by a USB device driver with which this library interact in
order to handle the control plane properly.

This library depends on the EwoK libstd.

The USBCtrl types and definitions
---------------------------------


The libUSBCtrl is reentrant and supports multiple devices in the same time. To handle this,
the library is using a *context*, which hold, for each device, all needed informations.

About USB Endpoints
"""""""""""""""""""

USB devices communicate through Endpoints. A endpoint is a communication pipe through
which data are transmitted.

A endpoint has a type (specifying the way data are formatted), a direction, and a
synchronization profile. An endpoint also has a usage::

   /*
    * USB Endpoint type
    */
   typedef enum {
      USB_EP_TYPE_CONTROL      = 0x00,
      USB_EP_TYPE_ISOCHRONOUS  = 0x01,
      USB_EP_TYPE_BULK         = 0x02,
      USB_EP_TYPE_INTERRUPT    = 0x03,
   } usb_ep_type_t;
   
   /*
    * USB Endpoint access mode
    */
   typedef enum {
       USB_EP_MODE_READ,
       USB_EP_MODE_WRITE,
       USB_EP_MODE_DATA /* e.g. DFU EP */
   } usb_ep_mode_t;
   
   /*
    * USB Endpoint attribute
    */
   typedef enum {
       USB_EP_ATTR_NO_SYNC     = 0x0,
       USB_EP_ATTR_ASYNC       = 0x1,
       USB_EP_ATTR_ADAPTATIVE  = 0x2,
       USB_EP_ATTR_SYNC        = 0x3,
   } usb_ep_attr_t;

   /*
    * USB Endpoint usage
    */
   typedef enum {
       USB_EP_USAGE_DATA               = 0x0,
       USB_EP_USAGE_FEEDBACK           = 0x1,
       USB_EP_USAGE_IMPLICIT_FEEDBACK  = 0x2,
   } usb_ep_usage_t;


To all these various attribute, some endpoint specific informations are also
defined: the maximum packet size supported by the endpoint (which may depends on
the hardware and the USB device class), and the endpoint unique identifier in the
device, which is dynamically set, depending on the other existing endpoints.

As a consequence, an endpoint structure is defined as the following::

   typedef struct {
       usb_ep_type_t    type;                  /* EP type */
       usb_ep_mode_t    mode;                  /* EP mode */
       usb_ep_attr_t    attr;                  /* EP attributes */
       usb_ep_usage_t   usage;                 /* EP usage */
       uint16_t         pkt_maxsize;           /* pkt maxsize in this EP */
       uint8_t          ep_num;                /* EP identifier */
   } usb_ep_infos_t;


About USB Interfaces
""""""""""""""""""""

A USB interface is the entity to which the host communicate through endpoints. A USB
interface respects a given USB Class, subclass and protocol (for example, a mass-storage
device is a USB MSC UMS Class, usually using SCSI reduced or transparent command set Subclass, and BBB (Mass-storage Bulk-Only) protocol. These three values are encoded on one byte and are standardized in the various USB Class specifications defined by the USB consortium.
In USB devices, interfaces can be handled synchronously, or separately. This depends on
interfaces constraints, which may be incompatible with each others. To do that, interfaces
are associated to *configuration*. A configuration is a set of interface which is active
at a given time. The host is responsible for requesting the list of valid configurations
from the device, and can request configuration schedule, in order to switch from a set
of interface(s) to another set of interface(s). The libUSBCtrl handle this.

In the libUSBCtrl, a USB interface definition:

    * defines the USB interface class, subclass and protocol
    * specify if the interface must be in a dedicated configuration (this will create a new configuration dedicated to it)
    * provide an interface request handler, to support *class requests*, which are host
      requests targeting the USB interface instead of the USB device control plane
    * a functional descriptor pointer. An interface may have a functional descriptor which
      specify a dedicated behavior to the host. This descriptor is specific to this interface and will be transmitted to the host by the libUSBCtrl
    * a list of endpoints associated to the interface, as defined above

The overall interface definition is the following::

   typedef struct {
      usb_class_t        usb_class;      /*< the standard USB Class */
      uint8_t            usb_subclass;   /*< interface subclass */
      uint8_t            usb_protocol;   /*< interface protocol */
      bool               dedicated;      /*< is the interface hosted in a dedicated configuration (not shared with others) ? */
      usb_rqst_handler_t rqst_handler;   /*< interface Requests handler */
      functional_descriptor_p func_desc; /*< pointer to functional descriptor, if it exists */
      uint8_t            func_desc_len;  /*< functional descriptor length (in byte)  */
      uint8_t            usb_ep_number;  /*< the number of EP associated */
      usb_ep_infos_t     eps[MAX_EP_PER_PERSONALITY];  /*< for each EP, the associated
                                                         informations */
   } usbctrl_interface_t;

About USB contexts
""""""""""""""""""

The libUSBCtrl handle, for each USB hardware block declared, a USB context. This context,
by default, only handle the USB default control pipe, which is common to any USB device.

Then, interfaces is added to the context, and the context can be launched, by fully
activating the device with the corresponding complete configuration.

Most of the context is hold by the libUSBCtrl. Only the link between the context and
the belowing device must be initiated by the caller.

The context definition is the following::


   typedef struct usbctrl_context {
       /* first, about device driver interactions */
       uint32_t                dev_id;             /*< device id, from the USB device driver */
       device_t                usb_dev;            /*< device_t structure for USB device driver */
       uint16_t               address;             /*< device address, to be set by std req */
       /* Then, about personalities (info, number) */
       uint8_t                interface_num;     /*< Number of personalities registered */
       usbctrl_interface_t    interfaces[MAX_INTERFACES_PER_DEVICE];     /*< For each registered interface,
                                                                           its associated infos */
       uint8_t                 num_cfg;        /*< number of different onfigurations */
       uint8_t                 curr_cfg;       /*< current configuration (starting with 1) */
       /* then current context state, associated to the USB standard state automaton  */
       uint8_t                 state;              /*< USB state machine current state */
   } usbctrl_context_t;


The context:

   * is associated to a unique USB device associated to its device identifier and its *device_t* structure passed to the driver.
   * holds an address field, which is associated to the *set_address* standard request and is managed by the libUSBCtrl.
   * holds the number of different configurations, and the current configuration identifier
   * holds the state of the standard USB 2.0 state automaton


The USBCtrl functional API
--------------------------

TODO: update text which is based on comments 

Declaring a USB context
"""""""""""""""""""""""

Declare the USB device through the ctrl interface, get back, for the current context,
the associated device identifier in ctx. This part handling the device part only ::

   mbed_error_t usbctrl_declare(usbctrl_context_t*ctx);

Initialize a USB context
""""""""""""""""""""""""

create the first USB context, and create endpoint 0 for default
control pipe. Other EPs need to be registered by other libs (bulk, HID, and so on)
The USB state machine is also initialized

Initialization *does not* touch the device. It only handle the local USB context.
The context is mapped to the device when requesting device start.
This permits to declare multiple classes/personalities before starting the device and
receiving the first requests from the host ::

   mbed_error_t usbctrl_initialize(usbctrl_context_t*ctx);

Manipulate the USB device
"""""""""""""""""""""""""

Bind the device to the task, if not mapped (ask the driver to map)::

   mbed_error_t usbctrl_bind(usbctrl_context_t*ctx);

Unmap the device, if mapped (ask the driver to unmap) ::

   mbed_error_t usbctrl_unbind(usbctrl_context_t*ctx);

Definitively release the device (ask the driver to release) ::

   mbed_error_t usbctrl_release(usbctrl_context_t*ctx);


Declare a new interface
"""""""""""""""""""""""

Declare a new USB interface. Endpoints are created, EP refs are set in
the interface context. Interface is associated to the context.

At interface declaration, all needed information to generate the associated
full descriptors is given. Each interface descriptor can be created by the
libusbctrl itself, as a consequence (see above).

At interface declaration time, interface endpoints infos are updated
(EP identifiers, etc.) depending on the current global device interface state::

   mbed_error_t usbctrl_declare_interface(__in      usbctrl_context_t   *ctx,
                                          __out    usbctrl_interface_t  *up);


Start the device
""""""""""""""""

bind and enable the device, initialize the communication and wait for the
initial requests from the host.
Current configuration is configuration 1 by default. The host can switch after.

By now, it is not possible to declare new personalities *after* the device is started.::

   mbed_error_t usbctrl_start_device(usbctrl_context_t      *ctx);


