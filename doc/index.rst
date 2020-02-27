.. _lib_usbctrl:


.. highlight:: c

The USB 2.0 Control stack
=========================

.. contents::

Overview
--------

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

This library is full software and does not directly handle the hardware USB device.
This device is handled by a USB device driver with which this library interact in
order to handle the control plane properly. Though, this library handle the driver choice
and provide fast and efficient USB driver access abstraction to allow a complete portability of all USB classes implementations.

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

An USB endpoint is a half-duplex communication pipe, which can receive (or send) data.
It can also handle handshaking (whatever its direction is) to acknowledge transfer states.

In order to handle a transfer even on an endpoint, a handle need to be executed:

   - In OUT mode (host centric, when the device is receiving data on the endpoint), the handler is triggered when the data has been received into the previously configured endpoint FIFO
   - In IN mode (host centric, when the device is sending data using the endpoint), the handler is triggered when the data has been fully sent to the host, from the previously configured FIFO

In both direction, this handler is responsible for trigger a new packet reception or to trigger a end of packet transmission.

This trigger is using the following prototypes::

   typedef mbed_error_t (*usb_ioep_handler_t)(uint32_t dev_id,
                                              uint32_t size,
                                              uint8_t  ep_id);

As a consequence, an endpoint structure is defined as the following::

   typedef struct {
       usb_ep_type_t    type;                  /* EP type */
       usb_ep_dir_t     dir;                   /* EP direction */
       usb_ep_attr_t    attr;                  /* EP attributes */
       usb_ep_usage_t   usage;                 /* EP usage */
       uint16_t         pkt_maxsize;           /* pkt maxsize in this EP */
       usb_ioep_handler_t handler;             /* EP handler */
       uint8_t          ep_num;                /* EP identifier */
       bool             configured;            /* EP enable in current config */
   } usb_ep_infos_t;


About USB Interfaces
""""""""""""""""""""

A USB interface is the entity to which the host communicate through endpoints. A USB
interface respects a given USB Class, subclass and protocol (for example, a mass-storage
device is a USB MSC UMS Class, usually using SCSI reduced or transparent command set Subclass, and BBB (Mass-storage Bulk-Only) protocol. These three values are encoded on one byte and are standardized in the various USB Class specifications defined by the USB consortium.
In USB devices, interfaces can be handled synchronously, or separately. This depends on
interfaces constraints, which may be incompatible with each others. To do that, interfaces
are associated to *configurations*. A configuration is a set of interface which is active
at a given time. The host is responsible for requesting the list of valid configurations
from the device, and can request configuration schedule, in order to switch from a set
of interface(s) to another set of interface(s). The libUSBCtrl handle this.

In the libUSBCtrl, a USB interface definition:

    * defines the USB interface class, subclass and protocol
    * specify if the interface must be in a dedicated configuration (this will create a new configuration dedicated to it)
    * provide an interface request handler, to support *class requests*, which are host
      requests targeting the USB interface instead of the USB device control plane
    * a class descriptor provider, if the class handle a class descriptor. If this provider is given, the class descriptor is added just after the interface descriptor in the configuration descriptor
    * a list of endpoints associated to the interface, as defined above

The overall interface definition is the following::

   typedef struct {
      usb_class_t        usb_class;      /*< the standard USB Class */
      uint8_t            usb_subclass;   /*< interface subclass */
      uint8_t            usb_protocol;   /*< interface protocol */
      bool               dedicated;      /*< is the interface hosted in a dedicated configuration (not shared with others) ? */
      usb_rqst_handler_t rqst_handler;   /*< interface Requests handler */
      usb_class_get_descriptor_handler_t class_desc_handler; /* class level descriptor getter */
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

In the libUSBCtrl, interfaces are hold in a configuration structure. The context hold
multiple configurations::


   typedef struct {
       uint8_t                first_free_epid;   /* first free EP identifier (starting with 1, as 0 is control) */
       uint8_t                interface_num;     /*< Number of personalities registered */
       usbctrl_interface_t    interfaces[MAX_INTERFACES_PER_DEVICE];     /*< For each registered interface */
   } usbctrl_configuration_t;


Most of the context is hold by the libUSBCtrl. Only the link between the context and
the belowing device must be initiated by the caller.

The context definition is the following::


   typedef struct usbctrl_context {
       /* first, about device driver interactions */
       uint32_t               dev_id;              /*< device id, from the USB device driver */
       uint16_t               address;             /*< device address, to be set by std req */
       /* then current context state, associated to the USB standard state automaton  */
       uint8_t                 num_cfg;        /*< number of different onfigurations */
       uint8_t                 curr_cfg;       /*< current configuration */
       usbctrl_configuration_t cfg[CONFIG_USBCTRL_MAX_CFG]; /* configurations list */
       uint8_t                 state;          /*< USB state machine current state */
       uint8_t                 ctrl_fifo[CONFIG_USBCTRL_EP0_FIFO_SIZE]; /* RECV FIFO for EP0 */
       bool                    ctrl_fifo_state; /*< RECV FIFO of control plane state */
       volatile bool           ctrl_req_processing; /* a control level request is being processed */
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

Here is a typical interface declaration for a USB MSC (Mass Storage Class) device::

    usbctrl_interface_t iface = { 0 };

    iface.usb_class = USB_CLASS_MSC_UMS;
    iface.usb_subclass = 0x6; /* SCSI transparent cmd set (i.e. use INQUIRY) */
    iface.usb_protocol = 0x50; /* Protocol BBB (Bulk only) */
    iface.dedicated = false;
    iface.rqst_handler = mass_storage_class_rqst_handler;
    iface.class_desc_handler = NULL;
    iface.usb_ep_number = 2;

    iface.eps[0].type        = USB_EP_TYPE_BULK;
    iface.eps[0].dir         = USB_EP_DIR_OUT;
    iface.eps[0].attr        = USB_EP_ATTR_NO_SYNC;
    iface.eps[0].usage       = USB_EP_USAGE_DATA;
    iface.eps[0].pkt_maxsize = 512; /* mpsize on EP1 */
    iface.eps[0].ep_num      = 1; /* this may be updated by libctrl */
    iface.eps[0].handler     = usb_bbb_data_received;

    iface.eps[1].type        = USB_EP_TYPE_BULK;
    iface.eps[1].dir         = USB_EP_DIR_IN;
    iface.eps[1].attr        = USB_EP_ATTR_NO_SYNC;
    iface.eps[1].usage       = USB_EP_USAGE_DATA;
    iface.eps[1].pkt_maxsize = 512; /* mpsize on EP2 */
    iface.eps[1].ep_num      = 2; /* this may be updated by libctrl */
    iface.eps[1].handler     = usb_bbb_data_sent;


    usbctrl_declare_interface(ctx, &iface);


Start the device
""""""""""""""""

bind and enable the device, initialize the communication and wait for the
initial requests from the host.
Current configuration is configuration 1 by default. The host can switch after.

By now, it is not possible to declare new personalities *after* the device is started.::

   mbed_error_t usbctrl_start_device(usbctrl_context_t      *ctx);


USB driver abstraction
""""""""""""""""""""""

Introduction
^^^^^^^^^^^^

The libUSBCtrl is handling a complete USB driver abstraction for all upper stack. This abstraction execute
the effective driver API, which may vary a little (starting with its name) from a driver to another. Although
these actions are generic to any driver and USB stack implementation::

   mbed_error_t usb_backend_drv_endpoint_clear_nak(uint8_t                  ep_id,
                                                   usb_backend_drv_ep_dir_t dir);

   mbed_error_t usb_backend_drv_endpoint_set_nak(uint8_t                  ep_id,
                                                 usb_backend_drv_ep_dir_t dir);

   mbed_error_t usb_backend_drv_endpoint_stall(uint8_t                  ep_id,
                                               usb_backend_drv_ep_dir_t dir);

   mbed_error_t usb_backend_drv_get_ep_state(uint8_t                  ep_id,
                                             usb_backend_drv_ep_dir_t dir);

   mbed_error_t usb_backend_drv_send_data(uint8_t  *src,
                                          uint32_t  size,
                                          uint8_t   ep);

   mbed_error_t usb_backend_drv_send_zlp(uint8_t  ep);

   mbed_error_t usb_backend_drv_set_recv_fifo(uint8_t  *dst,
                                              uint32_t  size,
                                              uint8_t   ep);


Sending and receiving packets
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Sending data on a IN Endpoint is done with the following API::

   usb_backend_drv_send_data

At that time, the data is not yet sent, the IN Endpoint handler declared at inteface declaration time is
triggered when the data is sent to the host.

Receiving a packet on a OUT Endpoint::

   usb_backend_drv_set_recv_fifo
   usb_backend_drv_endpoint_clear_nak

Again, at this time, no data is received yet. The OUT Endpoint handler will be triggered as soon as
a transfer complete is received on the corresponding endpoint, informing the application that data
has been received.

Handling handshake and control flow
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To inform the USB host that the EP is free to receive new data (previous data has been successively consumed),
the data should be acknowledge. acknowledgement is per-endpoint. This is done with::

   usb_backend_drv_endpoint_clear_nak

To inform the USB host that the data received was not handled correctly (corruption or failure), a NAK must
be sent to the host. This is done using::

   usb_backend_drv_endpoint_set_nak

There is cases when the host is using ZLP (Zero-length-Packet, a transfer of 0 bytes) acknowledgement, using as a ACK
to a received data content, informing the host that the data has been processed correctly.
This is done using::

   usb_backend_drv_send_zlp



