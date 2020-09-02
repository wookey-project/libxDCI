###################################################################
# About the library name and path
###################################################################

# library name, without extension
LIB_NAME ?= libusbctrl

# project root directory, relative to app dir
PROJ_FILES = ../../

# library name, with extension
LIB_FULL_NAME = $(LIB_NAME).a

# SDK helper Makefiles inclusion
-include $(PROJ_FILES)/m_config.mk
-include $(PROJ_FILES)/m_generic.mk

# use an app-specific build dir
APP_BUILD_DIR = $(BUILD_DIR)/libs/$(LIB_NAME)

###################################################################
# About the compilation flags
###################################################################

CFLAGS := $(LIBS_CFLAGS)
# libtoken needs libecc
CFLAGS += $(EXTERNAL_CFLAGS) $(LIBSIGN_CFLAGS)
CFLAGS += -Iapi
CFLAGS += -MMD -MP -O2 -std=gnu11

#############################################################
# About library sources
#############################################################

SRC_DIR = .
ALLSRC = $(wildcard $(SRC_DIR)/*.c)
SRC = $(filter-out $(SRC_DIR)/usbctrl_frama.c,$(ALLSRC))

# two build types: separated FW and DFU featureset, or single global featureset.
# This build type is controlled by USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD flag.
# In case of separated build, all objects, deps and libary files are written
# in dfu/ and fw/ subdirectories, and the current makefile build two independent
# libraries, with a differenciate additional cflag to detect DFU build: -DMODE_DFU
ifeq (y,$(CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD))
OBJ_FW = $(patsubst %.c,$(APP_BUILD_DIR)/fw/%.o,$(SRC))
OBJ_DFU = $(patsubst %.c,$(APP_BUILD_DIR)/dfu/%.o,$(SRC))
DEP_FW = $(OBJ_FW:.o=.d)
DEP_DFU = $(OBJ_DFU:.o=.d)
else
OBJ = $(patsubst %.c,$(APP_BUILD_DIR)/%.o,$(SRC))
DEP = $(OBJ:.o=.d)
endif


OUT_DIRS = $(dir $(OBJ))

# file to (dist)clean
# objects and compilation related
ifeq (y,$(CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD))
TODEL_CLEAN += $(OBJ_FW) $(OBJ_DFU)
else
TODEL_CLEAN += $(OBJ)
endif
# targets
TODEL_DISTCLEAN += $(APP_BUILD_DIR)

##########################################################
# generic targets of all libraries makefiles
##########################################################

.PHONY: app doc

default: all

ifeq (y,$(CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD))
all: $(APP_BUILD_DIR)  $(APP_BUILD_DIR)/dfu $(APP_BUILD_DIR)/fw lib
else
all: $(APP_BUILD_DIR) lib
endif

doc:
	$(Q)$(MAKE) BUILDDIR=../$(APP_BUILD_DIR)/doc  -C doc html latexpdf

show:
	@echo
	@echo "\tAPP_BUILD_DIR\t=> " $(APP_BUILD_DIR)
	@echo
	@echo "C sources files:"
	@echo "\tSRC_DIR\t\t=> " $(SRC_DIR)
	@echo "\tSRC\t\t=> " $(SRC)
ifeq (y,$(CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD))
	@echo "\tOBJ_FW\t\t=> " $(OBJ_FW)
	@echo "\tOBJ_DFU\t\t=> " $(OBJ_DFU)
else
	@echo "\tOBJ\t\t=> " $(OBJ)
endif
	@echo

ifeq (y,$(CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD))
lib: $(APP_BUILD_DIR)/dfu/$(LIB_FULL_NAME) $(APP_BUILD_DIR)/fw/$(LIB_FULL_NAME)
else
lib: $(APP_BUILD_DIR)/$(LIB_FULL_NAME)
endif

$(APP_BUILD_DIR):
	$(call cmd,mkdir)


ifeq (y,$(CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD))
# differenciated build

# make supplementary dirs
$(APP_BUILD_DIR)/fw:
	$(call cmd,mkdir)

$(APP_BUILD_DIR)/dfu:
	$(call cmd,mkdir)

# fw build
$(APP_BUILD_DIR)/fw/%.o: %.c
	$(call if_changed,cc_o_c)

# fw ranlib
$(APP_BUILD_DIR)/fw/$(LIB_FULL_NAME): $(OBJ_FW)
	$(call if_changed,mklib)
	$(call if_changed,ranlib)


# dfu build
$(APP_BUILD_DIR)/dfu/%.o: CFLAGS += -DMODE_DFU
$(APP_BUILD_DIR)/dfu/%.o: %.c
	$(call if_changed,cc_o_c)

# dfu ranlib
$(APP_BUILD_DIR)/dfu/$(LIB_FULL_NAME): $(OBJ_DFU)
	$(call if_changed,mklib)
	$(call if_changed,ranlib)


# deps files
-include $(DEP_FW)
-include $(DEP_DFU)

else
# undifferenciated FW/DFU build

# build
$(APP_BUILD_DIR)/%.o: %.c
	$(call if_changed,cc_o_c)

# ranlib
$(APP_BUILD_DIR)/$(LIB_FULL_NAME): $(OBJ)
	$(call if_changed,mklib)
	$(call if_changed,ranlib)

# deps files
-include $(DEP)

endif

#####################################################################
# Frama-C
#####################################################################

# This variable is to be overriden by local shell environment variable to
# compile and use frama-C targets
# by default, FRAMAC target is deactivated, it can be activated by overriding
# the following variable value with 'y' in the environment.
FRAMAC_TARGET ?= n

ifeq (y,$(FRAMAC_TARGET))

# some FRAMAC arguments may vary depending on the FRAMA-C version (Calcium, Scandium...)
# Here we support both Calcium (20) and Scandium (21) releases
FRAMAC_VERSION=$(shell frama-c -version|cut -d'.' -f 1)
FRAMAC_RELEASE=$(shell frama-c -version|sed -re 's:^.*\((.*)\)$:\1:g')

#
# INFO: Using Frama-C, the overall flags are not directly used as they are targetting
# arm-none-eabi architecture which is not handled by framaC. Instead, we used
# a 32bits target with custom CFLAGS to handle Frama-C compilation step.
# As a consequence, include paths need to be set here as above CFLAGS are dissmissed.
# Below variables are used to handle Wookey SDK in-tree vs out-of-tree Frama-C compilation,
# which permits to:
# - run Frama-C on an autonomous extract of the overall Wookey firmware, out of the Wookey SDK tree
# - run Frama-C directly in the SDK tree, on the same set of software
# The difference is mostly the dependencies paths. The advantage of such an effort is
# to simplify the begining of the Frama-C integration, by detecting and including the necessary
# dependencies only. In a second step only, the dependencies, if they are anotated or updated,
# are pushed back to their initial position in their initial repositories.
# For libxDCI, the dependencies are:
# - the USB device driver (we have chosen the USB OTG HS (High Speed) driver
# - the libstd, which is the tiny libc implementation of the Wookey environment, including the
#   userspace part of the syscalls.
# - some generated headers associated to the target plateform associated to the driver
# - EwoK kernel exported headers

# dir of USBOTG-HS sources (direct compilation from here bypassing local Makefile)
# this path is using the Wookey repositories structure hierarchy. Another hierarchy
# can be used by overriding this variable in the environment.
USBOTGHS_DIR ?= $(PROJ_FILES)/drivers/socs/$(SOC)/usbotghs

# This is the device specification header path generated by the Wookey SDK JSON layout.
# The following variable is using the standard Wookey SDK directories structure but
# can be overriden in case of out of tree execution.
# This directory handle both device specifications and devlist header (per device
# unique identifier table).
# INFO: this directory MUST contains a subdir named "generated" which contains these
# two files.
USBOTGHS_DEVHEADER_PATH ?= $(PROJ_FILES)/layouts/boards/wookey

# This is the Wookey micro-libC API directory. This directory is used by all libraries and driver
# and defines all prototypes and C types used nearly everywhere in the Wookey project.
LIBSTD_API_DIR ?= $(PROJ_FILES)/libs/std/api

# This is the EwoK kernel exported headers directory. These headers are requested by the libstd
# itself and thus by upper layers, including drivers and libraries.
EWOK_API_DIR ?= $(PROJ_FILES)/kernel/src/C/exported

SESSION     := framac/results/frama-c-rte-eva-wp-ref.session
EVA_SESSION := framac/results/frama-c-rte-eva.session
TIMESTAMP   := framac/results/timestamp-calcium_wp-eva.txt
JOBS        := $(shell nproc)
# Does this flag could be overriden by env (i.e. using ?=)
TIMEOUT     := 15

FRAMAC_GEN_FLAGS:=\
			-absolute-valid-range 0x40040000-0x40044000 \
			-no-frama-c-stdlib \
	        -warn-left-shift-negative \
	        -warn-right-shift-negative \
	        -warn-signed-downcast \
	        -warn-signed-overflow \
	        -warn-unsigned-downcast \
	        -warn-unsigned-overflow \
	        -warn-invalid-pointer \
			-kernel-msg-key pp \
			-cpp-extra-args="-nostdinc -I framac/include -I $(LIBSTD_API_DIR) -I $(USBOTGHS_DIR) -I $(USBOTGHS_DEVHEADER_PATH) -I $(EWOK_API_DIR)"  \
		    -rte \
		    -instantiate

FRAMAC_EVA_FLAGS:=\
		    -eva \
		    -eva-show-perf \
		    -eva-slevel 500 \
		    -eva-domains symbolic-locations\
		    -eva-domains equality \
		    -eva-split-return auto \
		    -eva-partition-history 3 \
		    -eva-use-spec usbctrl_reset_received \
		    -eva-use-spec class_rqst_handler \
		    -eva-use-spec handler_ep \
		    -eva-use-spec class_get_descriptor \
		    -eva-log a:frama-c-rte-eva.log

FRAMAC_WP_FLAGS:=\
	        -wp \
  			-wp-model "Typed+ref+int" \
  			-wp-literals \
  			-wp-prover alt-ergo,cvc4,z3 \
   			-wp-timeout $(TIMEOUT) \
			-wp-smoke-tests \
			-wp-no-smoke-dead-code \
   			-wp-log a:frama-c-rte-eva-wp.log


frama-c-parsing:
	frama-c framac/entrypoint.c usbctrl*.c $(USBOTGHS_DIR)/usbotghs.c $(USBOTGHS_DIR)/usbotghs_fifos.c \
		 -c11 \
		 -no-frama-c-stdlib \
		 -cpp-extra-args="-nostdinc -I framac/include -I $(LIBSTD_API_DIR) -I $(USBOTGHS_DIR) -I $(USBOTGHS_DEVHEADER_PATH) -I $(EWOK_API_DIR)"

frama-c-eva:
	frama-c framac/entrypoint.c usbctrl*.c $(USBOTGHS_DIR)/usbotghs.c $(USBOTGHS_DIR)/usbotghs_fifos.c -c11 \
		    $(FRAMAC_GEN_FLAGS) \
			$(FRAMAC_EVA_FLAGS) \
			-save $(EVA_SESSION)

frama-c:
	frama-c framac/entrypoint.c usbctrl*.c $(USBOTGHS_DIR)/usbotghs.c $(USBOTGHS_DIR)/usbotghs_fifos.c -c11 \
		    $(FRAMAC_GEN_FLAGS) \
			$(FRAMAC_EVA_FLAGS) \
   		    -then \
			$(FRAMAC_WP_FLAGS) \
   			-save $(SESSION) \
   			-time $(TIMESTAMP)

frama-c-instantiate:
	frama-c framac/entrypoint.c usbctrl.c -c11 -machdep x86_32 \
			$(FRAMAC_GEN_FLAGS) \
			-instantiate

frama-c-gui:
	frama-c-gui -load $(SESSION)



#
#   			-wp-smoke-tests \
#   			-wp-no-smoke-dead-code \


#    			-then \
#    			-wp-prop=@lemma \
#    			-wp-auto="wp:split,wp:bitrange" \
#  			-wp-auto="wp:bitshift" \

#			-wp-steps 100000 \

#-eva-bitwise-domain
#-eva-slevel-function usbctrl_declare_interface:300000 \
#-eva-equality-through-calls all \
# -from-verify-assigns \
#-eva-use-spec usbotghs_configure \

#   			-wp-smoke-tests \
#   			-wp-smoke-dead-code \
#   			-wp-smoke-dead-call \
#   			-wp-smoke-dead-loop \


# -wp-dynamic         Handle dynamic calls with specific annotations. (set by
#                     default, opposite option is -wp-no-dynamic) (calls = pointeur de fonction, wp a du mal avec cette notion,
#						contrairement à 	eva)

# -wp-init-const      Use initializers for global const variables. (set by
#                     default, opposite option is -wp-no-init-const)

# -wp-split           Split conjunctions into sub-goals. (opposite option is
#                     -wp-no-split)
# -wp-split-depth <p>  Set depth of exploration for splitting conjunctions into
#                     sub-goals.
#                     Value `-1` means an unlimited depth.

# -wp-steps <n>       Set number of steps for provers.

# -wp-let             Use variable elimination. (set by default, opposite
#                     option is -wp-no-let)

# -wp-simpl           Enable Qed Simplifications. (set by default, opposite
#                     option is -wp-no-simpl)

# -wp-par <p>         Number of parallel proof process (default: 4)

# -wp-model <model+...>  Memory model selection. Available selectors:
#                     * 'Hoare' logic variables only
#                     * 'Typed' typed pointers only
#                     * '+nocast' no pointer cast
#                     * '+cast' unsafe pointer casts
#                     * '+raw' no logic variable
#                     * '+ref' by-reference-style pointers detection
#                     * '+nat/+int' natural / machine-integers arithmetics
#                     * '+real/+float' real / IEEE floating point arithmetics

# -wp-literals        Export content of string literals. (opposite option is
#                     -wp-no-literals)

# -eva-bitwise-domain \

endif
