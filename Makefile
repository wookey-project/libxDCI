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
CFLAGS += -MMD -MP -O2

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
TODEL_CLEAN += $(OBJ)
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

SESSION:=framac/results/frama-c-rte-eva-wp-no-split.session
JOBS:=$(shell nproc)
TIMEOUT:=15

# "-val-warn-undefined-pointer-comparison none" is to deal with the
# checks (\pointer_comparable( - ,  - )) otherwise added by EVA before
# our tests of pointers against NULL. Those are not understood by WP.
# This is not an issue but should be revisited later. --arno
#
# See https://bts.frama-c.com/view.php?id=2206

frama-c-parsing:
	frama-c usbctrl.c usbctrl_descriptors.c usbctrl_handlers.c usbctrl_requests.c usbctrl_state.c framac/include/driver_api/usbotghs_frama.c \
		 -c11 -machdep x86_32 \
		 -no-frama-c-stdlib \
		 -cpp-extra-args="-nostdinc -I framac/include"

frama-c-parsing-concat:
	frama-c usbctrl_frama.c framac/include/driver_api/usbotghs_frama.c \
		 -c11 -machdep x86_32 \
		 -no-frama-c-stdlib \
		 -cpp-extra-args="-nostdinc -I framac/include"

frama-c-eva:
	frama-c usbctrl.c usbctrl_descriptors.c usbctrl_handlers.c usbctrl_requests.c usbctrl_state.c framac/include/driver_api/usbotghs_frama.c -c11 -machdep x86_32 \
	            -absolute-valid-range 0x40040000-0x40044000 \
	            -no-frama-c-stdlib \
	            -warn-left-shift-negative \
	            -warn-right-shift-negative \
	            -warn-signed-downcast \
	            -warn-signed-overflow \
	            -warn-unsigned-downcast \
	            -warn-unsigned-overflow \
				-kernel-msg-key pp \
				-cpp-extra-args="-nostdinc -I framac/include" \
		    -rte \
		    -eva \
		    -eva-auto-loop-unroll 500 \
		    -eva-slevel 500 \
		    -eva-slevel-function usbctrl_get_descriptor:12000 \
		    -eva-slevel-function usbotghs_send_data:1000 \
		    -eva-slevel-function usbotghs_endpoint_stall:1000 \
		    -eva-slevel-function usbotghs_endpoint_set_nak:1000 \
		    -eva-symbolic-locations-domain \
		    -eva-equality-domain \
		    -eva-bitwise-domain \
		    -eva-split-return auto \
		    -eva-partition-history 3 \
		    -eva-use-spec usbctrl_reset_received \
		    -eva-use-spec class_rqst_handler \
		    -eva-use-spec handler_ep \
		    -eva-log a:frama-c-rte-eva.log \
			-save framac/results/frama-c-rte-eva.session

frama-c:
	frama-c usbctrl.c usbctrl_descriptors.c usbctrl_handlers.c usbctrl_requests.c usbctrl_state.c framac/include/driver_api/usbotghs_frama.c -c11 -machdep x86_32 \
	        -absolute-valid-range 0x40040000-0x40044000 \
	        -no-frama-c-stdlib \
	        -warn-left-shift-negative \
	        -warn-right-shift-negative \
	        -warn-signed-downcast \
	        -warn-signed-overflow \
	        -warn-unsigned-downcast \
	        -warn-unsigned-overflow \
			-kernel-msg-key pp \
			-cpp-extra-args="-nostdinc -I framac/include" \
		    -rte \
		    -eva \
		    -eva-show-perf \
		    -eva-auto-loop-unroll 500 \
		    -eva-slevel 500 \
		    -eva-slevel-function usbctrl_get_descriptor:12000 \
		    -eva-slevel-function usbotghs_send_data:1000 \
		    -eva-slevel-function usbotghs_endpoint_stall:1000 \
		    -eva-slevel-function usbotghs_endpoint_set_nak:1000 \
		    -eva-symbolic-locations-domain \
		    -eva-equality-domain \
		    -eva-bitwise-domain \
		    -eva-split-return auto \
		    -eva-partition-history 3 \
		    -eva-use-spec usbctrl_reset_received \
		    -eva-use-spec class_rqst_handler \
		    -eva-use-spec handler_ep \
		    -eva-log a:frama-c-rte-eva.log \
   		    -then \
   		    -wp \
  			-wp-model "Typed+ref+int" \
  			-wp-literals \
  			-wp-prover alt-ergo,cvc4,z3 \
   			-wp-timeout $(TIMEOUT) \
   			 -save $(SESSION) \
   			-time calcium_wp-eva.txt


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

frama-c-gui:
	frama-c-gui -load $(SESSION)


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


