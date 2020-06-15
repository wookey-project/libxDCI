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
CFLAGS += -MMD -MP -O3

#############################################################
# About library sources
#############################################################

SRC_DIR = .
SRC = $(wildcard $(SRC_DIR)/*.c)
OBJ = $(patsubst %.c,$(APP_BUILD_DIR)/%.o,$(SRC))
DEP = $(OBJ:.o=.d)

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

all: $(APP_BUILD_DIR) lib

doc:

show:
	@echo
	@echo "\tAPP_BUILD_DIR\t=> " $(APP_BUILD_DIR)
	@echo
	@echo "C sources files:"
	@echo "\tSRC_DIR\t\t=> " $(SRC_DIR)
	@echo "\tSRC\t\t=> " $(SRC)
	@echo "\tOBJ\t\t=> " $(OBJ)
	@echo

lib: $(APP_BUILD_DIR)/$(LIB_FULL_NAME)

$(APP_BUILD_DIR)/%.o: %.c
	$(call if_changed,cc_o_c)

# lib
$(APP_BUILD_DIR)/$(LIB_FULL_NAME): $(OBJ)
	$(call if_changed,mklib)
	$(call if_changed,ranlib)

$(APP_BUILD_DIR):
	$(call cmd,mkdir)

-include $(DEP)


#####################################################################
# Frama-C
#####################################################################

SESSION:=result_frama/frama-c-rte-eva-wp-no-split.session
JOBS:=$(shell nproc)
TIMEOUT:=30

# "-val-warn-undefined-pointer-comparison none" is to deal with the
# checks (\pointer_comparable( - ,  - )) otherwise added by EVA before
# our tests of pointers against NULL. Those are not understood by WP.
# This is not an issue but should be revisited later. --arno
#
# See https://bts.frama-c.com/view.php?id=2206

frama-c-parsing:
	frama-c usbctrl.c usbctrl_descriptors.c usbctrl_handlers.c usbctrl_requests.c usbctrl_state.c include_frama/driver_api/usbotghs_frama.c \
		 -c11 -machdep x86_32 \
		 -no-frama-c-stdlib \
		 -cpp-extra-args="-nostdinc -I include_frama" 

frama-c-parsing-concat:
	frama-c usbctrl_frama.c include_frama/driver_api/usbotghs_frama.c \
		 -c11 -machdep x86_32 \
		 -no-frama-c-stdlib \
		 -cpp-extra-args="-nostdinc -I include_frama" 

frama-c-eva:
	frama-c usbctrl.c usbctrl_descriptors.c usbctrl_handlers.c usbctrl_requests.c usbctrl_state.c include_frama/driver_api/usbotghs_frama.c  -c11 -machdep x86_32 \
	            -absolute-valid-range 0x40040000-0x40080000 \
	            -no-frama-c-stdlib \
	            -warn-left-shift-negative \
	            -warn-right-shift-negative \
	            -warn-signed-downcast \
	            -warn-signed-overflow \
	            -warn-unsigned-downcast \
	            -warn-unsigned-overflow \
				-kernel-msg-key pp \
				-cpp-extra-args="-nostdinc -I include_frama" \
		    -rte \
		    -eva \
		    -eva-warn-undefined-pointer-comparison none \
		    -eva-auto-loop-unroll 20 \
		    -eva-slevel 300 \
		    -eva-symbolic-locations-domain \
		    -eva-equality-domain  \
  			-wp-dynamic \
		    -eva-split-return auto \
		    -eva-partition-history 6 \
		    -eva-log a:frama-c-rte-eva.log \
			-save result_frama/frama-c-rte-eva.session

frama-c-eva-concat:
	frama-c usbctrl_frama.c include_frama/driver_api/usbotghs_frama.c  -c11 -machdep x86_32 \
	            -absolute-valid-range 0x40040000-0x40080000 \
	            -no-frama-c-stdlib \
	            -warn-left-shift-negative \
	            -warn-right-shift-negative \
	            -warn-signed-downcast \
	            -warn-signed-overflow \
	            -warn-unsigned-downcast \
	            -warn-unsigned-overflow \
				-kernel-msg-key pp \
				-cpp-extra-args="-nostdinc -I include_frama" \
		    -rte \
		    -eva \
		    -eva-warn-undefined-pointer-comparison none \
		    -eva-auto-loop-unroll 20 \
		    -eva-slevel 300 \
		    -eva-symbolic-locations-domain \
		    -eva-equality-domain  \
  			-wp-dynamic \
		    -eva-split-return auto \
		    -eva-partition-history 6 \
		    -eva-log a:frama-c-rte-eva.log \
			-save result_frama/frama-c-rte-eva.session

frama-c:
	frama-c usbctrl.c usbctrl_descriptors.c usbctrl_handlers.c usbctrl_requests.c usbctrl_state.c include_frama/driver_api/usbotghs_frama.c -c11 -machdep x86_32 \
	            -absolute-valid-range 0x40040000-0x40080000 \
	            -no-frama-c-stdlib \
	            -warn-left-shift-negative \
	            -warn-right-shift-negative \
	            -warn-signed-downcast \
	            -warn-signed-overflow \
	            -warn-unsigned-downcast \
	            -warn-unsigned-overflow \
				-kernel-msg-key pp \
				-cpp-extra-args="-nostdinc -I include_frama" \
		    -rte \
		    -eva \
		    -eva-warn-undefined-pointer-comparison none \
		    -eva-auto-loop-unroll 20 \
		    -eva-slevel 300 \
		    -eva-symbolic-locations-domain \
		    -eva-equality-domain  \
  			-wp-dynamic \
		    -eva-split-return auto \
		    -eva-partition-history 6 \
		    -eva-log a:frama-c-rte-eva.log \
   		    -then \
   		    -wp \
  			-wp-model "Typed+ref+int" \
  			-wp-literals \
  			-wp-prover alt-ergo,cvc4,z3 \
   			-wp-timeout $(TIMEOUT) -save $(SESSION)  \
   			-time calcium_wp-eva.txt

frama-c-concat:
	frama-c usbctrl_frama.c include_frama/driver_api/usbotghs_frama.c -c11 -machdep x86_32 \
	            -absolute-valid-range 0x40040000-0x40080000 \
	            -no-frama-c-stdlib \
	            -warn-left-shift-negative \
	            -warn-right-shift-negative \
	            -warn-signed-downcast \
	            -warn-signed-overflow \
	            -warn-unsigned-downcast \
	            -warn-unsigned-overflow \
				-kernel-msg-key pp \
				-cpp-extra-args="-nostdinc -I include_frama" \
		    -rte \
		    -eva \
		    -eva-warn-undefined-pointer-comparison none \
		    -eva-auto-loop-unroll 20 \
		    -eva-slevel 300 \
		    -eva-symbolic-locations-domain \
		    -eva-equality-domain  \
  			-wp-dynamic \
		    -eva-split-return auto \
		    -eva-partition-history 6 \
		    -eva-log a:frama-c-rte-eva.log \
   		    -then \
   		    -wp \
  			-wp-model "Typed+ref+int" \
  			-wp-literals \
  			-wp-prover alt-ergo,cvc4,z3 \
   			-wp-timeout $(TIMEOUT) -save $(SESSION)  \
   			-time calcium_wp-eva.txt


#			-wp-steps 100000 \

#-eva-bitwise-domain
#-eva-slevel-function usbctrl_declare_interface:300000 \

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




