#------------------------------------------------------------------------------
# Makefile
#
# For building land-surface-temperature.
#------------------------------------------------------------------------------

# Set up compile options
CC = gcc
RM = rm -f
EXTRA = -Wall -g -O2

# Define the include files
INC = const.h utilities.h date.h 2d_array.h get_args.h input.h output.h \
      build_points.h build_modtran_input.h \
      calculate_point_atmospheric_parameters.h \
      calculate_pixel_atmospheric_parameters.h
INCDIR  = -I. -I$(HDFINC) -I$(HDFEOS_INC) -I$(HDFEOS_GCTPINC) -I$(XML2INC) \
          -I$(ESPAINC)
NCFLAGS = $(EXTRA) $(INCDIR)

# Define the source code and object files
SRC = \
      utilities.c             \
      2d_array.c              \
      date.c                  \
      input.c                 \
      output.c                \
      get_args.c              \
      build_points.c \
      build_modtran_input.c   \
      calculate_point_atmospheric_parameters.c \
      calculate_pixel_atmospheric_parameters.c \
      lst.c
OBJ = $(SRC:.c=.o)

# Define the object libraries
EXLIB = -L$(ESPALIB) -l_espa_raw_binary -l_espa_common \
        -l_espa_format_conversion -L$(HDFEOS_LIB) -lhdfeos -L$(HDFLIB) \
        -lmfhdf -ldf -L$(JPEGLIB) -ljpeg -L$(XML2LIB) -lxml2 \
        -L$(HDFEOS_GCTPLIB) -lGctp -lz
MATHLIB = -lm
LOADLIB = $(EXLIB) $(MATHLIB)

# Define the executable
EXE = l5_7_intermediate_data

# Target for the executable
all: $(EXE)

$(EXE): $(OBJ) $(INC)
	$(CC) $(EXTRA) -o $(EXE) $(OBJ) $(LOADLIB)

install:
	install -d $(PREFIX)/bin
	install -m 755 $(EXE) $(PREFIX)/bin

clean:
	$(RM) *.o $(EXE)

$(OBJ): $(INC)

.c.o:
	$(CC) $(NCFLAGS) -c $<

