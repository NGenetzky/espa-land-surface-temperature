## NOTE - Since we are still in the very early stages of development, the information contained in this README may not be correct, however it will be updated from time to time.

## Land Surface Temperature 0.0.1 Release Notes
Release Date: MONTH DAY, YEAR

This project contains application source code for producing Land Surface Temperature products.  It currently only supports Landsat 5-7, as prototype output products that have not been validated.

Algorithms for specific sensors, where warranted, are located in sensor specific sub-directories.  See the sensor specific sub-directories for more details and usage examples.

This project is provided by the US Geological Survey (USGS) Earth Resources
Observation and Science (EROS) Land Satellite Data Systems (LSDS) Science
Research and Development (LSRD) Project. For questions regarding products
produced by this source code, please contact the Landsat Contact Us page and
specify USGS CDR/ECV in the "Regarding" section.
https://landsat.usgs.gov/contactus.php 

### Downloads
Land Surface Temperature source code
```
    git clone https://github.com/USGS-EROS/espa-land-surface-temperature.git
```

For current proto-type version, see git tag [land-surface-temperature_v0.0.1]

### Installation
  * Install dependent libraries: ESPA product formatter (https://github.com/USGS-EROS/espa-product-formatter)

  * Set up environment variables: Can create an environment shell file or add the following to your bash shell.  For C shell, use 'setenv VAR "directory"'.
```
    export PREFIX="path/to/directory/for/build/data"
    export ASTER_GED_SERVER_NAME="server.name.where.the.GED.data.resides"
    export ASTER_GED_SERVER_PATH="/path/on/server/to/the/data/"
```

  * Download: (from Github USGS-EROS/espa-land-surface-temperature project)

  * Build/Install: The following build will create an executable file under $PREFIX/bin: lst (tested in Linux with the gcc compiler). It will also copy the Python scripts for running Land Surface Temperature into the $PREFIX/bin directory.

    - All sensor applications can be built and installed from the top-level directory, or at the users choice only a single individual sensors applications could be built and installed.

      - Available sensor options are: **l5-7_lst**

    - To build all sensor applications: ```make all```

    - To install all sensor applications: ```make install```

    - To build a single sensor application: ```make <sensor>```

    - To install a single sensor application: ```make <sensor>-install```

### Dependencies
  * ESPA raw binary and ESPA common libraries from ESPA product formatter and associated dependencies
  * XML2 library

### Data Preprocessing
This version of the spectral indices application requires the input Landsat products to be in the ESPA internal file format.

### Data Postprocessing
After compiling the ESPA product formatter raw\_binary libraries and tools, the convert\_espa\_to\_gtif and convert\_espa\_to\_hdf command-line tools can be used to convert the ESPA internal file format to HDF or GeoTIFF.  Otherwise the data will remain in the ESPA internal file format, which includes each band in the ENVI file format (i.e. raw binary file with associated ENVI header file) and an overall XML metadata file.

### Associated Scripts
A python script exists in the scripts directory to assist in running the Land Surface Temperature applications.  land\_surface\_temperature.py grabs the user-specified options and generates the desired Land Surface Temperature product by calling the lst executable.

### Verification Data

### User Manual

### Product Guide

## Changes From Previous Version
#### Updates on MONTH DAY, YEAR - USGS EROS
  * DESCRIBE WHAT WAS MODIFIED HERE
