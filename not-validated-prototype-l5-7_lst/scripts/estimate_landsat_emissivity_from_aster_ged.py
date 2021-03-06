#! /usr/bin/env python

import os
import sys
import glob
import logging
import math
import requests
import commands
import numpy as np
from cStringIO import StringIO
from argparse import ArgumentParser
from osgeo import gdal, osr
from time import sleep


# Import the metadata api found in the espa-common project
import metadata_api


'''
  Example HTTP file request for ASTER GED data.

      http://e4ftl01.cr.usgs.gov/ASTT/AG100.003/2000.01.01/<tile>

  Where <tile> is of the form:
      AG100.v003.44.-077.0001.h5  (Negative Longitude)
      or
      AG100.v003.44.077.0001.h5   (Positive Longitude)
'''
# Setup some formats to generate the URL to retrieve an ASTER GED tile
# TODO TODO TODO - To make this operational, the server needs to be specified
# TODO TODO TODO - on the fly through another method
SERVER = 'http://e4ftl01.cr.usgs.gov'
SERVER_PATH = '/ASTT/AG100.003/2000.01.01/'
FILE_N_FORMAT = 'AG100.v003.{0:02}.{1:04}.0001'
FILE_P_FORMAT = 'AG100.v003.{0:02}.{1:03}.0001'


'''
 Specify the no data value we will be using, it also matches the no_data_value
 for the ASTER data we extract and use
'''
NO_DATA_VALUE = -9999


# ============================================================================
class LandsatInfo(object):
    '''
    Description:
        Used as a data structure to cleanup parameter passing to routines.
    '''

    north = None
    south = None
    east = None
    west = None
    x_pixel_size = None
    y_pixel_size = None
    min_x_extent = None
    max_x_extent = None
    min_y_extent = None
    max_y_extent = None
    dest_proj4 = None


# ============================================================================
def execute_cmd(cmd):
    '''
    Description:
        Execute a command line and return the terminal output or raise an
        exception

    Returns:
        output - The stdout and/or stderr from the executed command.
    '''

    output = ''

    (status, output) = commands.getstatusoutput(cmd)

    if status < 0:
        message = "Application terminated by signal [%s]" % cmd
        if len(output) > 0:
            message = ' Stdout/Stderr is: '.join([message, output])
        raise Exception(message)

    if status != 0:
        message = "Application failed to execute [%s]" % cmd
        if len(output) > 0:
            message = ' Stdout/Stderr is: '.join([message, output])
        raise Exception(message)

    if os.WEXITSTATUS(status) != 0:
        message = "Application [%s] returned error code [%d]" \
                  % (cmd, os.WEXITSTATUS(status))
        if len(output) > 0:
            message = ' Stdout/Stderr is: '.join([message, output])
        raise Exception(message)

    return output


# ============================================================================
def http_transfer_file(download_url, destination_file):
    '''
    Description:
        Using http transfer a file from a source location to a destination
        file on the localhost.

    Returns:
        status_code - One of the following
                    - 200, requests.codes['ok']
                    - 404, requests.codes['not_found']:
                    - 503, requests.codes['service_unavailable']:

    Notes:
        If a 503 is returned, the logged exception should be reviewed to
        determine the real cause of the error.
    '''

    logger = logging.getLogger(__name__)

    logger.info(download_url)

    session = requests.Session()

    session.mount('http://', requests.adapters.HTTPAdapter(max_retries=3))
    session.mount('https://', requests.adapters.HTTPAdapter(max_retries=3))

    status_code = requests.codes['ok']
    retry_attempt = 0
    done = False
    while not done:
        status_code = requests.codes['ok']
        req = None
        try:
            req = session.get(url=download_url, timeout=300.0)

            if not req.ok:
                msg = "HTTP - Transfer of [{0}] - FAILED".format(download_url)
                logger.error(msg)
                # The raise_for_status gets caught by this try's except block
                req.raise_for_status()

            # Write the downloaded data to the destination file
            with open(destination_file, 'wb') as local_fd:
                local_fd.write(req.content)

            # Break the looping
            done = True
            logger.info("HTTP - Transfer Complete")

        except:
            logger.exception("HTTP - Transfer Issue")

            if req is not None:
                status_code = req.status_code

            if status_code != requests.codes['not_found']:
                if retry_attempt > 3:
                    msg = "HTTP - Transfer Failed - exceeded retry limit"
                    logger.info(msg)
                    done = True
                else:
                    retry_attempt += 1
                    sleep(int(1.5 * retry_attempt))
            else:
                # Not Found - So break the looping because we are done
                done = True

        finally:
            if req is not None:
                req.close()

    return status_code


# ============================================================================
def update_envi_header(hdr_file_path, no_data_value):
    '''
    Description:
        Updates the specified ENVI header.  Especially the no data value,
        since it is not supported by the GDAL ENVI driver.
    '''

    sb = StringIO()
    with open(hdr_file_path, 'r') as tmp_fd:
        while True:
            line = tmp_fd.readline()
            if not line:
                break
            if (line.startswith('data ignore value')
                    or line.startswith('description')):
                pass
            else:
                sb.write(line)

            if line.startswith('description'):
                # This may be on multiple lines so read lines until
                # we find the closing brace
                if not line.strip().endswith('}'):
                    while 1:
                        next_line = tmp_fd.readline()
                        if (not next_line
                                or next_line.strip().endswith('}')):
                            break
                sb.write('description = {ESPA-generated file}\n')
            elif (line.startswith('data type')
                  and (no_data_value is not None)):
                sb.write('data ignore value = %s\n' % no_data_value)

    # Do the actual replace here
    with open(hdr_file_path, 'w') as tmp_fd:
        tmp_fd.write(sb.getvalue())


# ============================================================================
def extract_aster_data(emis_ds_name, ndvi_ds_name, land_water_ds_name,
                       lat_ds_name, lon_ds_name):

    '''
    Description:
        Opens the requested files and extracts the associated data, which is
        then returned to the caller.

    Returns: An array of the following information.
        aster_b13_data - Aster Emissivity band 13 data.
        aster_b14_data - Aster Emissivity band 14 data.
        aster_ndvi_data - Aster NDVI band data.
        aster_land_water_data - Aster Land Water Map band data.
        aster_lat_data - Geolocation Lattitude data.
        aster_lon_data - Geolocation Longitude data.
        x_dim - Number of columns of the data.
        y_dim - Number of rows of the data.
    '''

    try:
        # Open the Emissivity sub-dataset
        emis_sds = gdal.Open(emis_ds_name)
        if emis_sds is None:
            raise RuntimeError("GDAL failed to open {0}".format(emis_ds_name))

        # Open the NDVI sub-dataset
        ndvi_sds = gdal.Open(ndvi_ds_name)
        if ndvi_sds is None:
            raise RuntimeError("GDAL failed to open {0}".format(ndvi_sds_name))

        # Open the Land Water sub-dataset
        land_water_sds = gdal.Open(land_water_ds_name)
        if land_water_sds is None:
            raise RuntimeError("GDAL failed to open"
                               " {0}".format(land_water_sds_name))

        # Open the Latitude sub-dataset
        lat_sds = gdal.Open(lat_ds_name)
        if lat_sds is None:
            raise RuntimeError("GDAL failed to open {0}".format(lat_ds_name))

        # Open the Longitude sub-dataset
        lon_sds = gdal.Open(lon_ds_name)
        if lon_sds is None:
            raise RuntimeError("GDAL failed to open {0}".format(lon_ds_name))

        # The dimensions are the same for all the bands so just use
        # the values from the Emissivity dataset
        x_dim = emis_sds.RasterXSize
        y_dim = emis_sds.RasterYSize

        # Retrieve the band 13 data from the HDF5 input
        aster_b13_data = emis_sds.GetRasterBand(4).ReadAsArray(0, 0,
                                                               x_dim, y_dim)

        # Retrieve the band 14 data from the HDF5 input
        aster_b14_data = emis_sds.GetRasterBand(5).ReadAsArray(0, 0,
                                                               x_dim, y_dim)
        del (emis_sds)

        # Retrieve the NDVI band data from the HDF5 input
        aster_ndvi_data = ndvi_sds.GetRasterBand(1).ReadAsArray(0, 0,
                                                                x_dim, y_dim)
        del (ndvi_sds)

        # Retrieve the Land Water band data from the HDF5 input
        aster_land_water_data = \
            land_water_sds.GetRasterBand(1).ReadAsArray(0, 0, x_dim, y_dim)
        del (land_water_sds)

        # Retrieve the Latitude data from the HDF5 input
        aster_lat_data = lat_sds.GetRasterBand(1).ReadAsArray(0, 0,
                                                              x_dim, y_dim)
        del (lat_sds)

        # Retrieve the Longitude data from the HDF5 input
        aster_lon_data = lon_sds.GetRasterBand(1).ReadAsArray(0, 0,
                                                              x_dim, y_dim)
        del (lon_sds)

    except Exception:
        raise

    return (aster_b13_data, aster_b14_data,
            aster_ndvi_data, aster_land_water_data,
            aster_lat_data, aster_lon_data, x_dim, y_dim)


# ============================================================================
def generate_raster_file(driver, filename, x_dim, y_dim, data,
                         geo_transform, proj_wkt, no_data_value, data_type):
    '''
    Description:
        Creates a raster file on disk for the specified data, using the
        specified driver.

    Note: It is assumed that the driver supports setting of the no data value.
          It is the callers responsibility to fix it if it does not.

    Note: It is assumed that the caller specified the correct file extension
          in the filename parameter for the specfied driver.
    '''

    try:
        raster = driver.Create(filename, x_dim, y_dim, 1, data_type)

        raster.SetGeoTransform(geo_transform)
        raster.SetProjection(proj_wkt)
        raster.GetRasterBand(1).WriteArray(data)
        raster.GetRasterBand(1).SetNoDataValue(no_data_value)
        raster.FlushCache()

        # Cleanup memory
        del (raster)

    except Exception:
        raise


# ============================================================================
def get_proj4_projection_string(img_filename):
    '''
    Description:
        Determine the proj4 projection parameters for the specified image.

    Returns:
        proj4 - The proj4 projection string for the image.
    '''

    ds = gdal.Open(img_filename)
    if ds is None:
        raise RuntimeError("GDAL failed to open (%s)" % img_filename)

    ds_srs = osr.SpatialReference()
    ds_srs.ImportFromWkt(ds.GetProjection())

    proj4 = ds_srs.ExportToProj4()

    del (ds_srs)
    del (ds)

    return proj4


# ============================================================================
def mosaic_all_tiles_into_one_raster(src_names, dest_name):
    '''
    Description:
        Executes gdalwarp on the supplied source names to generate a mosaic'ed
        destination named file.
    '''

    logger = logging.getLogger(__name__)

    cmd = ['gdalwarp', '-wm', '2048', '-multi',
           '-srcnodata', str(NO_DATA_VALUE),
           '-dstnodata', str(NO_DATA_VALUE)]
    cmd.extend(src_names)
    cmd.append(dest_name)

    cmd = ' '.join(cmd)

    output = ''
    try:
        logger.info("Executing [{0}]".format(cmd))
        output = execute_cmd(cmd)
    except Exception:
        logger.error("Failed to mosaic tiles")
        raise
    finally:
        if len(output) > 0:
            logger.info(output)


# ============================================================================
def warp_raster_to_match_landsat_data(src_name, dest_name,
                                      src_proj4, ls_info):
    '''
    Description:
        Executes gdalwarp on the supplied source name to generate a warped
        destination named file that matches the projection and image extents
        and pixel size specified, which were derived from Landsat data.
    '''

    logger = logging.getLogger(__name__)

    cmd = ['gdalwarp', '-wm', '2048', '-multi',
           '-tr', str(ls_info.x_pixel_size), str(ls_info.y_pixel_size),
           '-s_srs', "'" + src_proj4 + "'",
           '-t_srs', "'" + ls_info.dest_proj4 + "'",
           '-of', 'GTiff',
           '-overwrite', '-te',
           str(ls_info.min_x_extent), str(ls_info.min_y_extent),
           str(ls_info.max_x_extent), str(ls_info.max_y_extent),
           '-srcnodata', str(NO_DATA_VALUE),
           '-dstnodata', str(NO_DATA_VALUE)]
    cmd.append(src_name)
    cmd.append(dest_name)

    cmd = ' '.join(cmd)

    output = ''
    try:
        logger.info("Executing [{0}]".format(cmd))
        output = execute_cmd(cmd)
    except Exception:
        logger.error("Failed during warping to match Landsat")
        raise
    finally:
        if len(output) > 0:
            logger.info(output)


# ============================================================================
def build_b6_emis_data(driver, ls_info):
    '''
    Description:
        Download the ASTER GED tiles that encompass our Landsat scene and
        extract the bands required to generate the Landsat Emissivity data.
        Mosaic the Landsat Emissivity tiles together and then warp them to
        the projection and image extents of the Landsat scenes.  For
        convenience the ASTER NDVI is also extracted and warped to the
        Landsat scenes projection and image extents

    Returns:
        warped_eLandsat_b6_emis_name
          - The name of the reprojected Landsat Emissivity data.
        warped_aster_ndvi_name
          - The name of the reprojected ASTER NDVI data.
    '''

    # The ASTER data is in geographic projection so specify that here
    ds_srs = osr.SpatialReference()
    ds_srs.ImportFromEPSG(4326)

    # Process through the lattitude and longitude ASTER tiles which cover the
    # Landsat scene we are processing
    # - Download them
    # - Extract the Emissivity bands 13 and 14 as well as the NDVI
    # - Generate the B6 EMIS Landsat from the 13 and 14 band data
    eLandsat_b6_emis_filenames = list()
    aster_ndvi_filenames = list()
    aster_land_water_filenames = list()
    for lat in xrange(int(ls_info.south), int(ls_info.north)+1):
        for lon in xrange(int(ls_info.west), int(ls_info.east)+1):
            # Build the base filename using the positive or negative format
            filename = ''
            if lon < 0:
                filename = FILE_N_FORMAT.format(lat, lon)
            else:
                filename = FILE_P_FORMAT.format(lat, lon)

            # Build the HDF5 filename for the tile
            h5_file_path = ''.join([filename, '.h5'])

            # Build the URL and download the tile
            url_path = ''.join([SERVER, SERVER_PATH, h5_file_path])
            status_code = http_transfer_file(url_path, h5_file_path)

            # Check for and handle tiles that are not available in the ASTER
            # data
            if status_code != requests.codes['ok']:
                if status_code != requests.codes['not_found']:
                    raise Exception("HTTP - Transfer Failed")
                else:
                    # Advance to the next tile
                    continue

            # ----------------------------------------------------------------
            # Build the output tile names
            eLandsat_b6_emis_tile_name = ''.join([filename,
                                                  '_eLandsat_b6_emis.tif'])
            aster_ndvi_tile_name = ''.join([filename, '_ndvi.tif'])
            aster_land_water_tile_name = ''.join([filename, '_lw_map.tif'])

            # Add the tile names to the list for mosaic building and warping
            eLandsat_b6_emis_filenames.append(eLandsat_b6_emis_tile_name)
            aster_ndvi_filenames.append(aster_ndvi_tile_name)
            aster_land_water_filenames.append(aster_land_water_tile_name)

            # Get the sub-dataset name for Emissivity-Mean
            emis_ds_name = ''.join(['HDF5:"', h5_file_path,
                                    '"://Emissivity/Mean'])
            # Get the sub-dataset name for NDVI-ean
            ndvi_ds_name = ''.join(['HDF5:"', h5_file_path,
                                    '"://NDVI/Mean'])
            # Get the sub-dataset name for Land Water Map
            land_water_ds_name = ''.join(['HDF5:"', h5_file_path,
                                          '"://Land_Water_Map/LWmap'])
            # Get the sub-dataset name for Lattitude
            lat_ds_name = ''.join(['HDF5:"', h5_file_path,
                                   '"://Geolocation/Latitude'])
            # Get the sub-dataset name for Longitude
            lon_ds_name = ''.join(['HDF5:"', h5_file_path,
                                   '"://Geolocation/Longitude'])

            logger.debug(emis_ds_name)
            logger.debug(ndvi_ds_name)
            logger.debug(land_water_ds_name)
            logger.debug(lat_ds_name)
            logger.debug(lon_ds_name)

            # ----------------------------------------------------------------
            try:
                (aster_b13_data, aster_b14_data,
                 aster_ndvi_data, aster_land_water_data,
                 aster_lat_data, aster_lon_data, x_dim, y_dim) = \
                    extract_aster_data(emis_ds_name, ndvi_ds_name,
                                       land_water_ds_name,
                                       lat_ds_name, lon_ds_name)
            except Exception:
                logger.exception("Extracting ASTER data from tile")
                raise

            # Remove the HDF5 tile since we have extracted all the info we
            # need from it
# TODO TODO TODO - TEMP KEEP THEM AROUND
#            if os.path.exists(h5_file_path):
#                os.unlink(h5_file_path)

            # ----------------------------------------------------------------
            # Determine the minimum and maximum latitude and longitude
            x_min = aster_lon_data.min()
            x_max = aster_lon_data.max()
            y_min = aster_lat_data.min()
            y_max = aster_lat_data.max()

            # Determine the resolution of the ASTER data
            x_res = (x_max - x_min) / float(x_dim)
            y_res = (y_max - y_min) / float(y_dim)

            # Build the geo transform to apply to the raster tile
            geo_transform = [x_min, x_res, 0, y_max, 0, -y_res]

            # ----------------------------------------------------------------
            # Create a mask of the band 13 data and then scale it
            # Original matlab code is <= 0
            aster_b13_masked = np.ma.masked_less_equal(aster_b13_data, 0)
            aster_b13_scaled = aster_b13_masked * 0.001

            # Create a mask of the band 14 data and then scale it
            # Original matlab code is <= 0
            aster_b14_masked = np.ma.masked_less_equal(aster_b14_data, 0)
            aster_b14_scaled = aster_b14_masked * 0.001

            # Re-make the masks for B13 and B14 as a combined mask so the
            # estimated Landsat B6 EMIS has the correct mask
            mask = np.ma.mask_or(np.ma.getmask(aster_b13_scaled),
                                 np.ma.getmask(aster_b14_scaled))
            aster_b13_scaled = np.ma.masked_where(mask, aster_b13_scaled)
            aster_b14_scaled = np.ma.masked_where(mask, aster_b14_scaled)

            # Memory cleanup
            del (mask)
            del (aster_b13_data)
            del (aster_b14_data)
            del (aster_b13_masked)
            del (aster_b14_masked)

            # Create the estimated Landsat B6 EMIS data
            eLandsat_b6_emis = (0.44 * aster_b13_scaled
                                + 0.4 * aster_b14_scaled
                                + 0.156)

            # Memory cleanup
            del (aster_b13_scaled)
            del (aster_b14_scaled)

            # Create a mask of the NDVI band data and then scale it
            aster_ndvi_masked = np.ma.masked_equal(aster_ndvi_data,
                                                   NO_DATA_VALUE)
            aster_ndvi_scaled = aster_ndvi_masked * 0.01

            # Memory cleanup
            del (aster_ndvi_data)
            del (aster_ndvi_masked)

            # numpy array them so they are no longer masked
            eLandsat_b6_emis_numpy = np.array(eLandsat_b6_emis)
            aster_ndvi_numpy = np.array(aster_ndvi_scaled)

            # Memory cleanup
            del (eLandsat_b6_emis)
            del (aster_ndvi_scaled)

            # ----------------------------------------------------------------
            # Create the estimated Landsat B6 EMIS raster output tile
            try:
                logger.info("Creating an estimated Landsat B6 EMIS tile")
                generate_raster_file(driver, eLandsat_b6_emis_tile_name,
                                     x_dim, y_dim, eLandsat_b6_emis_numpy,
                                     geo_transform, ds_srs.ExportToWkt(),
                                     NO_DATA_VALUE, gdal.GDT_Float32)
            except Exception:
                logger.exception("Creating eLandsat B6 EMIS tile")
                raise

            # ----------------------------------------------------------------
            # Create the ASTER NDVI raster output tile
            try:
                logger.info("Creating an ASTER NDVI tile")
                generate_raster_file(driver, aster_ndvi_tile_name,
                                     x_dim, y_dim, aster_ndvi_numpy,
                                     geo_transform, ds_srs.ExportToWkt(),
                                     NO_DATA_VALUE, gdal.GDT_Float32)
            except Exception:
                logger.exception("Creating ASTER NDVI tile")
                raise

            # ----------------------------------------------------------------
            # Create the ASTER Land Water Map raster output tile
            try:
                logger.info("Creating an ASTER Land Water Map tile")
                generate_raster_file(driver, aster_land_water_tile_name,
                                     x_dim, y_dim, aster_land_water_data,
                                     geo_transform, ds_srs.ExportToWkt(),
                                     NO_DATA_VALUE, gdal.GDT_Int16)
            except Exception:
                logger.exception("Creating ASTER Land Water Map tile")
                raise

            # Memory cleanup
            del (eLandsat_b6_emis_numpy)
            del (aster_ndvi_numpy)
            del (aster_land_water_data)

    # Check to see that we downloaded at least one ASTER tile for processing.
    if len(eLandsat_b6_emis_filenames) == 0:
        raise Exception("No ASTER tiles were downloaded")

    # Save the source proj4 string to use during warping
    src_proj4 = ds_srs.ExportToProj4()

    # Define the temporary names
    temp_eLandsat_b6_emis_name = 'temp_eLandsat_b6_emis.tif'
    temp_aster_ndvi_name = 'temp_aster_ndvi.tif'
    temp_aster_land_water_name = 'temp_aster_lw_map.tif'
    warped_eLandsat_b6_emis_name = 'warped_elandsat_b6_emis.tif'
    warped_aster_ndvi_name = 'warped_aster_ndvi.tif'
    warped_aster_land_water_name = 'warped_aster_lw_map.tif'

    # Mosaic the estimated Landsat B6 EMIS tiles into the temp EMIS
    try:
        logger.info("Building mosaic for estimated Landsat B6 EMIS")
        mosaic_all_tiles_into_one_raster(eLandsat_b6_emis_filenames,
                                         temp_eLandsat_b6_emis_name)
    except Exception:
        logger.exception("Mosaicing B6 EMIS tiles")
        raise

    # Mosaic the ASTER NDVI tiles into the temp NDVI
    try:
        logger.info("Building mosaic for ASTER NDVI")
        mosaic_all_tiles_into_one_raster(aster_ndvi_filenames,
                                         temp_aster_ndvi_name)
    except Exception:
        logger.exception("Mosaicing ASTER NDVI tiles")
        raise

    # Mosaic the ASTER Land Water Map tiles into the temp Land Water Map
    try:
        logger.info("Building mosaic for ASTER Land Water Map")
        mosaic_all_tiles_into_one_raster(aster_land_water_filenames,
                                         temp_aster_land_water_name)
    except Exception:
        logger.exception("Mosaicing ASTER Land Water Map tiles")
        raise

    # Cleanup the estimated Landsat B6 EMIS tiles
# TODO TODO TODO - TEMP KEEP THEM AROUND
#    for emis_filename in eLandsat_b6_emis_filenames:
#        if os.path.exists(emis_filename):
#            os.unlink(emis_filename)

    # Cleanup the ASTER NDVI tiles
# TODO TODO TODO - TEMP KEEP THEM AROUND
#    for ndvi_filename in aster_ndvi_filenames:
#        if os.path.exists(ndvi_filename):
#            os.unlink(ndvi_filename)

    # Cleanup the ASTER Land Water Map tiles
# TODO TODO TODO - TEMP KEEP THEM AROUND
#    for land_water_filename in aster_land_water_filenames:
#        if os.path.exists(land_water_filename):
#            os.unlink(land_water_filename)

    # Warp estimated Landsat B6 EMIS to match the Landsat data
    try:
        logger.info("Warping estimated Landsat B6 EMIS to match Landsat data")
        warp_raster_to_match_landsat_data(temp_eLandsat_b6_emis_name,
                                          warped_eLandsat_b6_emis_name,
                                          src_proj4, ls_info)
    except Exception:
        logger.exception("Warping B6 EMIS to match Landsat data")
        raise

    # Warp ASTER NDVI to match the Landsat data
    try:
        logger.info("Warping ASTER NDVI to match Landsat data")
        warp_raster_to_match_landsat_data(temp_aster_ndvi_name,
                                          warped_aster_ndvi_name,
                                          src_proj4, ls_info)
    except Exception:
        logger.exception("Warping ASTER NDVI to match Landsat data")
        raise

    # Warp ASTER Land Water Map to match the Landsat data
    try:
        logger.info("Warping ASTER Land Water Map to match Landsat data")
        warp_raster_to_match_landsat_data(temp_aster_land_water_name,
                                          warped_aster_land_water_name,
                                          src_proj4, ls_info)
    except Exception:
        logger.exception("Warping ASTER Land Water Map to match Landsat data")
        raise

    # Cleanup the temp files
    if os.path.exists(temp_eLandsat_b6_emis_name):
        os.unlink(temp_eLandsat_b6_emis_name)
    if os.path.exists(temp_aster_ndvi_name):
        os.unlink(temp_aster_ndvi_name)
    if os.path.exists(temp_aster_land_water_name):
        os.unlink(temp_aster_land_water_name)

    return (warped_eLandsat_b6_emis_name,
            warped_aster_ndvi_name,
            warped_aster_land_water_name)


def read_info_from_metadata(xml_filename):
    # Read the XML metadata
    espa_xml = metadata_api.parse(xml_filename, silence=True)
    # Grab the global metadata object
    gm = espa_xml.get_global_metadata()
    # Grab the bands metadata object
    bands = espa_xml.get_bands()

    ls_info = LandsatInfo()

    toa_bt_name = ''
    toa_green_name = ''
    toa_red_name = ''
    toa_nir_name = ''
    toa_swir1_name = ''
    toa_green_scale_factor = 1.0
    toa_red_scale_factor = 1.0
    toa_nir_scale_factor = 1.0
    toa_swir1_scale_factor = 1.0

    # Find the TOA bands to extract information from
    for band in bands.band:
        if band.product == 'toa_refl' and band.name == 'toa_band2':
            toa_green_name = band.get_file_name()
            toa_green_scale_factor = float(band.scale_factor)

        if band.product == 'toa_refl' and band.name == 'toa_band3':
            toa_red_name = band.get_file_name()
            toa_red_scale_factor = float(band.scale_factor)

        if band.product == 'toa_refl' and band.name == 'toa_band4':
            toa_nir_name = band.get_file_name()
            toa_nir_scale_factor = float(band.scale_factor)

        if band.product == 'toa_refl' and band.name == 'toa_band5':
            toa_swir1_name = band.get_file_name()
            toa_swir1_scale_factor = float(band.scale_factor)

        if band.product == 'toa_bt' and band.category == 'image':
            # Get the output pixel size
            ls_info.x_pixel_size = band.pixel_size.x
            ls_info.y_pixel_size = band.pixel_size.y

            toa_bt_name = band.get_file_name()

            # Get the output proj4 string
            ls_info.dest_proj4 = get_proj4_projection_string(toa_bt_name)

    # Error if we didn't find the required TOA bands in the data
    if len(toa_green_name) <= 0:
        raise Exception("Failed to find the TOA GREEN band in the input data")
    if len(toa_red_name) <= 0:
        raise Exception("Failed to find the TOA RED band in the input data")
    if len(toa_nir_name) <= 0:
        raise Exception("Failed to find the TOA NIR band in the input data")
    if len(toa_swir1_name) <= 0:
        raise Exception("Failed to find the TOA SWIR1 band in the input data")
    if len(toa_bt_name) <= 0:
        raise Exception("Failed to find the TOA BT band in the input data")

    # Determine the bounding geographic coordinates for the ASTER tiles we
    # will need
    ls_info.north = math.ceil(gm.bounding_coordinates.north)
    ls_info.south = math.floor(gm.bounding_coordinates.south)
    ls_info.east = math.ceil(gm.bounding_coordinates.east)
    ls_info.west = math.floor(gm.bounding_coordinates.west)

    # Determine the UTM projection corner points
    for cp in gm.projection_information.corner_point:
        if cp.location == 'UL':
            ls_info.min_x_extent = cp.x
            ls_info.max_y_extent = cp.y
        if cp.location == 'LR':
            ls_info.max_x_extent = cp.x
            ls_info.min_y_extent = cp.y

    # Adjust the UTM coordinates for image extents becuse they are in center
    # of pixel, and we need to supply the warping with actual extents
    ls_info.min_x_extent = ls_info.min_x_extent - ls_info.x_pixel_size * 0.5
    ls_info.max_x_extent = ls_info.max_x_extent + ls_info.x_pixel_size * 0.5
    ls_info.min_y_extent = ls_info.min_y_extent - ls_info.y_pixel_size * 0.5
    ls_info.max_y_extent = ls_info.max_y_extent + ls_info.y_pixel_size * 0.5

    # Save for later
    satellite = gm.satellite

    del (bands)
    del (gm)
    del (espa_xml)

    return (ls_info, toa_bt_name, toa_green_name, toa_red_name, toa_nir_name,
            toa_swir1_name, toa_green_scale_factor, toa_red_scale_factor,
            toa_nir_scale_factor, toa_swir1_scale_factor, satellite)


# TODO TODO TODO - NEED TO PROCESS A COASTAL SCENE BECAUSE MAY NOT HAVE ASTER
#                  TILE DATA FOR SOME OF THE SCENE AND WILL NEED TO DO
#                  SOMETHING ELSE

# NEED TO TEST THIS, BECAUSE I HOPE TO HAVE IMPLEMENTED A SOLUTION
# To date, I have not found a scene the has this condition.

# TODO TODO TODO - NEED TO PROCESS A COASTAL SCENE BECAUSE MAY NOT HAVE ASTER
#                  TILE DATA FOR SOME OF THE SCENE AND WILL NEED TO DO
#                  SOMETHING ELSE


# ============================================================================
def process(args):

    logger = logging.getLogger(__name__)

    try:
        (ls_info, toa_bt_name, toa_green_name, toa_red_name, toa_nir_name,
         toa_swir1_name, toa_green_scale_factor, toa_red_scale_factor,
         toa_nir_scale_factor, toa_swir1_scale_factor,
         satellite) = read_info_from_metadata(args.xml_filename)
    except:
        logger.exception("Failed reading input XML metadata file")
        raise

    # Register all the gdal drivers and choose the GeoTiff for our temp output
    gdal.AllRegister()
    driver = gdal.GetDriverByName('GTiff')

    # Read the Landsat bands into memory
    # GREEN
    ds = gdal.Open(toa_green_name)
    x_dim = ds.RasterXSize  # They are all the same size
    y_dim = ds.RasterYSize
    landsat_green_data = ds.GetRasterBand(1).ReadAsArray(0, 0, x_dim, y_dim)
    landsat_green_masked = np.ma.masked_equal(landsat_green_data,
                                              NO_DATA_VALUE)
    landsat_green_masked = landsat_green_masked * toa_green_scale_factor

    # RED
    ds = gdal.Open(toa_red_name)
    landsat_red_data = ds.GetRasterBand(1).ReadAsArray(0, 0, x_dim, y_dim)
    landsat_red_masked = np.ma.masked_equal(landsat_red_data,
                                            NO_DATA_VALUE)
    landsat_red_masked = landsat_red_masked * toa_red_scale_factor

    # NIR
    ds = gdal.Open(toa_nir_name)
    landsat_nir_data = ds.GetRasterBand(1).ReadAsArray(0, 0, x_dim, y_dim)
    landsat_nir_masked = np.ma.masked_equal(landsat_nir_data,
                                            NO_DATA_VALUE)
    landsat_nir_masked = landsat_nir_masked * toa_nir_scale_factor

    # SWIR1
    ds = gdal.Open(toa_swir1_name)
    landsat_swir1_data = ds.GetRasterBand(1).ReadAsArray(0, 0, x_dim, y_dim)
    landsat_swir1_masked = np.ma.masked_equal(landsat_swir1_data,
                                              NO_DATA_VALUE)
    landsat_swir1_masked = landsat_swir1_masked * toa_swir1_scale_factor

    # Save the locations of the fill and scan gaps
    landsat_green_no_data_locations = \
        np.where(landsat_green_data == NO_DATA_VALUE)
    landsat_red_no_data_locations = \
        np.where(landsat_red_data == NO_DATA_VALUE)
    landsat_nir_no_data_locations = \
        np.where(landsat_nir_data == NO_DATA_VALUE)
    landsat_swir1_no_data_locations = \
        np.where(landsat_swir1_data == NO_DATA_VALUE)

    # Save for the output products
    ds_tmp_srs = osr.SpatialReference()
    ds_tmp_srs.ImportFromWkt(ds.GetProjection())
    ds_tmp_transform = ds.GetGeoTransform()

    # Memory cleanup
    del (landsat_green_data)
    del (landsat_red_data)
    del (landsat_nir_data)
    del (landsat_swir1_data)
    del (ds)

    # Re-make the masks for NIR and RED as a combined mask so NDVI has the
    # correct mask
    mask = np.ma.mask_or(np.ma.getmask(landsat_nir_masked),
                         np.ma.getmask(landsat_red_masked))
    landsat_nir_masked = np.ma.masked_where(mask, landsat_nir_masked)
    landsat_red_masked = np.ma.masked_where(mask, landsat_red_masked)

    # Re-make the masks for GREEN and SWIR1 as a combined mask so NDSI has
    # the correct mask
    mask = np.ma.mask_or(np.ma.getmask(landsat_green_masked),
                         np.ma.getmask(landsat_swir1_masked))
    landsat_green_masked = np.ma.masked_where(mask, landsat_green_masked)
    landsat_swir1_masked = np.ma.masked_where(mask, landsat_swir1_masked)

    # Build the Landsat TOA NDVI data
    landsat_ndvi_masked = ((landsat_nir_masked - landsat_red_masked)
                           / (landsat_nir_masked + landsat_red_masked))

    # Build the Landsat TOA NDSI data
    landsat_ndsi_masked = ((landsat_green_masked - landsat_swir1_masked)
                           / (landsat_green_masked + landsat_swir1_masked))

    # Memory cleanup
    del (mask)
    del (landsat_red_masked)
    del (landsat_nir_masked)
    del (landsat_green_masked)
    del (landsat_swir1_masked)

    # Harden the mask so it does not change in the following statement
    landsat_ndvi_masked = landsat_ndvi_masked.harden_mask()
    # Turn all negative values to zero
    landsat_ndvi_masked[landsat_ndvi_masked < 0] = 0

    # Save the locations for the specfied snow pixels
    selected_snow_locations = np.where(landsat_ndsi_masked > 0.4)

    # Memory cleanup
    del (landsat_ndsi_masked)

    # Build the estimated Landsat B6 EMIS data from the ASTER GED data and
    # warp it to the Landsat scenes projection and image extents
    # For convenience the ASTER NDVI is also extracted and warped to the
    # Landsat scenes projection and image extents
    (warped_eLandsat_b6_emis_name,
     warped_aster_ndvi_name,
     warped_aster_land_water_name) = build_b6_emis_data(driver, ls_info)

    # Load the warped estimated Landsat B6 EMIS into memory
    ds = gdal.Open(warped_eLandsat_b6_emis_name)
    eLandsat_b6_emis = ds.GetRasterBand(1).ReadAsArray(0, 0, x_dim, y_dim)
    eLandsat_b6_emis_masked = np.ma.masked_equal(eLandsat_b6_emis,
                                                 NO_DATA_VALUE)
    # Harden the mask so it does not change
    eLandsat_b6_emis_masked = eLandsat_b6_emis_masked.harden_mask()

    # Load the warped ASTER NDVI into memory
    ds = gdal.Open(warped_aster_ndvi_name)
    aster_ndvi_data = ds.GetRasterBand(1).ReadAsArray(0, 0, x_dim, y_dim)
    aster_ndvi_masked = np.ma.masked_equal(aster_ndvi_data, NO_DATA_VALUE)
    # Harden the mask so it does not change
    aster_ndvi_masked = aster_ndvi_masked.harden_mask()

    # Save the locations of the gaps in the estimated Landsat B6 EMIS
    # and Aster NDVI data
    aster_b6_emis_gap_locations = np.where(eLandsat_b6_emis == 0)
    aster_b6_emis_no_data_locations = \
        np.where(eLandsat_b6_emis == NO_DATA_VALUE)
    aster_ndvi_gap_locations = np.where(aster_ndvi_data == 0)
    aster_ndvi_no_data_locations = np.where(aster_ndvi_data == NO_DATA_VALUE)

    # Memory cleanup
    del (ds)
    del (eLandsat_b6_emis)
    del (aster_ndvi_data)

    # Normalize Landsat NDVI by max value
    min_ls_ndvi = landsat_ndvi_masked.min()
    max_ls_ndvi = landsat_ndvi_masked.max()
    landsat_ndvi_masked = landsat_ndvi_masked / float(max_ls_ndvi)

    # Normalize ASTER NDVI by max value
    min_aster_ndvi = aster_ndvi_masked.min()
    max_aster_ndvi = aster_ndvi_masked.max()
    aster_ndvi_masked = aster_ndvi_masked / float(max_aster_ndvi)

    # Calculate fractional vegetation cover for both Landsat and ASTER NDVI
    fv_Landsat = 1.0 - ((max_ls_ndvi - landsat_ndvi_masked)
                        / (max_ls_ndvi - min_ls_ndvi))
    fv_Aster = 1.0 - ((max_aster_ndvi - aster_ndvi_masked)
                      / (max_aster_ndvi - min_aster_ndvi))

    # Memory cleanup
    del (landsat_ndvi_masked)
    del (aster_ndvi_masked)

    landsat_soil = None
    landsat_mod = None
    landsat_emis = None
    # Adjust estimated Landsat B6 EMIS for vegetation and snow
    if satellite == 'LANDSAT_7':
        logger.info("Adjusting estimated Landsat 7 B6 EMIS"
                    " for vegetation and snow")
        landsat_soil = ((eLandsat_b6_emis_masked - 0.975 * fv_Aster)
                        / (1.0 - fv_Aster))
        landsat_mod = 0.9848 * fv_Landsat + landsat_soil * (1.0 - fv_Landsat)

        # Create a copy as a non-masked array
        landsat_emis = np.array(landsat_mod)
        landsat_emis[selected_snow_locations] = 0.9869  # Medium snow

    elif satellite == 'LANDSAT_5':
        logger.info("Adjusting estimated Landsat 5 B6 EMIS"
                    " for vegetation and snow")
        landsat_soil = ((eLandsat_b6_emis_masked - 0.975 * fv_Aster)
                        / (1.0 - fv_Aster))
        landsat_mod = 0.9851 * fv_Landsat + landsat_soil * (1.0 - fv_Landsat)

        # Create a copy as a non-masked array
        landsat_emis = np.array(landsat_mod)
        landsat_emis[selected_snow_locations] = 0.9851  # Medium snow

    # Memory cleanup
    del (fv_Landsat)
    del (fv_Aster)
    del (landsat_soil)
    del (landsat_mod)
    del (selected_snow_locations)

    # Add the fill and scan gaps and ASTER gaps back into the results, since
    # they may have been lost
    landsat_emis[aster_b6_emis_no_data_locations] = NO_DATA_VALUE
    landsat_emis[aster_b6_emis_gap_locations] = NO_DATA_VALUE
    landsat_emis[aster_ndvi_no_data_locations] = NO_DATA_VALUE
    landsat_emis[aster_ndvi_gap_locations] = NO_DATA_VALUE
    landsat_emis[landsat_green_no_data_locations] = NO_DATA_VALUE
    landsat_emis[landsat_red_no_data_locations] = NO_DATA_VALUE
    landsat_emis[landsat_nir_no_data_locations] = NO_DATA_VALUE
    landsat_emis[landsat_swir1_no_data_locations] = NO_DATA_VALUE

    # Memory cleanup
    del (aster_b6_emis_no_data_locations)
    del (aster_b6_emis_gap_locations)
    del (aster_ndvi_no_data_locations)
    del (aster_ndvi_gap_locations)
    del (landsat_green_no_data_locations)
    del (landsat_red_no_data_locations)
    del (landsat_nir_no_data_locations)
    del (landsat_swir1_no_data_locations)

    generate_raster_file(driver, 'landsat_emis.tif', x_dim, y_dim,
                         landsat_emis, ds_tmp_transform,
                         ds_tmp_srs.ExportToWkt(), NO_DATA_VALUE,
                         gdal.GDT_Float32)

    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - Do I create an output product for Landsat Emissivity?
    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - ??????????????????????

    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - What else needs to be done?
    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - ??????????????????????

    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - Do I create the LST output product here and now, or not?
    # TODO TODO TODO - ??????????????????????
    # TODO TODO TODO - ??????????????????????

    # Memory cleanup
    del (landsat_emis)


# ============================================================================
if __name__ == '__main__':
    '''
    Description:
      Generate B6 EMIS and ASTER NDVI from ASTER GED tiles for the specified
      Landsat scene.
    '''

    # Build the command line argument parser
    description = ("Retrieve ASTER data application")
    parser = ArgumentParser(description=description)

    # ---- Add parameters ----
    # Required parameters
    parser.add_argument('--xml',
                        action='store', dest='xml_filename', required=True,
                        help="The XML metadata file to use")

    # Parse the command line arguments
    args = parser.parse_args()

    # Configure logging
    logging.basicConfig(format=('%(asctime)s.%(msecs)03d %(process)d'
                                ' %(levelname)-8s'
                                ' %(filename)s:%(lineno)d:%(funcName)s'
                                ' -- %(message)s'),
                        datefmt='%Y-%m-%d %H:%M:%S',
                        filename='aster.log',
                        level=logging.DEBUG)

    logger = logging.getLogger(__name__)

    try:
        # Call the main processing routine
        process(args)
    except Exception, e:
        if hasattr(e, 'output'):
            logger.error("Output [%s]" % e.output)
        logger.exception("Processing failed")
        sys.exit(1)  # EXIT FAILURE

    sys.exit(0)  # EXIT SUCCESS
