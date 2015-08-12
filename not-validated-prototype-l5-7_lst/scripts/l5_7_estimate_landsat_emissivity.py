#! /usr/bin/env python

'''
    FILE: l5-7_landsat_emissivity_from_aster_ged.py

    PURPOSE: Estimates a Landsat Emissivity product from ASTER Emissivity and
             NDVI.  The results are meant to be used for generation of a Land
             Surface Temperature product.

    PROJECT: Land Satellites Data Systems (LSDS) Science Research and
             Development (LSRD) at the USGS EROS

    LICENSE: NASA Open Source Agreement 1.3

    Algorithm Authors:

        Glynn C. Hulley
        Research Scientist
        NASA Jet Propulsion Laboratory
        email: glynn.hulley@nasa.gov

        Simon J. Hook
        Research Scientist
        NASA Jet Propulsion Laboratory
        email: Simon.J.Hook@jpl.nasa.gov

    Date              Programmer               Reason
    ----------------  ------------------------ -------------------------------
    June/2015         Ron Dilley               Initial implementation
'''

import os
import sys
import logging
import math
import requests
import datetime
import numpy as np
from argparse import ArgumentParser
from osgeo import gdal, osr


# Import the metadata api found in the espa-product-formatter project
import metadata_api


# Import local modules
import lst_utilities as util


# ============================================================================
class EstimateLandsatEmissivity(object):
    '''
    Description:
        Defines the processor for generating the estimated Landsat Emissivity
        product.
    '''

    # ------------------------------------------------------------------------
    class LandsatSourceInfo(object):
        '''
        Description:
            Used as a data structure to organize geographic and other image
            information.
        '''

        def __init__(self):
            super(EstimateLandsatEmissivity.LandsatSourceInfo, self).__init__()
            self.north = None
            self.south = None
            self.east = None
            self.west = None
            self.x_pixel_size = None
            self.y_pixel_size = None
            self.min_x_extent = None
            self.max_x_extent = None
            self.min_y_extent = None
            self.max_y_extent = None
            self.dest_proj4 = None

    # ------------------------------------------------------------------------
    def __init__(self, xml_filename, keep_intermediate_data=False):
        super(EstimateLandsatEmissivity, self).__init__()

        server_name = ''
        # Grab the server name from the environment
        if 'ASTER_GED_SERVER_NAME' not in os.environ:
            raise Exception('Environment variable ASTER_GED_SERVER_NAME is'
                            ' not defined')
        else:
            server_name = os.environ.get('ASTER_GED_SERVER_NAME')

        # Grab the server path from the environment or default it
        server_path = os.environ.get('ASTER_GED_SERVER_PATH',
                                     '/ASTT/AG100.003/2000.01.01/')

        # Keep local copies of these
        self.xml_filename = xml_filename
        self.keep_intermediate_data = keep_intermediate_data

        # Create the info object
        self.ls_info = self.LandsatSourceInfo()

        # Specify the no data value we will be using, it also matches the
        # no_data_value for the ASTER data we extract and use
        self.no_data_value = -9999

        # Specify the base URL to use for retrieving the ASTER GED data
        self.base_url_path = ''.join(['http://', server_name, server_path])

        # ASTER GED filename formats
        # AG100.v003.44.-077.0001.h5  (Negative Longitude)
        # or
        # AG100.v003.44.077.0001.h5   (Positive Longitude)
        # Setup the formats to apply to the URL for retrieving ASTER GED tiles
        self.file_n_format = 'AG100.v003.{0:02}.{1:04}.0001'
        self.file_p_format = 'AG100.v003.{0:02}.{1:03}.0001'

        # Initialize these to defaults
        self.toa_green_name = ''
        self.toa_red_name = ''
        self.toa_nir_name = ''
        self.toa_swir1_name = ''
        self.toa_green_scale_factor = 1.0
        self.toa_red_scale_factor = 1.0
        self.toa_nir_scale_factor = 1.0
        self.toa_swir1_scale_factor = 1.0

        self.src_proj4 = None
        self.satellite = None

        # Setup the logger to use
        self.logger = logging.getLogger(__name__)

    # ------------------------------------------------------------------------
    def extract_aster_data(self, emis_ds_name, ndvi_ds_name,
                           lat_ds_name, lon_ds_name):
        '''
        Description:
            Opens the requested files and extracts the associated data, which
            is then returned to the caller.

        Returns: An array of the following information.
            aster_b13_data - Aster Emissivity band 13 data.
            aster_b14_data - Aster Emissivity band 14 data.
            aster_ndvi_data - Aster NDVI band data.
            aster_lat_data - Geolocation Lattitude data.
            aster_lon_data - Geolocation Longitude data.
            x_dim - Number of columns of the data.
            y_dim - Number of rows of the data.
        '''

        try:
            # Open the Emissivity sub-dataset
            data_set = gdal.Open(emis_ds_name)
            if data_set is None:
                raise RuntimeError('GDAL failed to open {0}'
                                   .format(emis_ds_name))

            # The dimensions are the same for all the bands so just use
            # the values from the Emissivity dataset
            x_dim = data_set.RasterXSize
            y_dim = data_set.RasterYSize

            # Retrieve the band 13 data from the HDF5 input
            aster_b13_data = data_set.GetRasterBand(4).ReadAsArray(0, 0,
                                                                   x_dim,
                                                                   y_dim)

            # Retrieve the band 14 data from the HDF5 input
            aster_b14_data = data_set.GetRasterBand(5).ReadAsArray(0, 0,
                                                                   x_dim,
                                                                   y_dim)
            # Open the NDVI sub-dataset
            data_set = gdal.Open(ndvi_ds_name)
            if data_set is None:
                raise RuntimeError('GDAL failed to open {0}'
                                   .format(ndvi_ds_name))

            # Retrieve the NDVI band data from the HDF5 input
            aster_ndvi_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                                    x_dim,
                                                                    y_dim)
            # Open the Latitude sub-dataset
            data_set = gdal.Open(lat_ds_name)
            if data_set is None:
                raise RuntimeError('GDAL failed to open {0}'
                                   .format(lat_ds_name))

            # Retrieve the Latitude data from the HDF5 input
            aster_lat_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                                   x_dim,
                                                                   y_dim)

            # Open the Longitude sub-dataset
            data_set = gdal.Open(lon_ds_name)
            if data_set is None:
                raise RuntimeError('GDAL failed to open {0}'
                                   .format(lon_ds_name))

            # Retrieve the Longitude data from the HDF5 input
            aster_lon_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                                   x_dim,
                                                                   y_dim)

            del data_set

        except Exception:
            raise

        return (aster_b13_data, aster_b14_data, aster_ndvi_data,
                aster_lat_data, aster_lon_data, x_dim, y_dim)

    # ------------------------------------------------------------------------
    def warp_raster_to_match_ls_data(self, src_name, dest_name):
        '''
        Description:
            Executes gdalwarp on the supplied source name to generate a warped
            destination named file that matches the projection and image
            extents and pixel size specified, which were derived from Landsat
            data.
        '''

        cmd = ['gdalwarp', '-wm', '2048', '-multi',
               '-tr', str(self.ls_info.x_pixel_size),
               str(self.ls_info.y_pixel_size),
               '-s_srs', ''.join(["'", self.src_proj4, "'"]),
               '-t_srs', ''.join(["'", self.ls_info.dest_proj4, "'"]),
               '-of', 'GTiff',
               '-overwrite', '-te',
               str(self.ls_info.min_x_extent), str(self.ls_info.min_y_extent),
               str(self.ls_info.max_x_extent), str(self.ls_info.max_y_extent),
               '-srcnodata', str(self.no_data_value),
               '-dstnodata', str(self.no_data_value)]
        cmd.append(src_name)
        cmd.append(dest_name)

        cmd = ' '.join(cmd)

        output = ''
        try:
            self.logger.info('Executing [{0}]'.format(cmd))
            output = util.System.execute_cmd(cmd)
        except Exception:
            self.logger.error('Failed during warping to match Landsat')
            raise
        finally:
            if len(output) > 0:
                self.logger.info(output)

    # ------------------------------------------------------------------------
    def build_ls_emis_data(self, driver):
        '''
        Description:
            Download the ASTER GED tiles that encompass our Landsat scene and
            extract the bands required to generate the Landsat Emissivity data.
            Mosaic the Landsat Emissivity tiles together and then warp them to
            the projection and image extents of the Landsat scenes.  For
            convenience the ASTER NDVI is also extracted and warped to the
            Landsat scenes projection and image extents

        Returns:
            ls_emis_warped_name
              - The name of the reprojected Landsat Emissivity data.
            aster_ndvi_warped_name
              - The name of the reprojected ASTER NDVI data.
        '''

        # The ASTER data is in geographic projection so specify that here
        ds_srs = osr.SpatialReference()
        ds_srs.ImportFromEPSG(4326)

        # Process through the lattitude and longitude ASTER tiles which cover
        # the Landsat scene we are processing
        # - Download them
        # - Extract the Emissivity bands 13 and 14 as well as the NDVI
        # - Generate the Landsat EMIS from the 13 and 14 band data
        ls_emis_mean_filenames = list()
        aster_ndvi_mean_filenames = list()
        for lat in xrange(int(self.ls_info.south), int(self.ls_info.north)+1):
            for lon in xrange(int(self.ls_info.west),
                              int(self.ls_info.east)+1):
                # Build the base filename using the correct format
                filename = ''
                if lon < 0:
                    filename = self.file_n_format.format(lat, lon)
                else:
                    filename = self.file_p_format.format(lat, lon)

                # Build the HDF5 filename for the tile
                h5_file_path = ''.join([filename, '.h5'])

                # Build the URL and download the tile
                url_path = ''.join([self.base_url_path, h5_file_path])
                status_code = util.Web.http_transfer_file(url_path,
                                                          h5_file_path)

                # Check for and handle tiles that are not available in the
                # ASTER data
                if status_code != requests.codes['ok']:
                    if status_code != requests.codes['not_found']:
                        raise Exception('HTTP - Transfer Failed')
                    else:
                        # Advance to the next tile
                        continue

                # ------------------------------------------------------------
                # Build the output tile names
                ls_emis_tile_name = ''.join([filename, '_emis.tif'])
                aster_ndvi_tile_name = ''.join([filename, '_ndvi.tif'])

                # Add the tile names to the list for mosaic building and
                # warping
                ls_emis_mean_filenames.append(ls_emis_tile_name)
                aster_ndvi_mean_filenames.append(aster_ndvi_tile_name)

                # Get the sub-dataset name for Emissivity-Mean
                emis_ds_name = ''.join(['HDF5:"', h5_file_path,
                                        '"://Emissivity/Mean'])
                # Get the sub-dataset name for NDVI-ean
                ndvi_ds_name = ''.join(['HDF5:"', h5_file_path,
                                        '"://NDVI/Mean'])
                # Get the sub-dataset name for Lattitude
                lat_ds_name = ''.join(['HDF5:"', h5_file_path,
                                       '"://Geolocation/Latitude'])
                # Get the sub-dataset name for Longitude
                lon_ds_name = ''.join(['HDF5:"', h5_file_path,
                                       '"://Geolocation/Longitude'])

                self.logger.debug(emis_ds_name)
                self.logger.debug(ndvi_ds_name)
                self.logger.debug(lat_ds_name)
                self.logger.debug(lon_ds_name)

                # ------------------------------------------------------------
                try:
                    (aster_b13_data, aster_b14_data, aster_ndvi_data,
                     aster_lat_data, aster_lon_data, x_dim, y_dim) = (
                        self.extract_aster_data(emis_ds_name, ndvi_ds_name,
                                                lat_ds_name, lon_ds_name))
                except Exception:
                    self.logger.exception('Extracting ASTER data from tile')
                    raise

                # Remove the HDF5 tile since we have extracted all the info we
                # need from it
                if not self.keep_intermediate_data:
                    if os.path.exists(h5_file_path):
                        os.unlink(h5_file_path)

                # ------------------------------------------------------------
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

                # ------------------------------------------------------------
                # Save the no data and gap locations.
                aster_b13_gap_locations = np.where(aster_b13_data == 0)
                aster_b13_no_data_locations = (
                    np.where(aster_b13_data == self.no_data_value))

                # Scale the data
                aster_b13_data = aster_b13_data * 0.001

                # ------------------------------------------------------------
                # Save the no data and gap locations.
                aster_b14_gap_locations = np.where(aster_b14_data == 0)
                aster_b14_no_data_locations = (
                    np.where(aster_b14_data == self.no_data_value))

                # Scale the data
                aster_b14_data = aster_b14_data * 0.001

                # ------------------------------------------------------------
                # Create the estimated Landsat EMIS data
                ls_emis_data = (0.44 * aster_b13_data +
                                0.4 * aster_b14_data + 0.156)

                # Re-apply the no data and gap locations.
                ls_emis_data[aster_b13_gap_locations] = 0
                ls_emis_data[aster_b13_no_data_locations] = self.no_data_value
                ls_emis_data[aster_b14_gap_locations] = 0
                ls_emis_data[aster_b14_no_data_locations] = self.no_data_value

                # Memory cleanup
                del aster_b13_data
                del aster_b14_data
                del aster_b13_gap_locations
                del aster_b14_gap_locations
                del aster_b13_no_data_locations
                del aster_b14_no_data_locations

                # ------------------------------------------------------------
                # Save the no data locations.
                aster_ndvi_no_data_locations = (
                    np.where(aster_ndvi_data == self.no_data_value))

                # Scale the data
                aster_ndvi_data = aster_ndvi_data * 0.01

                # Re-apply the no data locations.
                aster_ndvi_data[aster_ndvi_no_data_locations] = (
                    self.no_data_value)

                # ------------------------------------------------------------
                # Create the estimated Landsat EMIS raster output tile
                try:
                    self.logger.info('Creating an estimated Landsat EMIS tile')
                    util.Geo.generate_raster_file(driver, ls_emis_tile_name,
                                                  ls_emis_data, x_dim, y_dim,
                                                  geo_transform,
                                                  ds_srs.ExportToWkt(),
                                                  self.no_data_value,
                                                  gdal.GDT_Float32)
                except Exception:
                    self.logger.exception('Creating Landsat EMIS tile')
                    raise

                # ------------------------------------------------------------
                # Create the ASTER NDVI raster output tile
                try:
                    self.logger.info('Creating an ASTER NDVI tile')
                    util.Geo.generate_raster_file(driver,
                                                  aster_ndvi_tile_name,
                                                  aster_ndvi_data,
                                                  x_dim, y_dim,
                                                  geo_transform,
                                                  ds_srs.ExportToWkt(),
                                                  self.no_data_value,
                                                  gdal.GDT_Float32)
                except Exception:
                    self.logger.exception('Creating ASTER NDVI tile')
                    raise

                # Memory cleanup
                del ls_emis_data
                del aster_ndvi_data

        # Check to see that we downloaded at least one ASTER tile for
        # processing.
        if len(ls_emis_mean_filenames) == 0:
            raise Exception('No ASTER tiles were downloaded')

        # Save the source proj4 string to use during warping
        self.src_proj4 = ds_srs.ExportToProj4()

        # Define the temporary names
        ls_emis_mosaic_name = 'landsat_emis_mosaic.tif'
        ls_emis_warped_name = 'landsat_emis_warped.tif'
        aster_ndvi_mosaic_name = 'aster_ndvi_mosaic.tif'
        aster_ndvi_warped_name = 'aster_ndvi_warped.tif'

        # Mosaic the estimated Landsat EMIS tiles into the temp EMIS
        try:
            self.logger.info('Building mosaic for estimated Landsat EMIS')
            util.Geo.mosaic_tiles_into_one_raster(ls_emis_mean_filenames,
                                                  ls_emis_mosaic_name,
                                                  self.no_data_value)
        except Exception:
            self.logger.exception('Mosaicing EMIS tiles')
            raise

        # Mosaic the ASTER NDVI tiles into the temp NDVI
        try:
            self.logger.info('Building mosaic for ASTER NDVI')
            util.Geo.mosaic_tiles_into_one_raster(aster_ndvi_mean_filenames,
                                                  aster_ndvi_mosaic_name,
                                                  self.no_data_value)
        except Exception:
            self.logger.exception('Mosaicing ASTER NDVI tiles')
            raise

        if not self.keep_intermediate_data:
            # Cleanup the estimated Landsat EMIS tiles
            for emis_filename in ls_emis_mean_filenames:
                if os.path.exists(emis_filename):
                    os.unlink(emis_filename)

            # Cleanup the ASTER NDVI tiles
            for ndvi_filename in aster_ndvi_mean_filenames:
                if os.path.exists(ndvi_filename):
                    os.unlink(ndvi_filename)

        # Warp estimated Landsat EMIS to match the Landsat data
        try:
            self.logger.info('Warping estimated Landsat EMIS to'
                             ' match Landsat data')
            self.warp_raster_to_match_ls_data(ls_emis_mosaic_name,
                                              ls_emis_warped_name)
        except Exception:
            self.logger.exception('Warping EMIS to match Landsat data')
            raise

        # Warp ASTER NDVI to match the Landsat data
        try:
            self.logger.info('Warping ASTER NDVI to match Landsat data')
            self.warp_raster_to_match_ls_data(aster_ndvi_mosaic_name,
                                              aster_ndvi_warped_name)
        except Exception:
            self.logger.exception('Warping ASTER NDVI to match Landsat data')
            raise

        if not self.keep_intermediate_data:
            # Cleanup the temp files
            if os.path.exists(ls_emis_mosaic_name):
                os.unlink(ls_emis_mosaic_name)
            if os.path.exists(aster_ndvi_mosaic_name):
                os.unlink(aster_ndvi_mosaic_name)

        return (ls_emis_warped_name, aster_ndvi_warped_name)

    # ------------------------------------------------------------------------
    def retrieve_metadata_information(self):
        '''
        Description:
            Loads and reads required information from the metadata XML file.
        '''

        # Read the XML metadata
        espa_xml = metadata_api.parse(self.xml_filename, silence=True)
        # Grab the global metadata object
        gm = espa_xml.get_global_metadata()
        # Grab the bands metadata object
        bands = espa_xml.get_bands()

        toa_bt_name = ''  # Only one that is local

        # Find the TOA bands to extract information from
        for band in bands.band:
            if band.product == 'toa_refl' and band.name == 'toa_band2':
                self.toa_green_name = band.get_file_name()
                self.toa_green_scale_factor = float(band.scale_factor)

            if band.product == 'toa_refl' and band.name == 'toa_band3':
                self.toa_red_name = band.get_file_name()
                self.toa_red_scale_factor = float(band.scale_factor)

            if band.product == 'toa_refl' and band.name == 'toa_band4':
                self.toa_nir_name = band.get_file_name()
                self.toa_nir_scale_factor = float(band.scale_factor)

            if band.product == 'toa_refl' and band.name == 'toa_band5':
                self.toa_swir1_name = band.get_file_name()
                self.toa_swir1_scale_factor = float(band.scale_factor)

            if band.product == 'toa_bt' and band.category == 'image':
                # Get the output pixel size
                self.ls_info.x_pixel_size = band.pixel_size.x
                self.ls_info.y_pixel_size = band.pixel_size.y

                toa_bt_name = band.get_file_name()

                # Get the output proj4 string
                self.ls_info.dest_proj4 = (
                    util.Geo.get_proj4_projection_string(toa_bt_name))

        # Error if we didn't find the required TOA bands in the data
        if len(self.toa_green_name) <= 0:
            raise Exception('Failed to find the TOA GREEN band'
                            ' in the input data')
        if len(self.toa_red_name) <= 0:
            raise Exception('Failed to find the TOA RED band'
                            ' in the input data')
        if len(self.toa_nir_name) <= 0:
            raise Exception('Failed to find the TOA NIR band'
                            ' in the input data')
        if len(self.toa_swir1_name) <= 0:
            raise Exception('Failed to find the TOA SWIR1 band'
                            ' in the input data')
        if len(toa_bt_name) <= 0:
            raise Exception('Failed to find the TOA BT band'
                            ' in the input data')

        # Determine the bounding geographic coordinates for the ASTER tiles we
        # will need
        self.ls_info.north = math.ceil(gm.bounding_coordinates.north)
        self.ls_info.south = math.floor(gm.bounding_coordinates.south)
        self.ls_info.east = math.ceil(gm.bounding_coordinates.east)
        self.ls_info.west = math.floor(gm.bounding_coordinates.west)

        # Determine the UTM projection corner points
        for cp in gm.projection_information.corner_point:
            if cp.location == 'UL':
                self.ls_info.min_x_extent = cp.x
                self.ls_info.max_y_extent = cp.y
            if cp.location == 'LR':
                self.ls_info.max_x_extent = cp.x
                self.ls_info.min_y_extent = cp.y

        # Adjust the UTM coordinates for image extents becuse they are in
        # center of pixel, and we need to supply the warping with actual
        # extents
        self.ls_info.min_x_extent = (self.ls_info.min_x_extent -
                                     self.ls_info.x_pixel_size * 0.5)
        self.ls_info.max_x_extent = (self.ls_info.max_x_extent +
                                     self.ls_info.x_pixel_size * 0.5)
        self.ls_info.min_y_extent = (self.ls_info.min_y_extent -
                                     self.ls_info.y_pixel_size * 0.5)
        self.ls_info.max_y_extent = (self.ls_info.max_y_extent +
                                     self.ls_info.y_pixel_size * 0.5)

        # Save for later
        self.satellite = gm.satellite

        del bands
        del gm
        del espa_xml

    # ------------------------------------------------------------------------
    # TODO - NEED TO PROCESS A COASTAL SCENE BECAUSE MAY NOT HAVE ASTER TILE
    #        DATA FOR SOME OF THE SCENE AND WILL NEED TO DO SOMETHING ELSE
    #      - I have implemented a solution for this, but have not been able to
    #        test it.  I have not been able to find a scene that has this
    #        condition.
    # ------------------------------------------------------------------------
    def generate_product(self):
        '''
        Description:
            Provides the main processing algorithm for generating the
            estimated Landsat emissivity product.  It produces the final
            emissivity product.
        '''

        self.logger = logging.getLogger(__name__)

        self.logger.info('Start - Estimate Landsat Emissivity')

        try:
            self.retrieve_metadata_information()
        except Exception:
            self.logger.exception('Failed reading input XML metadata file')
            raise

        # Register all the gdal drivers and choose the GeoTiff for our temp
        # output
        gdal.AllRegister()
        geotiff_driver = gdal.GetDriverByName('GTiff')
        envi_driver = gdal.GetDriverByName('ENVI')

        # ====================================================================
        # Build NDVI in memory
        self.logger.info('Building TOA based NDVI band for Landsat data')

        # NIR ----------------------------------------------------------------
        data_set = gdal.Open(self.toa_nir_name)
        x_dim = data_set.RasterXSize  # They are all the same size
        y_dim = data_set.RasterYSize
        ls_nir_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                            x_dim, y_dim)
        nir_no_data_locations = np.where(ls_nir_data == self.no_data_value)
        ls_nir_data = ls_nir_data * self.toa_nir_scale_factor

        # RED ----------------------------------------------------------------
        data_set = gdal.Open(self.toa_red_name)
        ls_red_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                            x_dim, y_dim)
        red_no_data_locations = np.where(ls_red_data == self.no_data_value)
        ls_red_data = ls_red_data * self.toa_red_scale_factor

        # NDVI ---------------------------------------------------------------
        # Also scale from (-1.0, 1.0) to (0.0, 1.0) the ASTER range
        ls_ndvi_data = (((ls_nir_data - ls_red_data) /
                         (ls_nir_data + ls_red_data)) + 1.0) / 2.0

        # Cleanup no data locations
        ls_ndvi_data[nir_no_data_locations] = self.no_data_value
        ls_ndvi_data[red_no_data_locations] = self.no_data_value

        # Memory cleanup
        del ls_red_data
        del ls_nir_data
        del nir_no_data_locations
        del red_no_data_locations

        # ====================================================================
        # Build NDSI in memory
        self.logger.info('Building TOA based NDSI band for Landsat data')

        # GREEN --------------------------------------------------------------
        data_set = gdal.Open(self.toa_green_name)
        ls_green_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                              x_dim, y_dim)
        green_no_data_locations = (
            np.where(ls_green_data == self.no_data_value))
        ls_green_data = ls_green_data * self.toa_green_scale_factor

        # SWIR1 --------------------------------------------------------------
        data_set = gdal.Open(self.toa_swir1_name)
        ls_swir1_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                              x_dim, y_dim)
        swir1_no_data_locations = (
            np.where(ls_swir1_data == self.no_data_value))
        ls_swir1_data = ls_swir1_data * self.toa_swir1_scale_factor

        # Build the Landsat TOA NDSI data
        self.logger.info('Building TOA based NDSI for Landsat data')
        ls_ndsi_data = ((ls_green_data - ls_swir1_data) /
                        (ls_green_data + ls_swir1_data))

        # Cleanup no data locations
        ls_ndsi_data[green_no_data_locations] = self.no_data_value
        # Cleanup no data locations
        ls_ndsi_data[swir1_no_data_locations] = self.no_data_value

        # Memory cleanup
        del ls_green_data
        del ls_swir1_data
        del green_no_data_locations
        del swir1_no_data_locations

        # Save for the output products
        ds_tmp_srs = osr.SpatialReference()
        ds_tmp_srs.ImportFromWkt(data_set.GetProjection())
        ds_tmp_transform = data_set.GetGeoTransform()

        # Memory cleanup
        del data_set

        # Save the locations for the specfied snow pixels
        self.logger.info('Determine snow pixel locations')
        selected_snow_locations = np.where(ls_ndsi_data > 0.4)

        # Save ndvi and ndsi no data locations
        ndvi_no_data_locations = np.where(ls_ndvi_data == self.no_data_value)
        ndsi_no_data_locations = np.where(ls_ndsi_data == self.no_data_value)

        # Memory cleanup
        del ls_ndsi_data

        # Turn all negative values to zero
        # Use a realy small value so that we don't have negative zero (-0.0)
        ls_ndvi_data[ls_ndvi_data < 0.0000001] = 0

        # Build the estimated Landsat EMIS data from the ASTER GED data and
        # warp it to the Landsat scenes projection and image extents
        # For convenience the ASTER NDVI is also extracted and warped to the
        # Landsat scenes projection and image extents
        self.logger.info('Build thermal emissivity band and'
                         ' retrieve ASTER NDVI')
        (ls_emis_warped_name,
         aster_ndvi_warped_name) = self.build_ls_emis_data(geotiff_driver)

        # Load the warped estimated Landsat EMIS into memory
        data_set = gdal.Open(ls_emis_warped_name)
        ls_emis_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                             x_dim, y_dim)
        ls_emis_gap_locations = np.where(ls_emis_data == 0)
        ls_emis_no_data_locations = (
            np.where(ls_emis_data == self.no_data_value))

        # Load the warped ASTER NDVI into memory
        data_set = gdal.Open(aster_ndvi_warped_name)
        aster_ndvi_data = data_set.GetRasterBand(1).ReadAsArray(0, 0,
                                                                x_dim, y_dim)
        aster_ndvi_gap_locations = np.where(aster_ndvi_data == 0)
        aster_ndvi_no_data_locations = (
            np.where(aster_ndvi_data == self.no_data_value))

        # Turn all negative values to zero
        # Use a realy small value so that we don't have negative zero (-0.0)
        aster_ndvi_data[aster_ndvi_data < 0.0000001] = 0

        # Memory cleanup
        del data_set

        if not self.keep_intermediate_data:
            # Cleanup the temp files since we have them in memory
            if os.path.exists(ls_emis_warped_name):
                os.unlink(ls_emis_warped_name)
            if os.path.exists(aster_ndvi_warped_name):
                os.unlink(aster_ndvi_warped_name)

        self.logger.info('Normalizing Landsat and ASTER NDVI')
        # Normalize Landsat NDVI by max value
        # TODO TODO TODO - Min is always Zero here, but wonder if it should be the lowest above zero.
        min_ls_ndvi = ls_ndvi_data.min()
        max_ls_ndvi = ls_ndvi_data.max()
        self.logger.info('Min LS NDVI {0}'.format(min_ls_ndvi))
        self.logger.info('Max LS NDVI {0}'.format(max_ls_ndvi))
        ls_ndvi_data = ls_ndvi_data / float(max_ls_ndvi)

        # Normalize ASTER NDVI by max value
        # TODO TODO TODO - Min is always Zero here, but wonder if it should be the lowest above zero.
        min_ls_ndvi = ls_ndvi_data.min()
        min_aster_ndvi = aster_ndvi_data.min()
        max_aster_ndvi = aster_ndvi_data.max()
        self.logger.info('Min ASTER NDVI {0}'.format(min_aster_ndvi))
        self.logger.info('Max ASTER NDVI {0}'.format(max_aster_ndvi))
        aster_ndvi_data = aster_ndvi_data / float(max_aster_ndvi)

        # Calculate fractional veg-cover for both Landsat and ASTER NDVI
        self.logger.info('Calculating fractional vegetation cover')
        fv_Landsat = 1.0 - ((max_ls_ndvi - ls_ndvi_data) /
                            (max_ls_ndvi - min_ls_ndvi))
        fv_Aster = 1.0 - ((max_aster_ndvi - aster_ndvi_data) /
                          (max_aster_ndvi - min_aster_ndvi))

        # Memory cleanup
        del ls_ndvi_data
        del aster_ndvi_data

        # Soil - From prototype code variable name
        ls_emis_final = ((ls_emis_data - 0.975 * fv_Aster) /
                         (1.0 - fv_Aster))

        # Memory cleanup
        del ls_emis_data
        del fv_Aster

        snow_emis_value = None

        # Adjust estimated Landsat EMIS for vegetation and snow, to generate
        # the final Landsat EMIS data
        if self.satellite == 'LANDSAT_7':
            self.logger.info('Adjusting estimated Landsat 7 EMIS'
                             ' for vegetation and snow')
            # Mod - From prototype code variable name
            ls_emis_final = (0.9848 * fv_Landsat +
                             ls_emis_final * (1.0 - fv_Landsat))

            snow_emis_value = 0.9869

        elif self.satellite == 'LANDSAT_5':
            self.logger.info('Adjusting estimated Landsat 5 EMIS'
                             ' for vegetation and snow')
            # Mod - From prototype code variable name
            ls_emis_final = (0.9851 * fv_Landsat +
                             ls_emis_final * (1.0 - fv_Landsat))

            snow_emis_value = 0.9851

        # Medium snow
        ls_emis_final[selected_snow_locations] = snow_emis_value

        # Memory cleanup
        del fv_Landsat
        del selected_snow_locations

        # Add the fill and scan gaps and ASTER gaps back into the results,
        # since they may have been lost
        self.logger.info('Adding fill and data gaps back into the estimated'
                         ' Landsat emissivity results')
        ls_emis_final[ls_emis_no_data_locations] = self.no_data_value
        ls_emis_final[ls_emis_gap_locations] = self.no_data_value
        ls_emis_final[aster_ndvi_no_data_locations] = self.no_data_value
        ls_emis_final[aster_ndvi_gap_locations] = self.no_data_value
        ls_emis_final[ndvi_no_data_locations] = self.no_data_value
        ls_emis_final[ndsi_no_data_locations] = self.no_data_value

        # Memory cleanup
        del ls_emis_no_data_locations
        del ls_emis_gap_locations
        del aster_ndvi_no_data_locations
        del aster_ndvi_gap_locations

        product_id = self.xml_filename.split('.xml')[0]
        ls_emis_img_filename = ''.join([product_id, '_emis', '.img'])
        ls_emis_hdr_filename = ''.join([product_id, '_emis', '.hdr'])
        ls_emis_aux_filename = ''.join([ls_emis_img_filename, '.aux', '.xml'])

        self.logger.info('Creating {0}'.format(ls_emis_img_filename))
        util.Geo.generate_raster_file(envi_driver, ls_emis_img_filename,
                                      ls_emis_final, x_dim, y_dim,
                                      ds_tmp_transform,
                                      ds_tmp_srs.ExportToWkt(),
                                      self.no_data_value, gdal.GDT_Float32)

        self.logger.info('Updating {0}'.format(ls_emis_hdr_filename))
        util.Geo.update_envi_header(ls_emis_hdr_filename, self.no_data_value)

        # Remove the *.aux.xml file generated by GDAL
        if os.path.exists(ls_emis_aux_filename):
            os.unlink(ls_emis_aux_filename)

        self.logger.info('Adding {0} to {1}'.format(ls_emis_img_filename,
                                                    self.xml_filename))
        # Add the estimated Landsat emissivity to the metadata XML
        espa_xml = metadata_api.parse(self.xml_filename, silence=True)
        bands = espa_xml.get_bands()
        sensor_code = product_id[0:3]
        source_product = 'toa_refl'

        # Find the TOA Band 1 to use for the specific band details
        base_band = None
        for band in bands.band:
            if band.product == source_product and band.name == 'toa_band1':
                base_band = band

        if base_band is None:
            raise Exception('Failed to find the TOA BLUE band'
                            ' in the input data')

        emis_band = metadata_api.band(product='lst_temp',
                                      source=source_product,
                                      name='landsat_emis',
                                      category='image',
                                      data_type='FLOAT32',
                                      nlines=base_band.get_nlines(),
                                      nsamps=base_band.get_nsamps(),
                                      fill_value=str(self.no_data_value))

        emis_band.set_short_name('{0}EMIS'.format(sensor_code))
        emis_band.set_long_name('Landsat emissivity estimated from ASTER GED'
                                ' data')
        emis_band.set_file_name(ls_emis_img_filename)
        emis_band.set_data_units('Emissivity Coefficient')

        pixel_size = metadata_api.pixel_size(base_band.pixel_size.x,
                                             base_band.pixel_size.x,
                                             base_band.pixel_size.units)
        emis_band.set_pixel_size(pixel_size)

        valid_range = metadata_api.valid_range(min=0.0, max=1.0)
        emis_band.set_valid_range(valid_range)

        # Set the date, but first clean the microseconds off of it
        production_date = (
            datetime.datetime.strptime(datetime.datetime.now().
                                       strftime('%Y-%m-%dT%H:%M:%S'),
                                       '%Y-%m-%dT%H:%M:%S'))

        emis_band.set_production_date(production_date)

        emis_band.set_app_version(util.Version.app_version())

        bands.add_band(emis_band)

        # Write the XML metadata file out
        with open(self.xml_filename, 'w') as fd:
            metadata_api.export(fd, espa_xml)

        # Memory cleanup
        del ls_emis_final

        self.logger.info('Completed - Estimate Landsat Emissivity')


# ============================================================================
if __name__ == '__main__':
    '''
    Description:
        Generate Landsat EMIS and ASTER NDVI from ASTER GED tiles for the
        specified Landsat scene.
    '''

    # Build the command line argument parser
    description = ('Estimates Landsat Emissivity from ASTER GED data')
    parser = ArgumentParser(description=description)

    # ---- Add parameters ----
    # Required parameters
    parser.add_argument('--xml',
                        action='store', dest='xml_filename',
                        required=False, default=None,
                        help='The XML metadata file to use')

    # Optional parameters
    parser.add_argument('--keep-intermediate-data',
                        action='store_true', dest='keep_intermediate_data',
                        required=False, default=False,
                        help='Keep any intermediate data generated')

    parser.add_argument('--debug',
                        action='store_true', dest='debug',
                        required=False, default=False,
                        help='Turn debug messaging on')

    parser.add_argument('--version',
                        action='store_true', dest='version',
                        required=False, default=False,
                        help='Reports the version of the software')

    # Parse the command line arguments
    args = parser.parse_args()

    # Report the version and exit
    if args.version:
        print 'Version: {0}'.format(util.Version.version_text())
        sys.exit(0)  # EXIT SUCCESS

    # Verify that the --xml parameter was specified
    if args.xml_filename is None:
        raise Exception('--xml must be specified on the command line')

    debug_level = logging.INFO
    if args.version:
        debug_level = logging.DEBUG

    # Configure logging
    logging.basicConfig(format=('%(asctime)s.%(msecs)03d %(process)d'
                                ' %(levelname)-8s'
                                ' %(filename)s:%(lineno)d:%(funcName)s'
                                ' -- %(message)s'),
                        datefmt='%Y-%m-%d %H:%M:%S',
                        level=debug_level)

    logger = logging.getLogger(__name__)

    try:
        # Create the processor object
        processor = EstimateLandsatEmissivity(args.xml_filename,
                                              args.keep_intermediate_data)

        # Call the main processing routine
        processor.generate_product()
    except Exception:
        logger.exception('Processing failed')
        sys.exit(1)  # EXIT FAILURE

    sys.exit(0)  # EXIT SUCCESS
