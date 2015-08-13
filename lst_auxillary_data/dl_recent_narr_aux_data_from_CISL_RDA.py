#! /usr/bin/env python
'''
    PURPOSE: Retieves archived NARR3D files from the CISL RDA for the dates
             requested.  Extracts the variables LST requires (HGT, TMP, SPFH)
             and repackages them into our internal location and filenames.

    PROJECT: Land Satellites Data Systems Science Research and Development
             (LSRD) at the USGS EROS

    LICENSE: NASA Open Source Agreement 1.3

    NOTES:

          NCEP     - National Centers for Environmental Prediction
                     http://www.ncep.noaa.gov

          NARR     - NCEP North American Regional Reanalysis

          CISL RDA - Computational & Information Systems Lab
                     Research Data Archive http://rda.ucar.edu

          NCAR     - National Center for Atmospheric Research
                     http://ncar.ucar.edu

          UCAR     - University Corporation for Atmospheric Research
                     http://www2.ucar.edu

    HISTORY:

    Date              Reason
    ----------------  --------------------------------------------------------
    July/2015         Initial implementation
'''
import os
import sys
import shutil
import logging
import errno
import commands
import requests
import calendar
import itertools
import multiprocessing as mp
from cStringIO import StringIO
from argparse import ArgumentParser
from osgeo import gdal, osr
from time import sleep
from datetime import datetime, timedelta
from contextlib import closing
import collections
import json


def debug(tag, message):
    logger = logging.getLogger(tag)
    logger.debug(message)


# ============================================================================
class Web(object):
    '''
    Description:
        Provides methods for interfacing with web resources.
    '''

    # ------------------------------------------------------------------------
    class Session(object):
        '''
        Description:
            Manages an http(s) session.
        '''

        # --------------------------------------------------------------------
        def __init__(self, max_retries=3, block_size=None, timeout=300.0):
            super(Web.Session, self).__init__()

            self.logger = logging.getLogger(__name__)

            self.session = requests.Session()

            self.timeout = timeout

            # Determine if we are streaming or not based on block_size
            self.block_size = block_size
            self.stream = False
            if self.block_size is not None:
                self.stream = True

            adapter = requests.adapters.HTTPAdapter(max_retries=max_retries)
            self.session.mount('http://', adapter)
            self.session.mount('https://', adapter)

        # --------------------------------------------------------------------
        def login(self, login_url=None, login_data=None):
            '''
            Description:
                Provides for establishing a logged in session.
            '''

            # Verify that a login url was provided
            if login_url is None:
                raise Exception('{login_url} not defined')

            # Verify that login data was provided
            if login_data is None:
                raise Exception('{login_data} not defined')

            # Login to the site
            self.session.post(url=login_url, data=login_data)

        # --------------------------------------------------------------------
        def _get_file(self, download_url, destination_file, headers=None):
            '''
            Notes: Downloading this way will place the whole source file into
                   memory before dumping to the local file.
            '''

            req = self.session.get(url=download_url, timeout=self.timeout,
                                   headers=headers)

            if not req.ok:
                self.logger.error('HTTP - Transfer of [{0}] - FAILED'
                                  .format(download_url))
                # The raise_for_status gets caught by this try's except block
                req.raise_for_status()

            # Write the downloaded data to the destination file
            with open(destination_file, 'wb') as local_fd:
                local_fd.write(req.content)

                return True

        # --------------------------------------------------------------------
        def _stream_file(self, download_url, destination_file, headers=None):
            '''
            Notes: Downloading this way streams 'block_size' of data at a
                   time.
            '''

            retrieved_bytes = 0
            with closing(self.session.get(url=download_url,
                                          timeout=self.timeout,
                                          stream=self.stream,
                                          headers=headers)) as req:
                file_size = int(req.headers['content-length'])

                # Set block size based on streaming
                if self.stream:
                    block_size = self.block_size
                else:
                    block_size = file_size

                # Write the downloaded data to the destination file
                with open(destination_file, 'wb') as local_fd:
                    for data_chunk in req.iter_content(block_size):
                        local_fd.write(data_chunk)
                        retrieved_bytes += len(data_chunk)

                if retrieved_bytes != file_size:
                    raise Exception("Transfer Failed - HTTP -"
                                    " Retrieved %d out of %d bytes"
                                    % (retrieved_bytes, file_size))
                else:
                    return True

        # --------------------------------------------------------------------
        def http_transfer_file(self, download_url, destination_file,
                               headers=None):
            '''
            Description:
                Use http to transfer a file from a source location to a
                destination file on the localhost.

            Returns:
                status_code - One of the following
                            - 200, requests.codes['ok']
                            - 404, requests.codes['not_found']:
                            - 503, requests.codes['service_unavailable']:

            Notes:
                If a 503 is returned, the logged exception should be reviewed
                to determine the real cause of the error.
            '''

            self.logger.info(download_url)

            status_code = requests.codes['ok']
            retry_attempt = 0
            done = False
            while not done:
                status_code = requests.codes['ok']
                req = None
                try:

                    # if self.block_size is not None:
                    done = self._stream_file(download_url,
                                             destination_file)
                    # else:
                    #    done = self._get_file(download_url, destination_file)

                    if done:
                        self.logger.info("Transfer Complete - HTTP")

                except Exception:
                    self.logger.exception('HTTP - Transfer Issue')

                    if req is not None:
                        status_code = req.status_code

                    if status_code != requests.codes['not_found']:
                        if retry_attempt > 3:
                            self.logger.info('HTTP - Transfer Failed'
                                             ' - exceeded retry limit')
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
class System(object):
    '''
    Description:
        Provides methods for interfacing with the host server.
    '''

    base_aux_dir = None

    @classmethod
    def get_arch_filename(cls, variable, year, month, day, hour, ext):
        # archive_name_format.format(variable, year, month, day, hour*100,'hdr')
        return (Config.get('archive_name_format')
                      .format(variable, year, month, day, hour*100, ext))

    @classmethod
    def get_arch_dir(cls, year, month, day):
        # archive_directory_format.format(base_aux_dir, year, month, day)
        return (Config.get('archive_directory_format')
                      .format(cls.base_aux_dir, year, month, day))

    @classmethod
    def get_base_aux_dir(cls):
        if cls.base_aux_dir is None:  # Check if its already stored
            logger = logging.getLogger(__name__)
            cls.base_aux_dir = os.environ.get('LST_AUX_DIR')
            # print("$LST_AUX_DIR="+str(base_aux_dir))
            if cls.base_aux_dir is None:
                logger.info('Missing environment variable LST_AUX_DIR')
                sys.exit(1)

            if not os.path.isdir(cls.base_aux_dir):
                logger.info('LST_AUX_DIR directory does not exist')
                sys.exit(1)
        return cls.base_aux_dir

    # ------------------------------------------------------------------------
    @staticmethod
    def execute_cmd(cmd):
        '''
        Description:
            Execute a command line and return the terminal output or raise an
            exception

        Returns:
            output - The stdout and/or stderr from the executed command.
        '''

        logger = logging.getLogger(__name__)

        output = ''

        logger.info('Executing [{0}]'.format(cmd))
        (status, output) = commands.getstatusoutput(cmd)

        if status < 0:
            message = 'Application terminated by signal [{0}]'.format(cmd)
            if len(output) > 0:
                message = ' Stdout/Stderr is: '.join([message, output])
            raise Exception(message)

        if status != 0:
            message = 'Application failed to execute [{0}]'.format(cmd)
            if len(output) > 0:
                message = ' Stdout/Stderr is: '.join([message, output])
            raise Exception(message)

        if os.WEXITSTATUS(status) != 0:
            message = ('Application [{0}] returned error code [{1}]'
                       .format(cmd, os.WEXITSTATUS(status)))
            if len(output) > 0:
                message = ' Stdout/Stderr is: '.join([message, output])
            raise Exception(message)

        return output

    # ------------------------------------------------------------------------
    @staticmethod
    def create_directory(directory):
        '''
        Description:
            Create the specified directory with some error checking.
        '''

        # Create/Make sure the directory exists
        try:
            os.makedirs(directory, mode=0755)
        except OSError as ose:
            if ose.errno == errno.EEXIST and os.path.isdir(directory):
                pass
            else:
                raise


class Config(object):
    config = None
    URL_FMT = 'http://ftp.cpc.ncep.noaa.gov/wd51we/NARR_archive/{0}'
    EXT_NAME_FMT = 'rcdas.{0:03}{1:02}{2:02}{3:02}.awip32.merged'

    @classmethod
    def read_config(cls, cfg_file='lst_auxillary.config.example'):
        # Load the file
        with open(cfg_file, 'r') as fd:
            lines = list()
            for line in fd:
                # Skip rudimentary comments
                if line.strip().startswith('#'):
                    continue

                lines.append(line)

            cls.config = json.loads(' '.join(lines))

        if cls.config is None:
            raise Exception('Failed loading configuration')
        return cls.config

    @classmethod
    def get(cls, attr):
        if cls.config is None:
            cls.read_config()
        if attr is 'ncep_url_format':
            return cls.URL_FMT
        if attr is 'remote_name_format':
            return cls.EXT_NAME_FMT
        return cls.config[attr]

# ============================================================================
# NAME_FORMAT = 'NARR3D_{0:04}{1:02}_{2:02}{3:02}'
def get_requested_file_list(s_date, e_date):
    '''
    Description:
        Determines all of the base filenames to process based on the dates
        provided.
    '''
    NAME_FORMAT = 'rcdas.{0}.awip32.merged'  # .format(year, month, day, hour)
    # Zero the min and sec. Make sure hours is multiple of 3.
    s_date.replace(hour=s_date.hour/3*3, minute=0, second=0)
    # print('Start date was adjusted to: ' + s_date.isoformat())
    hours_3 = timedelta(hours=3)
    c_date = s_date

    while c_date <= e_date:
        datetime_formatted = datetime.strftime(c_date, '%Y%m%d%H')
        yield(NAME_FORMAT.format(datetime_formatted))
        c_date += hours_3

# ============================================================================

def process_grib_for_variable(args):
    '''
    Description:
        Extract the specified variable from the grib file and archive it.
    '''
    # ARCH_FMT = 'NARR_3D.{0}.{1:04}{2:02}{3:02}.{4:04}.{5}'
    # DIR_FMT = '{0}/{1:0>4}/{2:0>2}/{3:0>2}'

    variable = args[0]
    grib_file = args[1]

    logger = logging.getLogger(__name__)

    logger.info("Processing [{0}]".format(grib_file))

    narr = NarrData.from_external_name(grib_file)

    hdr_name = narr.get_internal_filename(variable, 'hdr')
    grb_name = narr.get_internal_filename(variable, 'grb')

    # Create inventory/header file to extract the variable data
    cmd = ['wgrib', grib_file, '|', 'grep', variable, '>', hdr_name]
    cmd = ' '.join(cmd)
    output = ''
    try:
        logger.info('Executing [{0}]'.format(cmd))
        output = System.execute_cmd(cmd)
    except:
        raise
    finally:
        if len(output) > 0:
            logger.info(output)

    # Create grib files for each variable
    cmd = ['cat', hdr_name, '|',
           'wgrib', grib_file, '-i', '-grib', '-o', grb_name]
    cmd = ' '.join(cmd)
    output = ''
    try:
        logger.info('Executing [{0}]'.format(cmd))
        output = System.execute_cmd(cmd)
    except:
        raise
    finally:
        if len(output) > 0:
            logger.info(output)

    # Create new inventory/header file for the variable
    cmd = ['wgrib', grb_name, '|', 'grep', variable, '>', hdr_name]
    cmd = ' '.join(cmd)
    output = ''
    try:
        logger.info('Executing [{0}]'.format(cmd))
        output = System.execute_cmd(cmd)
    except:
        raise
    finally:
        if len(output) > 0:
            logger.info(output)

    # Determine the directory to place the data and create it if it does not
    # exist
    dest_path = narr.get_internal_drectory()

    System.create_directory(dest_path)

    # Archive the files
    logger.info('Archiving into [{0}]'.format(dest_path))
    # GRIB
    dest_file = os.path.join(dest_path, grb_name)
    shutil.copyfile(grb_name, dest_file)
    # HEADER
    dest_file = os.path.join(dest_path, hdr_name)
    shutil.copyfile(hdr_name, dest_file)

    # Cleanup the working directory
    if os.path.exists(grb_name):
        os.unlink(grb_name)
    if os.path.exists(hdr_name):
        os.unlink(hdr_name)


def download_file_list(grib_file_list, block_size):
    logger = logging.getLogger(__name__)
    # Establish a logged in session
    session = Ncep.get_session()

    for grib_file in grib_file_list:
        logger.info('Retrieving {0}'.format(grib_file))

        # http://rda.ucar.edu/data/ds608.0/3HRLY/1979/NARR3D_197901_0103.tar
        url = Ncep.get_url(grib_file)

        session.http_transfer_file(url, grib_file)


def process_file_list(grib_file_list):
    list_var_gribs = []
    for grib_file in grib_file_list:
        vargrib = [('HGT', grib_file), ('TMP', grib_file), ('SPFH', grib_file)]
        list_var_gribs.extend(vargrib)

    for vg in list_var_gribs:
        process_grib_for_variable(vg)

    # Process each sub-file and archive the results using a process pool
    # pool = mp.Pool(int(os.environ.get('OMP_NUM_THREADS', 1)))
    # pool.map(process_grib_for_variable, list_var_gribs)

    for grib_file in grib_file_list:  # Cleanup - Extracted grib files
        if os.path.exists(grib_file):
            os.unlink(grib_file)


def substring_between(s, start, finish):
    '''Find string between two substrings'''
    end_of_start = s.index(start) + len(start)
    start_of_finish = s.index(finish, end_of_start)
    return s[end_of_start:start_of_finish]


class Ncep(object):
    ''' Sample reponse of the list of files
    '<tr><td><a href="rcdas.2015010300.awip32.merged.b">
        rcdas.2015010300.awip32.merged.b</a></td>
    <td align="right">08-Jan-2015 10:12  </td>
    <td align="right">1.3M</td></tr>\n'
    '''
    mtime_by_name = None
    session = None

    # NOAA_FMT.format(year, month, day, hour)
    @staticmethod
    def get_url(filename):
        return Config.get('ncep_url_format').format(filename)

    @staticmethod
    def get_filename(year, month, day, hour):
        fmt = Config.get('remote_name_format')
        return fmt.format(year, month, day, hour)

    @classmethod
    def download_file(cls, filename):
        logger = logging.getLogger(__name__)
        logger.info('Retrieving {0}'.format(filename))
        cls.get_session().http_transfer_file(cls.get_url(filename),
                                             filename)

    @staticmethod
    def get_list_of_external_data():
        ArchiveData = collections.namedtuple('ArchiveData',
                                             ['name', 'mtime', 'size'])
        lines_thrown = 0
        data_list = []

        response = requests.get(Ncep.get_url(''))
        for line in response.iter_lines():
            if('awip' not in line):
                lines_thrown = lines_thrown + 1
                continue  # go to next line
            (garbage, partial_line) = line.split('">', 1)
            (name, partial_line) = partial_line.split('</a>', 1)
            (garbage, partial_line) = partial_line.split('">', 1)
            (mtime, partial_line) = partial_line.split('</td>', 1)
            (garbage, partial_line) = partial_line.split('">', 1)
            (size, partial_line) = partial_line.split('</td>', 1)

            mtime = mtime.strip()  # Remove extra space
            data_list.append(ArchiveData(name=name, mtime=mtime, size=size))
        return data_list

    @classmethod
    def get_session(cls):
        if(cls.session is None):
            # Establish a logged in session
            cls.session = Web.Session()

            ucar_login_credentials = Config.get('ucar_login_credentials')

            # Log in
            cls.session.login(ucar_login_credentials['login_url'],
                              ucar_login_credentials['login_data'])
        return cls.session

    @classmethod
    def get_dict_of_date_modified(cls):
        if(cls.mtime_by_name is None):
            data_list = Ncep.get_list_of_external_data()
            cls.mtime_by_name = {}
            for item in data_list:
                date_modified = datetime.strptime(item.mtime,
                                                  '%d-%b-%Y %H:%M')
                cls.mtime_by_name[item.name] = date_modified
        return cls.mtime_by_name


class NarrData(object):
    variables = ['HGT', 'TMP', 'SPFH']

    class FileMissing(Exception):
        pass

    def __init__(self, year, month, day, hour=00):
        hour = hour/3*3  # Ensures it is a multiple of 3
        self.dt = datetime(year, month, day, hour=hour)

    def get_internal_drectory(self):
        return System.get_arch_dir(self.dt.year, self.dt.month, self.dt.day)

    def get_internal_name(self, variable, ext):
        return System.get_arch_filename(variable, self.dt.year, self.dt.month,
                                        self.dt.day, self.dt.hour, ext)

    def get_internal_filename(self, variable, ext):
        return os.path.join(self.get_internal_drectory(),
                            self.get_internal_name(variable, ext))

    def get_internal_last_modified(self, variable='HGT', ext='hdr'):
        try:
            filename = self.get_internal_filename(variable, ext)
            ts_epoch = os.stat(filename).st_mtime
            return datetime.fromtimestamp(ts_epoch)
        except OSError:  # Expecting 'No such file or directory'
            raise NarrData.FileMissing

    def get_external_filename(self):
        return Ncep.get_filename(self.dt.year, self.dt.month, self.dt.day,
                                 self.dt.hour)

    def get_external_last_modified(self):
        filename = self.get_external_filename()
        try:
            return Ncep.get_dict_of_date_modified()[filename]
        except KeyError:
            raise NarrData.FileMissing

    def need_to_download(self):
        try:
            ext_mtime = self.get_external_last_modified()
        except NarrData.FileMissing:  # Expecting 'No such file or directory'
            return False  # File is not available to download

        try:
            # Check if existing data is stale
            return (self.get_internal_last_modified() < ext_mtime)
        except NarrData.FileMissing:  # Expecting 'No such file or directory'
            return True  # The file does not exist internally.

    def download_grib(self):
        Ncep.download_file(self.get_external_filename())

    def extract_var_from_grib(self):
        for var in NarrData.variables:
            process_grib_for_variable((var, self.get_external_filename()))

    def clean_downloaded_grib(self):
        if os.path.exists(self.get_external_filename()):
            os.unlink(self.get_external_filename())

    @staticmethod
    def from_external_name(external_name):
        date_measured = datetime.strptime(external_name.split('.')[1],
                                          '%Y%m%d%H')
        return NarrData(year=date_measured.year, month=date_measured.month,
                        day=date_measured.day, hour=date_measured.hour)

    @staticmethod
    def get_base_aux_dir():
        return System.get_base_aux_dir()

    def get_next(self, time_increment=timedelta(hours=3)):
        dt = self.dt + time_increment
        return NarrData(year=dt.year, month=dt.month,
                        day=dt.day, hour=dt.hour)


def get_next_narr_data_gen(s_date, e_date, interval=timedelta(hours=3)):
    # Zero the min and sec. Make sure hours is multiple of 3.
    s_date.replace(hour=s_date.hour/3*3, minute=0, second=0)
    e_date.replace(hour=e_date.hour/3*3, minute=0, second=0)
    current = NarrData(year=s_date.year, month=s_date.month,
                       day=s_date.day, hour=s_date.hour)
    while current.dt <= e_date:
        yield(current)
        current = current.get_next(interval)


def update(data_to_be_updated):
    for data in data_to_be_updated:
        data.download_grib()

    for data in data_to_be_updated:
        data.extract_var_from_grib()

    for data in data_to_be_updated:
        data.clean_downloaded_grib()


def report(data_to_report):

    # print('\n'.join(Ncep.get_list_of_external_data()))
    # print(Ncep.get_dict_of_date_modified())

    report = []
    print('Will download {0} files'.format(len(data_to_report)))
    for data in data_to_report:
        line = []
        line.append(data.dt.isoformat())
        try:
            line.append(data.get_internal_last_modified().isoformat())
        except NarrData.FileMissing:
            line.append('-')
        try:
            line.append(data.get_external_last_modified().isoformat())
        except NarrData.FileMissing:
            line.append('-')
        report.append(', '.join(line))
    return '\n'.join(report)


def parse_arguments():
    # Create a command line arugment parser
    description = ('Downloads LST auxillary inputs, then archives them for'
                   ' future use.')
    parser = ArgumentParser(description=description)

    # ---- Add parameters ----
    parser.add_argument('--start-date',
                        action='store',
                        dest='start_date',
                        metavar='DATE',
                        required=False,
                        help='The start date YYYYMMDD if requiring a range.')

    parser.add_argument('--end-date',
                        action='store',
                        dest='end_date',
                        metavar='DATE',
                        required=False,
                        help='The end date YYYYMMDD if requiring a range.')

    parser.add_argument('--date',
                        action='store',
                        dest='date',
                        metavar='DATE',
                        required=False,
                        help='The date YYYYMMDD.')

    parser.add_argument('--block-size',
                        action='store',
                        dest='block_size',
                        metavar='SIZE',
                        required=False,
                        default=16777216,  # 16MB; 33554432 = 32MB
                        help=('The block size used for streaming the download.'
                              ' (Default => 16MB)'))

    parser.add_argument('--version',
                        action='version',
                        version='%(prog)s 0.0.1',
                        help='Displays the version of the software.')

    # Parse the command line parameters
    args = parser.parse_args()

    # Check if dates were given
    if args.date is not None:
        s_date = datetime.strptime(args.date, '%Y%m%d')
        e_date = datetime.strptime(args.date, '%Y%m%d')

    elif args.end_date is not None:
        e_date = datetime.strptime(args.end_date, '%Y%m%d')

        if args.start_date is not None:
            s_date = datetime.strptime(args.start_date, '%Y%m%d')

        else:
            s_date = e_date
    else:
        print('Defaulting to the 10 days ago until now')
        e_date = datetime.now().replace(hour=0, minute=0, second=0)
        s_date = e_date-timedelta(days=10)

        # raise Exception('Must supply either --date or --end-date')

    print('Dates {0} to {1}'.format(s_date.isoformat(), e_date.isoformat()))

    args.start_date = s_date
    args.end_date = e_date
    return args


def main():
    args = parse_arguments()
    # Setup the default logger format and level. log to STDOUT
    logging.basicConfig(format=('%(asctime)s.%(msecs)03d %(process)d'
                                ' %(levelname)-8s'
                                ' %(filename)s:%(lineno)d:'
                                '%(funcName)s -- %(message)s'),
                        datefmt='%Y-%m-%d %H:%M:%S',
                        level=logging.INFO,
                        stream=sys.stdout)

    logger = logging.getLogger(__name__)  # Get the logger

    # Turn down the requests and urllib3 logging
    logging.getLogger("requests").setLevel(logging.WARNING)
    logging.getLogger("urllib3").setLevel(logging.WARNING)

    # narr_data = NarrData(year=2015, month=8, day=6)

    data = get_next_narr_data_gen(args.start_date, args.end_date)
    print(Ncep.get_list_of_external_data())

    data_to_be_updated = filter(lambda x: x.need_to_download(), data)
    if True:
        print('Measured,UpdatedLocally,UpdatedOnline')
        print(report(data_to_be_updated))
    if True:
        update(data_to_be_updated)

# Cleanup - The Tar ball
#        if os.path.exists(filename):
#            os.unlink(filename)


if __name__ == '__main__':
    main()

