
cmake_minimum_required ( VERSION 2.8.12 )

find_package ( PythonInterp 2.7.0 REQUIRED )
find_package ( PythonLibs 2.7.0 REQUIRED )

install ( PROGRAMS update_narr_aux_data_from_CISL_RDA.py
          DESTINATION ${CMAKE_INSTALL_PREFIX}/bin )

install ( FILES lst_auxillary.config.example
          DESTINATION ${CMAKE_INSTALL_PREFIX}/bin )
