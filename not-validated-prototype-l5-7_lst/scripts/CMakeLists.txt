
cmake_minimum_required ( VERSION 2.8.12 )

find_package ( PythonInterp 2.7.0 REQUIRED )
find_package ( PythonLibs 2.7.0 REQUIRED )

install ( PROGRAMS l5_7_lst.py
                   l5_7_build_lst_data.py
                   l5_7_estimate_landsat_emissivity.py
                   lst_extract_modtran_results.py
                   lst_prototype.py
          DESTINATION ${CMAKE_INSTALL_PREFIX}/bin )

install ( FILES lst_utilities.py
          DESTINATION ${CMAKE_INSTALL_PREFIX}/bin )
