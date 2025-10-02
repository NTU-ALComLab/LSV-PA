cmake_minimum_required(VERSION 3.10)

add_library(ext_lsv STATIC
  lsvCmd.cpp
)

target_include_directories(ext_lsv PRIVATE
  ${PROJECT_SOURCE_DIR}/src
  ${PROJECT_SOURCE_DIR}/src/ext-lsv
)

target_link_libraries(ext_lsv abc)
