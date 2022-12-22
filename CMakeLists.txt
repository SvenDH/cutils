# CMakeList.txt : CMake project for utils, include source and define
# project specific logic here.
#
cmake_minimum_required (VERSION 3.8)

project (utils C)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")

# Add source to this project's executable.
add_executable (utils  utils.h main.c)

# TODO: Add tests and install targets if needed.
