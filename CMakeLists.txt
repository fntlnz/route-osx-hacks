cmake_minimum_required(VERSION 3.4)
project(route_osx)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c99")

set(SOURCE_FILES main.c)
add_executable(route_osx ${SOURCE_FILES})