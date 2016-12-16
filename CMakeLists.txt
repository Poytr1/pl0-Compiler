cmake_minimum_required(VERSION 3.6)
project(pl0)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

set(SOURCE_FILES
    pl0.c
        )

add_executable(pl0 ${SOURCE_FILES})