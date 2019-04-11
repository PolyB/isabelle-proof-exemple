CMAKE_MINIMUM_REQUIRED(VERSION 2.8)

PROJECT(pexemple)

set(SRC
  list.c
  main.c
  )

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_FLAGS "${CMAKE_CXX_FLAGS} -Wall -pedantic -Wextra -Werror")

add_executable(pexemple ${SRC})

add_custom_target(gen-all-c_pp
                  ALL
                  COMMAND cat ${SRC} > all.c
                  COMMAND ${CMAKE_C_COMPILER} --preprocess all.c -o all.c_pp
                  BYPRODUCTS all.c_pp
                  DEPENDS ${SRC}
                  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                  VERBATIM
                  COMMENT "rebuilding all.c_pp"
                  )
