# Makefile for InsertSort

CXX ?= g++
CXXFLAGS ?= -std=c++17 -Wall -Wextra -Wpedantic -O2 -Iinclude

.PHONY: all test test-cpp clean

all: Sort.vo tests/test_cpp_insert_sort

Sort.vo: Sort.v
	coqc Sort.v

tests/test_cpp_insert_sort: tests/test_cpp_insert_sort.cpp include/insert_sort.hpp include/binary_insert_sort.hpp
	$(CXX) $(CXXFLAGS) tests/test_cpp_insert_sort.cpp -o tests/test_cpp_insert_sort

test-cpp: tests/test_cpp_insert_sort
	./tests/test_cpp_insert_sort

test: all test-cpp
	poly -q --use insert_sort.sml < /dev/null
	poly -q --use binary_insert_sort.sml < /dev/null
	python3 -m doctest insert_sort.py
	python3 -m doctest binary_insert_sort.py
	python3 -m unittest discover -s tests -p "test_*.py"

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
	rm -f sort.ml sort.mli
	rm -f tests/test_cpp_insert_sort
	rm -rf __pycache__ tests/__pycache__ .pytest_cache

