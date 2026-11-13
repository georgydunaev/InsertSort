# Makefile for InsertSort

.PHONY: all test clean

all: Sort.vo

Sort.vo: Sort.v
	coqc Sort.v

test: all
	poly -q --use insert_sort.sml < /dev/null
	python3 -m doctest insert_sort.py
	python3 -m unittest discover -s tests -p "test_*.py"

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
	rm -f sort.ml sort.mli
	rm -rf __pycache__ tests/__pycache__ .pytest_cache
