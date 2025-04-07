.PHONY: all clean

all: _pesto_params_cffi.o

_pesto_params_cffi.o: pesto_params.h ../_lazer_cffi.o
	python3 ../params_cffi_build.py pesto_params.h ../..

pesto_params.h: pesto_params.py
	cd ../../scripts && sage lin-codegen.sage ../python/pesto/pesto_params.py > ../python/pesto/pesto_params.h

../_lazer_cffi.o:
	cd .. && make

clean:
	rm -rf __pycache__
	rm -f *.c *.o *.so
