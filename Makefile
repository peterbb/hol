
TARGET=test
OCBFLAGS= -use-menhir
OCB= ocamlbuild ${OCBFLAGS}

.PHONY: core

default: core

core:
	${OCB} core/core.cma

byte:
	${OCB} src/${TARGET}.byte

run: byte
	ocamlrun ${TARGET}.byte

clean:
	ocamlbuild -clean
