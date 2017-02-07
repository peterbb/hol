
TARGET=test
OCBFLAGS= -use-menhir
OCB= ocamlbuild ${OCBFLAGS}

.PHONY: core byte run clean

default: run

core:
	${OCB} core/core.cma

${TARGET}.byte: core
	${OCB} src/${TARGET}.byte

run: ${TARGET}.byte
	ocamlrun ${TARGET}.byte

clean:
	ocamlbuild -clean
