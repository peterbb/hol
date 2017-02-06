
TARGET=test
OCAMLBUILDFLAGS= -use-menhir

default:
	ocamlbuild ${OCAMLBUILDFLAGS} src/${TARGET}.byte
	ocamlrun ${TARGET}.byte

clean:
	ocamlbuild -clean
