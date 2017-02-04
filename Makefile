
TARGET=test

default:
	ocamlbuild src/${TARGET}.byte
	ocamlrun ${TARGET}.byte

clean:
	ocamlbuild -clean
