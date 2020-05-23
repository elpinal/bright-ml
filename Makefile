BIN := bright-ml

LIB := std.sml nat.sml ordered.sml queue.sml non_empty.sml map.sml bst.sml
LIBI := std.ui nat.ui ordered.ui queue.ui non_empty.ui map.ui bst.ui

CMLIBI := from-string-sig.ui from-string.ui bytestring-sig.ui bytestring.ui susp-sig.ui susp.ui stream-sig.ui stream.ui streamable-sig.ui streamable.ui bytesubstring-sig.ui bytesubstring.ui streamable-mono-sig.ui streamable-mono.ui lex-engine-sig.ui lex-engine.ui parse-engine-sig.ui parse-engine.ui

all: lib cmlib make_lexer.sml make_parser.sml
	@mosmlc -liberal -toplevel -I lib -I cmlib-mosml $(LIBI) $(CMLIBI) pretty.sml result.sml filepath.sml ident.sml token.sml syntax.sml make_lexer.sml lexer.sml make_parser.sml parser.sml variable.sml record.sml dynamic.sml internal.sml quantified.sml semantic_signature.sml env.sml space.sml semantics.sml bright_ml.sml cli.sml main.sml -o $(BIN)

lib:
	@cd lib && mosmlc -toplevel $(LIB)

cmlib:
	@cd cmlib-mosml && make >/dev/null

make_lexer.sml: make_lexer.cmlex
	cmlex -o make_lexer.sml make_lexer.cmlex

make_parser.sml: make_parser.cmyacc
	cmyacc -o make_parser.sml make_parser.cmyacc

run: all
	./bright-ml $(ARG)

test:
	go run test.go

test-with-update:
	go run test.go -update


install:
ifndef PREFIX
	$(error PREFIX is not set)
endif
	cp ./bright-ml $(PREFIX)/bright-ml

.PHONY: all lib cmlib run test test-with-update install
