HC=ghc
SOURCES=src/Main.hs src/Grammar.hs
GEN_SOURCES=src/Lexer.x src/Parser.y
GENERATED=src/Lexer.hs src/Parser.hs
PACKAGE=HW3.zip

.PHONY: pack all run clean

all: parser

clean:
		rm -rf src/*.o src/*.hi
		rm -f parser
		rm -f input_parser

run: parser
		./parser

input_parser:
	g++ -o input_parser ./src/input.cpp

parser: $(GENERATED) $(SOURCES)
	$(HC) -i./src -tmpdir . ./src/Main.hs -o parser

$(GENERATED): $(GEN_SOURCES) $(SOURCES)
	alex src/Lexer.x -o src/Lexer.hs
	happy src/Parser.y -o src/Parser.hs

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src
