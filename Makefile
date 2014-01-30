AGDA ?= agda
AGDALIB ?= /usr/share/agda-stdlib

all:Everything.agdai
clean:
	rm -f *.agdai
Everything.agdai:$(wildcard *.agda)
	$(AGDA) -i. -i$(AGDALIB) Everything.agda
