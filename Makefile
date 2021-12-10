
IDRIS ?= idris2
TARGET = puff

.PHONY: all build clean install test

all: build

build:
	$(IDRIS) --build ${TARGET}.ipkg

clean:
	rm -rf ./build

install:
	echo "TODO"


