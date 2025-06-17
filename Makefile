# Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
# institutional affiliations. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Adrien Champion



# Temporary makefile, mostly to generate documentation.
#
# It should go away once we update the lean-toolchain version.

all: docServe

build:
	lake build

test:
	lake test

docClean:
	cd Docs ; lake clean

docUpdate:
	cd Docs ; lake update ; lake run init

doc: build
	cd Docs ; lake update Cvc ; lake build Cvc:docs

docServe: doc
	python3 -m http.server -d Docs/.lake/build/doc

manualClean:
	cd Manual ; lake clean

manualUpdate:
	cd Manual ; lake update ; lake run init

manual: build
	cd Manual ; lake update Cvc ; lake exe textbook --output _out/html --depth 2

manualServe: manual
	python3 -m http.server -d Manual/_out/html/html-multi

check: build test doc manual

.PHONY: Docs Manual manual
