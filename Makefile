# Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
# institutional affiliations. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Adrien Champion



# Temporary makefile, mostly to generate documentation.
#
# It should go away once we update the lean-toolchain version.

all: docServe

docClean:
	cd docbuild ; lake clean

docUpdate:
	cd docbuild ; lake update 

doc:
	lake build
	cd docbuild ; lake update Cvc ; lake build Cvc:docs

docServe: doc
	python3 -m http.server -d docbuild/.lake/build/doc

docOpen: doc
	open http://[::]:8000 \
	&& python3 -m http.server -d docbuild/.lake/build/doc
