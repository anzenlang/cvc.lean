# Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
# institutional affiliations. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Adrien Champion



# Temporary makefile, mostly to generate documentation.
#
# It should go away once we update the lean-toolchain version.

all: docServe

docClean:
	cd Docs ; lake clean

docUpdate:
	cd Docs ; lake update ; lake run init

doc:
	lake build
	cd Docs ; lake update Cvc ; lake build Cvc:docs

docServe: doc
	python3 -m http.server -d Docs/.lake/build/doc

docOpen: doc
	open http://[::]:8000 \
	&& python3 -m http.server -d Docs/.lake/build/doc
