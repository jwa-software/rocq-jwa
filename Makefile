# Copyright (c) 2026 Junzhe Wang, licensed under the MIT License.

# Build entry points for rocq-jwa.
#
#   make          build every theory and the test suite (default target)
#   make fmt      format the dune files
#   make clean    remove the build directory
#   make opam     regenerate opam/rocq-jwa.opam from dune-project
#   make deps     install the build dependencies into the current opam switch
#
# Each command runs under `opam exec`, so that the dune and Rocq of the
# active switch are used whether or not the shell has been initialised with
# `opam env`.
OPAM_EXEC := opam exec --

.PHONY: build fmt clean opam deps

build:
	$(OPAM_EXEC) dune build

fmt:
	$(OPAM_EXEC) dune fmt || $(OPAM_EXEC) dune build @fmt

clean:
	$(OPAM_EXEC) dune clean

# dune 3.21 provides no @opam alias; the file is built by its path.
opam:
	$(OPAM_EXEC) dune build opam/rocq-jwa.opam

# The dependencies are those declared in the generated opam file: dune, and
# rocq-core, which also provides Ltac2.
deps:
	opam install --deps-only --yes ./opam/rocq-jwa.opam
