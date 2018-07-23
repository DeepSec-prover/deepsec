Code release associated to the ESORICS'18 paper
```
      ==============================================================

        Partial-Order Reduction for Security Protocol Equivalences

                       Beyond Action-Determinism

            David Baelde, Lucca Hirschi and Stephanie Delaune

      ==============================================================
```
A long version of which may be found at <https://arxiv.org/abs/1804.03650>.

# Porridge

Porridge is an OCaml library implementing POR techniques for checking
trace equivalence of security protocols.

Copyright 2017-2018 David Baelde, Stéphanie Delaune & Lucca Hirschi

This library is free software. You can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

A copy of the GNU GPL v3 license may be found in `./COPYING`.

## Build

The code builds with OCaml 4.05.0 or later.
It requires the Alcotest library >=0.8.1, and ocamlfind.

You may use opam to get these requirements, using the following
commands once you have opam installed and up-to-date:
```
$ opam switch 4.05.0
$ eval `opam config env`
$ opam install ocamlfind alcotest
```

Then simply run:
```
$ make
```

In more details, make targets include:
```
$ make lib      # build only the library
$ make test     # test it
$ make porridge # build a utility to play with the lib on predefined examples
$ make doc      # build documentation for "toplevel" modules in doc/
```

## Install

To install/uninstall the library, run `make install` or
`make uninstall`. The library will be usable with `ocamlfind`.

You can also use with opam:
```
opam pin add porridge .
```
Then `opam install/uninstall/upgrade porridge` can simply
be used to install, uninstall, or upgrade the porridge library
based on the latest sources.

## Code

The `src` subdirectory contains the code. The main modules are:

- `LTS`: our generic notion of symbolic transition system
- `POR`: given an LTS, compute persistent sets, define the induced
  persistent and sleep set LTS
- `Trace_equiv`: the symbolic LTS for trace equivalence of security protocols

See `doc` subdirectory, after running `make doc`, for more details.

We also use various utility modules, including:

- `Hashcons` for various (interchangeable) hashconsing strategies
- `Memo` plays a similar role for memoization
