<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Cylindical Algbebraic Decomposition

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/cad/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/cad/actions/workflows/docker-action.yml




This library contains a formal proof of Collins' Cylindical
Aglebraic Decomposition, using the Mathematical Components Library.

## Meta

- Author(s):
  - Cyril Cohen (initial)
  - Boris Djalal (initial)
  - Quentin Vermande (initial)
- License: [GNU Lesser General Public License v3.0](LICENSE)
- Compatible Coq versions: Coq 8.18 or later
- Additional dependencies:
  - [Hierarchy Builder >= 1.4.0 ](https://github.com/math-comp/hierarchy-builder)
  - [MathComp ssreflect 2.2](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp fingroup](https://math-comp.github.io)
  - [MathComp solvable](https://math-comp.github.io)
  - [MathComp field](https://math-comp.github.io)
  - [MathComp bigenough 1.0.1 or later](https://github.com/math-comp/bigenough)
  - [MathComp bigenough 1.0.1 or later](https://github.com/math-comp/bigenough)
  - [MathComp multinomials 2.2.0 or later](https://github.com/math-comp/multninomials)
  - [MathComp real-closed 2.0.1 or later](https://github.com/math-comp/real-closed)
  - [MathComp classical 1.1.0 or later](https://github.com/math-comp/analysis)
  - [MathComp analysis 1.1.0 or later](https://github.com/math-comp/analysis)
- Coq namespace: `SemiAlgebraic`
- Related publication(s):
  - [A Constructive Formalisation of Semi-algebraic Sets and Functions](https://hal.inria.fr/hal-01643919) doi:[10.1145/3167099](https://doi.org/10.1145/3167099)

## Building and installation instructions

The easiest way to install the latest released version of Cylindical Algbebraic Decomposition
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-cad
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/cad.git
cd cad
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



