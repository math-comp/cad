# cad
Formalizing Cylindrical Algebraic Decomposition and related theories in mathcomp

# META
- Compatible Coq versions: Coq 8.18 to 8.20 (or dev)
- Additional dependencies:
	- MathComp ssreflect 2.2.0 or later
	- MathComp fingroup 2.2.0 or later
	- MathComp algebra 2.2.0 or later
	- MathComp solvable 2.2.0 or later
	- MathComp field 2.2.0 or later
	- MathComp finmap 2.2.0 or later
	- MathComp bigenough 2.2.0 or later
	- MathComp multinomials 2.2.0 or later
	- MathComp finmap 2.1.0 or later
	- MathComp real-closed 2.0.1 or later
	- MathComp classical 1.1.0 or later
	- MathComp analysis 1.1.0 or later
	- Hierarchy Builder 1.4.0 or later

# Installation
## With OPAM
If you already have OPAM installed (a fresh or up to date version of opam 2 is required):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-cad
```

## Manual installation
To build and install manually, make sure the dependencies are met and do 

```
git clone https://github.com/math-comp/cad.git
cd cad
make   # or make -j <number-of-cores-on-your-machine> 
make install
```
