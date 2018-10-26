# cad
Formalizing Cylindrical Algebraic Decomposition related theories in mathcomp

## Installation

Clone this repository and switch to the branch "thesis".

The compilation of this project requires dependencies, that you can install with Opam.

With the following dependencies versions, you should be able to compile the whole project in the thesis branch.

Create a new switch in Opam with OCaml 4.06.1.
Install Coq 8.8.1
Install SSReflect 1.7.0 

Install coq-mathcomp-real-closed dev
Install coq-mathcomp-algebra, coq-mathcomp-field, coq-mathcomp-fingroup 1.7.0
Install coq-mathcomp-multinomials 1.1

Install coq-ppsimpl 8.8.0

Each subdirectories has got his its own Make file.
Execute the make command in each subdirectory, in the following order :
auxresults, elliptic-curves, subresultant, newtonsums, semialgebraic.




