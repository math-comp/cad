{ coq, mkCoqDerivation, mathcomp, mathcomp-bigenough
, mathcomp-finmap, mathcomp-real-closed, multinomials
, mathcomp-classical, mathcomp-analysis
, lib, version ? null }:

mkCoqDerivation {

  namePrefix = [ "coq" "mathcomp" ];
  pname = "cad";
  owner = "math-comp";
  inherit version;
  release = {};
  defaultVersion = null;

  propagatedBuildInputs = [
    mathcomp.ssreflect
    mathcomp.algebra
    mathcomp.field
    mathcomp.fingroup
    mathcomp.solvable
    mathcomp-bigenough
    mathcomp-finmap
    mathcomp-real-closed
    multinomials
    mathcomp-classical
    mathcomp-analysis
  ];

  meta = {
    description = "Mathematical Components Library on CAD";
    license = lib.licenses.cecill-c;
  };
}
