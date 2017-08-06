{ build-idris-package
, fetchFromGitHub
, prelude
, base
, lib
, idris
}:

build-idris-package {

  name = "specdris";

  src = fetchFromGitHub {
    owner = "pheymann";
    repo = "specdris";
    rev = "fe00346468c663c6db4ddc9ab1e1f55f3df8be59";
    sha256 = "0m381fxa8f2qmsifg2vkn12pb3qknnn4zj07bwv21fbn62whxfpi";
  };

  propagatedBuildInputs = [ prelude base ];

}
