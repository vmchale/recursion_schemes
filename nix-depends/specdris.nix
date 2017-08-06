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
    sha256 = "1xgpijqna3d4cf0i4kchp279gbkns0z699lcvdpvszidsi387lll";
  };

  propagatedBuildInputs = [ prelude base ];

}
