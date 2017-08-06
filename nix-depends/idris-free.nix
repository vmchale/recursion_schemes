{ build-idris-package
, fetchFromGitHub
, prelude
, base
, lib
, idris
}:

build-idris-package {

  name = "idris-free";

  src = fetchFromGitHub {
    owner = "idris-hackers";
    repo = "idris-free";
    rev = "919950fb6a9d97c139c2d102402fec094a99c397";
    sha256 = "1xgpijqna3d4cf0i4kchp279gbkns0z699lcvdpvszidsi387lll";
  };

  propagatedBuildInputs = [ prelude base ];

}
