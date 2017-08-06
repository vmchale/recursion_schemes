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
    sha256 = "1n4daf1acjkd73an4m31yp9g616crjb7h5z02f1gj29wm3dbx5s7";
  };

  propagatedBuildInputs = [ prelude base ];

}
