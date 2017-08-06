{ build-idris-package
, fetchFromGitHub
, prelude
, base
, lib
, idris
}:

build-idris-package {


  name = "recursion_schemes";

  src = fetchFromGitHub {
    owner = "vmchale";
    repo = "recursion_schemes";
    rev = "cfd76690fe5929b5bbc24c9520c2217f921eae09";
    sha256 = "1xgpijqna3d4cf0i4kchp279gbkns0z699lcvdpvszidsi387lll";
  };

  propagatedBuildInputs = 
  [ 
  prelude 
  base 
  (let pkgs = import <nixpkgs> { }; in pkgs.idrisPackages.callPackage ./nix-depends/specdris.nix { }) 
  (let pkgs = import <nixpkgs> { }; in pkgs.idrisPackages.callPackage ./nix-depends/idris-free.nix { }) 
  ];

}
