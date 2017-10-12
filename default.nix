# This is used in the Travis build to install the Idris compiler.
let
  pkgs = import <nixpkgs> {};
  stdenv = pkgs.stdenv;
in {
  idris-containers = stdenv.mkDerivation {
    name = "recursion_schemes";
    src = ./.;
    buildInputs = with pkgs; [ haskellPackages.idris gmp ];
  };
}
