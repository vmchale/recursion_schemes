# FIXME this is kinda stupid.
let
  pkgs = import <nixpkgs> {};
  stdenv = pkgs.stdenv;
in {
  idris-binary = stdenv.mkDerivation {
    name = "idris-binary";
    src = ./.;
    buildInputs = with pkgs; [ haskellPackages.idris gmp ];
  };
}
