let
  pkgs = import <nixpkgs> { };

in
  (pkgs.idrisPackages.callPackage ./specdris.nix { })
