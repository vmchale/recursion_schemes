let
  pkgs = import <nixpkgs> { };

in
  (pkgs.idrisPackages.callPackage ./default.nix { })
