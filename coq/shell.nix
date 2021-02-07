let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ pkgs ? pinned }:

let
  inherit (pkgs) mkShell;

  /*coq-matching-logic = import sources."coq8.13-matching-logic" { inherit pkgs; };*/
  coq-matching-logic = import sources."AML-Formalization" { };


  self = mkShell {
    buildInputs = [
      coq-matching-logic
      pkgs.bashInteractive
    ];
  };
in
  self

