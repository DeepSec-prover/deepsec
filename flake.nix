{
  description = "DeepSec: Deciding Equivalence Properties in Security Protocols.

Automated verification has become an essential part in the security evaluation of cryptographic protocols. Recently, there has been a considerable effort to lift the theory and tool support that existed for reachability properties to the more complex case of equivalence properties. **DeepSec** allows you to decide trace equivalence and session equivalence for a large variety of cryptographic primitives---those that can be represented by a subterm convergent destructor rewrite system.
  ";

  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
    # nixpkgs.url = "github:nixos/nixpkgs";
  };

  outputs = { self, flake-utils, opam-nix
  , nixpkgs 
}@inputs:
    # Don't forget to put the package name instead of `throw':
    let
      package = "deepsec";
    in
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        on = opam-nix.lib.${system};
        scope =
          on.buildOpamProject { } package ./. { ocaml-base-compiler = "*"; };
        overlay = final: prev:
          {
            # Your overrides go here
          };
      in {
        legacyPackages = scope.overrideScope overlay;

        defaultPackage = self.legacyPackages.${system}.${package};

      });
}
