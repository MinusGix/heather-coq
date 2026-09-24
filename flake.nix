{
  description = "DeLaM formalization (Coq 8.20)";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      coqPackages = pkgs.coqPackages_8_20.overrideScope (_: prev: {
        coq = prev.coq.override { version = "8.20.0"; };
      });
      # smpl is not packaged in nixpkgs for Coq 8.20.
      smpl = coqPackages.mkCoqDerivation {
        pname = "smpl";
        owner = "uds-psl";
        version = "8.20";
        src = pkgs.fetchFromGitHub {
          owner = "uds-psl";
          repo = "smpl";
          rev = "ac72bf26110a3676d8122033d3ab0bda1437f461";
          hash = "sha256-VdoXCDy5hprFaeQldMHwutOCWJdVfjM8qADK71xq/AU=";
        };
        mlPlugin = true;
      };
    in {
      packages.${system}.smpl = smpl;
      devShells.${system}.default = pkgs.mkShell {
        packages = [
          coqPackages.coq
          coqPackages.equations
          smpl
          pkgs.gnumake
          pkgs.time
        ];
        shellHook = ''
          export OCAMLRUNPARAM="''${OCAMLRUNPARAM:-o=500,s=8M}"
        '';
      };
    };
}
