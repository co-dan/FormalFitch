{
  description = "Rocq and Iris development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };

      # Create a custom Rocq environment bundled with Iris and its dependencies
      rocqWithLibs = pkgs.rocqPackages.rocq-core.withPackages (p: [
        p.stdpp
        p.iris
      ]);
      
    in {
      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [
          rocqWithLibs
        ];
      };
    };
}
