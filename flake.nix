{
  description = "A very basic flake";

  inputs = {
  };

  outputs = { self, nixpkgs }: let
    pkgs = nixpkgs.legacyPackages.x86_64-linux;
  in {
    devShells.x86_64-linux.default = pkgs.mkShell {
      packages = with pkgs; [
        pandoc
        (agda.withPackages (p: [ 
          p.standard-library 
        ]))
      ];
    };

  };
}
