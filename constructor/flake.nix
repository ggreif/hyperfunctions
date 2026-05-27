{
  description = "Constructor language: nested data with universe-level inference";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "aarch64-darwin" "x86_64-darwin" "aarch64-linux" "x86_64-linux" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      packages = forAllSystems (pkgs: {
        default = pkgs.haskellPackages.developPackage {
          root = ./.;
          name = "constructor";
        };
      });

      devShells = forAllSystems (pkgs: {
        default = pkgs.haskellPackages.developPackage {
          root = ./.;
          name = "constructor";
          returnShellEnv = true;
          withHoogle = false;
          modifier = drv:
            pkgs.haskell.lib.addBuildTools drv
              (with pkgs.haskellPackages; [ cabal-install haskell-language-server ghcid ]);
        };
      });
    };
}
