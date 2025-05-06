{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }: flake-utils.lib.eachDefaultSystem
    (system:
      let pkgs = import nixpkgs { system = system; config.allowUnfree = true; };
      in
      {
        devShells.default = pkgs.mkShell {
          allowUnfree = true;
          nativeBuildInputs = (with pkgs; [
            haskell.compiler.ghc966
            ghcid
            stylish-haskell
            cabal-install
            haskell-language-server
          ]) ++ (with pkgs.haskellPackages; [
            hindent
            haskell-language-server
          ]);
        };
      }
    );
}
