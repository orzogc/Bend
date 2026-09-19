# Nix flake for Bend, written by release.ts (in the bend-lang.com repo,
# from deploy/flake.nix.in) with the version and the sha256 of each
# release archive filled in: do not bump it by hand. The package fetches
# the host's archive from GitHub Releases, the same one install.sh and
# the Homebrew formula install, lands it whole in libexec/bend (bin/bend
# beside bend2/ and guide/, the layout the executable expects) and puts
# a wrapper at bin/bend that adds clang to PATH on Linux (bend -o needs
# clang 14+) and names Apple's clang on macOS. On Linux the Bun
# executable is patched to find the store's glibc. Use:
# `nix profile install github:bendlang/bend`, `nix run github:bendlang/bend`,
# or `inputs.bend.url = "github:bendlang/bend"` and
# `inputs.bend.packages.${system}.default` in a flake.
{
  description = "Bend: C speed, CUDA parallelism, Lean proofs, Python syntax";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      ver = "2.0.18";
      archives = {
        aarch64-darwin = { target = "darwin-arm64"; sha256 = "e994cdbc008300c0a95cf146591e4ff947e74b31ec73b3f8a8e2cc88dddf422e"; };
        x86_64-darwin  = { target = "darwin-x64";   sha256 = "b333b8468bb00f80f70a197e0907bd31d2f218f2d2e41ec1c92c3aaef14f9478"; };
        aarch64-linux  = { target = "linux-arm64";  sha256 = "61a4b963e496f109b0d63fb51cbe5dc3c99ff02c7500f30881caf1525e24e685"; };
        x86_64-linux   = { target = "linux-x64";    sha256 = "e55c564fa784a5428392fce57e1a81a7ae472bb9fa3bb2a5e745d6e6295dc22a"; };
      };
      each = f: nixpkgs.lib.mapAttrs (system: archive:
        f (import nixpkgs { inherit system; }) archive) archives;
    in {
      packages = each (pkgs: archive: {
        default = pkgs.stdenv.mkDerivation {
          pname = "bend";
          version = ver;
          src = pkgs.fetchurl {
            url = "https://github.com/bendlang/bend/releases/download/v${ver}/"
              + "bend-${ver}-${archive.target}.tar.gz";
            inherit (archive) sha256;
          };
          nativeBuildInputs = [ pkgs.makeWrapper ]
            ++ pkgs.lib.optional pkgs.stdenv.hostPlatform.isLinux pkgs.autoPatchelfHook;
          dontBuild = true;
          dontStrip = true;
          installPhase = ''
            mkdir -p $out/libexec/bend $out/bin
            cp -r . $out/libexec/bend
            makeWrapper $out/libexec/bend/bin/bend $out/bin/bend \
              ${if pkgs.stdenv.hostPlatform.isLinux
                then ''--prefix PATH : "${pkgs.lib.makeBinPath [ pkgs.clang ]}"''
                else "--set-default CC /usr/bin/clang"}
          '';
          meta = {
            description = "Bend: C speed, CUDA parallelism, Lean proofs, Python syntax";
            homepage = "https://bend-lang.com";
            license = pkgs.lib.licenses.asl20;
            mainProgram = "bend";
          };
        };
      });
      apps = each (pkgs: archive: {
        default = {
          type = "app";
          program = "${self.packages.${pkgs.system}.default}/bin/bend";
        };
      });
    };
}
