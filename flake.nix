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
      ver = "2.0.19";
      archives = {
        aarch64-darwin = { target = "darwin-arm64"; sha256 = "9b3b7da0919e345ffe0f7c81059593bd45e533571dbaaedac45b5362ddb27779"; };
        x86_64-darwin  = { target = "darwin-x64";   sha256 = "41fdd494425f79746d78bbc2ee11279f199cd216c723de210fe1a2ad64375266"; };
        aarch64-linux  = { target = "linux-arm64";  sha256 = "388b3c1f98468ad7cc508b67044c842fc24c1527962cecd6a68c956ab6f92e5e"; };
        x86_64-linux   = { target = "linux-x64";    sha256 = "4f50d0a34283bb4e9ad6277a36fd91ef20c5d8992ca857c8185e605b866425b9"; };
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
