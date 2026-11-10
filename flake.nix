{
  description = "lean-assay: check whether Lean theorems pin down an implementation, by running broken implementations against them";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix.url = "github:numtide/treefmt-nix";
    plausible = {
      url = "github:leanprover-community/plausible/v4.35.0";
      flake = false;
    };
  };

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ inputs.treefmt-nix.flakeModule ];

      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];

      perSystem =
        { pkgs, config, ... }:
        {
          packages.default = pkgs.stdenv.mkDerivation {
            pname = "lean-assay";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./lakefile.toml
                ./lean-toolchain
                ./Assay.lean
                ./Assay
                ./Examples
                ./AssayTest
              ];
            };
            nativeBuildInputs = [ pkgs.lean4 ];
            buildPhase = ''
              export HOME=$TMPDIR
              cp -r ${inputs.plausible} $TMPDIR/plausible
              chmod -R u+w $TMPDIR/plausible
              sed -i 's|^git = .*|path = "'$TMPDIR'/plausible"|; /^rev = /d' lakefile.toml
              lake build Assay Examples
              lake test
            '';
            installPhase = ''
              mkdir -p $out
              cp -r Assay.lean Assay lakefile.toml lean-toolchain $out/
              cp -r .lake/build $out/build
            '';
          };

          treefmt = {
            projectRootFile = "flake.nix";
            programs.nixfmt.enable = true;
          };

          devShells.default = pkgs.mkShell {
            packages = [
              pkgs.lean4
              config.treefmt.build.wrapper
            ];
          };
        };
    };
}
