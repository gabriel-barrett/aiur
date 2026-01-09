{
  description = "Rust Nix flake";

  # First enable Garnix GitHub app for the repo
  #nixConfig = {
  #  extra-substituters = [
  #    "https://cache.garnix.io"
  #  ];
  #  extra-trusted-public-keys = [
  #    "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g="
  #  ];
  #};

  inputs = {
    # System packages
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";

    # Helper: flake-parts for easier outputs
    flake-parts.url = "github:hercules-ci/flake-parts";

    # Rust toolchain
    fenix = {
      url = "github:nix-community/fenix";
      # Follow top-level nixpkgs so we stay in sync
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # Rust crate builder
    crane.url = "github:ipetkov/crane";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    fenix,
    crane,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      # Systems we want to build for
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        system,
        pkgs,
        ...
      }: let
        # Pins the Rust toolchain
        rustToolchain = fenix.packages.${system}.fromToolchainFile {
          file = ./rust-toolchain.toml;
          # Update this hash when `rust-toolchain.toml` changes
          # Just copy the expected hash from the `nix build` error message
          sha256 = "sha256-sqSWJDUxc+zaz1nBWMAJKTAGBuGWP25GCftIOlCEAtA=";
        };
        # Rust package
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        commonArgs = {
          src = craneLib.cleanCargoSource ./.;
          strictDeps = true;

          buildInputs =
            [
              # Add additional build inputs here
            ]
            ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [
              # Additional darwin specific inputs can be set here
              pkgs.libiconv
            ];
        };
        cargoArtifacts = craneLib.buildDepsOnly commonArgs;

        template = craneLib.buildPackage (commonArgs
          // {
            inherit cargoArtifacts;
            # Prevents tests from running on build
            doCheck = false;
          });

        # Run tests with cargo-nextest
        template-nextest = craneLib.cargoNextest (
          commonArgs
          // {
            inherit cargoArtifacts;
            partitions = 1;
            partitionType = "count";
            cargoNextestPartitionsExtraArgs = "--no-tests=pass";
          }
        );
        # Workspace example for `client` and `server` subcrates
        # serverPkg = craneLib.buildPackage (commonArgs // {
        #   inherit cargoArtifacts;
        #   pname = "server";
        #   cargoExtraArgs = "-p server";
        # });
        # clientPkg = craneLib.buildPackage (commonArgs // {
        #   inherit cargoArtifacts;
        #   pname = "client";
        #   cargoExtraArgs = "-p client";
        # });
      in {
        # Run with `nix flake check -L`
        # To re-run from scratch, delete the derivations:
        # ```
        # rm result
        # nix path-info .#default
        # nix store delete /nix/store/<hash>-<name> # Use path from prior step
        # nix path-info .#test
        # nix store delete /nix/store/<hash>-<name> # Use path from prior step
        # ```
        # Then run `nix flake check -L` again
        # Alternatively, run `nix build --rebuild` and ignore the non-determinism error
        checks = {
          inherit template template-nextest;
        };

        packages = {
          default = template;

          # Workspace example
          # server = serverPkg;
          # client = clientPkg;
        };

        # Provide a dev shell with `cargo` and the pinned toolchain
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            pkg-config
            openssl
            ocl-icd
            gcc
            clang
            rustToolchain
            rust-analyzer
            cargo-nextest
          ];
        };
      };
    };
}
