{
  pkgs,
  lib,
  config,
  inputs,
  ...
}: let
  checkFailReasonsScript = pkgs.writeShellScriptBin "fail-reasons" ''
    jq="${pkgs.jq}/bin/jq"
    sort="${pkgs.coreutils}/bin/sort"
    uniq="${pkgs.coreutils}/bin/uniq"

    "$jq" '.results[] | select(.success == false) | select(.fail_reason == "PANIC") | select(.exc_info | test("^not yet implemented")) | .exc_info' < results.json | $sort | $uniq -c
  '';
in {
  packages = [pkgs.git pkgs.gh pkgs.alejandra pkgs.rustup checkFailReasonsScript];

  languages.rust.enable = true;
  languages.rust.channel = "stable";
  languages.python.enable = true;
  languages.python.venv.enable = true;
  languages.python.venv.requirements = ''
    maturin==1.8.3
  '';

  scripts.demangle.exec = ''
    exec cargo run -p demangle-gnuv2 --bin demangle "$@"
  '';

  tasks = {
    "workspace:build".exec = "cargo build --workspace";
    "workspace:lint".exec = "cargo clippy --workspace --keep-going -- -D warnings";
    "workspace:fix-lints".exec = "cargo clippy --workspace --keep-going --fix";
    "workspace:fmt".exec = "cargo fmt";
    "pyext:develop".exec = "cd \"$DEVENV_ROOT/demangle-gnuv2-py\" && maturin develop";
    "test:symbols" = {
      after = ["pyext:develop"];
      exec = ''
        set -euo pipefail
        python test/test_demangle.py -Cj -o results.json | tee "$DEVENV_TASK_OUTPUT_FILE"
      '';
    };
  };

  enterTest = ''
    echo "Running tests"
    cargo test --workspace
  '';

  git-hooks.hooks.alejandra.enable = true;
  git-hooks.hooks.rustfmt.enable = true;
  # Not ready for the prime time yet
  # git-hooks.hooks.clippy.enable = true;
}
