{
  pkgs,
  lib,
  config,
  inputs,
  ...
}: let
  checkPanicReasonsScript = pkgs.writeShellScriptBin "panic-reasons" ''
    jq="${pkgs.jq}/bin/jq"
    sort="${pkgs.coreutils}/bin/sort"
    uniq="${pkgs.coreutils}/bin/uniq"

    "$jq" '.results[] | select(.success == false) | select(.fail_reason == "PANIC") | select(.exc_info | test("^not yet implemented")) | .exc_info' < results.json | $sort | $uniq -c
  '';
  checkFailuresScript = pkgs.writeShellScriptBin "failed-syms" ''
    jq="${pkgs.jq}/bin/jq"
    sort="${pkgs.coreutils}/bin/sort"
    uniq="${pkgs.coreutils}/bin/uniq"

    "$jq" '.results[] | select(.success == false)' < results.json
  '';
in {
  env.JJ_PRE_PUSH_CHECKER = "prek";

  packages = [pkgs.git pkgs.gh pkgs.alejandra pkgs.rustup checkPanicReasonsScript checkFailuresScript];

  languages.rust.enable = true;
  languages.rust.channel = "stable";
  languages.python.enable = true;
  languages.python.package = pkgs.python312;
  languages.python.venv.enable = true;
  languages.python.venv.requirements = ''
    maturin==1.13.1
  '';

  scripts.demangle.exec = ''
    exec cargo run -p demangle-gnuv2 --bin demangle "$@"
  '';

  tasks = {
    "workspace:build".exec = "cargo build --workspace";
    "workspace:lint".exec = "cargo clippy --workspace --keep-going -- -D warnings";
    "workspace:fix-lints".exec = "cargo clippy --workspace --keep-going --fix";
    "workspace:fmt".exec = "cargo fmt";
    "pyext:develop" = {
      before = ["test:symbols"];
      exec = "cd \"$DEVENV_ROOT/demangle-gnuv2-py\" && maturin develop";
    };
    "test:symbols" = {
      exec = ''
        set -euo pipefail
        source "$DEVENV_STATE/venv/bin/activate"
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
  git-hooks.hooks.clippy.enable = true;
}
