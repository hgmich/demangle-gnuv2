{
  pkgs,
  lib,
  config,
  inputs,
  ...
}: {
  packages = [pkgs.git pkgs.gh pkgs.alejandra];

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
    "workspace:fmt".exec = "cargo fmt --workspace";
    "pyext:develop".exec = "cd demangle-gnuv2-py && maturin develop";
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
