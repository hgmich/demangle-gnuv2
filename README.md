# demangle-gnuv2

This project implements demangling of symbols for versions of `g++` predating
the v3/Itanium C++ ABI, with specific intentions of providing structured
demangling information for Binary Ninja. The core is written in Rust, with a
Python binding using PyO3 made available.

Note this code is a direct rewrite of the demangling code from older verisons
of `libiberty` as included in [rz-libdemangle][rz-libdemangle-gh]. As such:

- The code quality is quite poor currently, as it uses a mixture of Rust idioms
  (options, slicing) and C mutable state idioms.

- The work is a clear derivative work and as such, must be licensed under the
  LGPL (2.0 or newer, per the license terms of this version of libiberty).

**NOTE:** Currently under development and not fully usable.

[rz-demangle-gh]: https://github.com/rizinorg/rz-libdemangle
