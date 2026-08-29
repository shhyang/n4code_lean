# N4Code

A machine-checked proof, in Lean 4 and mathlib, of the classification of
optimal finite-length block codes of size four for binary symmetric channels.

This repository formalizes the main results of

> Y. Dong and S. Yang, "On Optimal Finite-Length Block Codes of Size Four for
> Binary Symmetric Channels," *IEEE Transactions on Information Theory*,
> vol. 71, no. 1, pp. 138-166, 2025,
> [doi:10.1109/TIT.2024.3504823](https://doi.org/10.1109/TIT.2024.3504823).

The formalization proves the paper's classification theorems: for every
blocklength `n` and crossover probability `ε`, there exists an optimal
`(n, 4)` binary code that is equivalent to a linear or Class-I code, and for
`n > 3` every optimal code is equivalent to a linear, Class-I, or Class-II
code.

## Build

The Lean toolchain is pinned in
[`lean-toolchain`](lean-toolchain) and mathlib is pinned in
[`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get   # fetch prebuilt mathlib oleans
lake build           # build the N4Code package
```

To build only the root library:

```bash
lake build N4Code
```

Do not run a bare `lake clean`, as that can delete the prebuilt mathlib oleans
and trigger a lengthy mathlib rebuild. Restore the oleans with
`lake exe cache get` first if needed.

## Repository layout

```text
N4Code.lean          # library root module
N4Code/              # the Lean formalization
lakefile.toml        # Lake package definition
lean-toolchain       # pinned Lean version
lake-manifest.json   # pinned mathlib dependency
LICENSE              # Apache-2.0
README.md
```

## Authors

- Shenghao Yang
- Yanyan Dong

## AI assistance

The proof scripts in this repository were developed with substantial
assistance from AI coding agents. All theorem statements, definitions, and the
overall design were authored by the project authors. The AI-assisted proof
text was reviewed by the authors and is machine-checked by the Lean 4 kernel.

## Paper

```bibtex
@article{DongYang2025,
  author  = {Dong, Yanyan and Yang, Shenghao},
  title   = {On Optimal Finite-Length Block Codes of Size Four for Binary Symmetric Channels},
  journal = {IEEE Transactions on Information Theory},
  volume  = {71},
  number  = {1},
  pages   = {138--166},
  year    = {2025},
  doi     = {10.1109/TIT.2024.3504823}
}
```

## License

This repository is licensed under the Apache License, Version 2.0. See
[`LICENSE`](LICENSE).
