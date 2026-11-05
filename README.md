# Lattice4SDE-Lean

Lean 4 formalization of the paper *Randomly shifted lattice rules for SDEs with
constant diffusion: error bounds uniform in time discretization and dimension*.

Authors: **Du Ouyang, Josef Dick, and Ziyang Ye**.

## Build

The project pins Lean **v4.35.0-rc3** in `lean-toolchain` and Mathlib **v4.35.0-rc3**
in `lakefile.toml`. The committed `lake-manifest.json` fixes Mathlib at
`c55e6e786f49471c72fbddbec5415808896aec1e` and records its dependencies.

With `elan` installed, run these commands from this directory on the first build:

```text
lake exe cache get
lake build
```

Subsequent checks use `lake build`. The `.lake` directory contains downloaded dependencies
and generated build files.

GitHub CI runs the Lean build with the Mathlib cache. Automatic documentation deployment
and release creation are disabled; dependency updates can be requested manually.

## Main entry points

Paths below are relative to `TimeDependentLattice/`. Start with these files to read the
final statements; their imports lead to the supporting proofs.

| Paper result | Lean entry point |
| --- | --- |
| Theorem 3.1, single and median sampling errors | [Sampling/PaperTheorems.lean](TimeDependentLattice/Sampling/PaperTheorems.lean): `single_real`, `median_real` |
| Corollary 3.4, dimension-uniform sampling errors | [Sampling/PaperUniformTheorems.lean](TimeDependentLattice/Sampling/PaperUniformTheorems.lean) |
| Theorem 4.1, derivative summability | [Sampling/DimensionUniform.lean](TimeDependentLattice/Sampling/DimensionUniform.lean): `theorem4_1_with_paper_constant` |
| Theorems 3.7 and 3.8, strong error and Euler bias | [Bias/EulerTheorems.lean](TimeDependentLattice/Bias/EulerTheorems.lean) |
| Theorems 3.7(ii) and 3.8(ii), dimension-uniform Euler rates | [Bias/UniformTheorems.lean](TimeDependentLattice/Bias/UniformTheorems.lean) |
| Corollary 3.9, single-rule total error | [Bias/PaperTotalError.lean](TimeDependentLattice/Bias/PaperTotalError.lean) |
| Corollary 3.9, median total error | [Bias/PaperMedianTotalError.lean](TimeDependentLattice/Bias/PaperMedianTotalError.lean) |
| Corollary 3.9, dimension-uniform total errors | [Bias/PaperUniformTotalError.lean](TimeDependentLattice/Bias/PaperUniformTotalError.lean) |

The derivative-tree expansion is in
[Trees/DerivativeExpansion.lean](TimeDependentLattice/Trees/DerivativeExpansion.lean).
The scalar Gronwall results in `Bias/EulerBias.lean` and the conditional combinations in
`Bias/TotalError.lean` and `Bias/TotalErrorSpecializations.lean` are supporting lemmas.

The paper correspondence and precise external mathematical inputs are documented in
[the blueprint](blueprint/main_lean_blueprint.tex).

## License

The source code is distributed under the [Apache License 2.0](LICENSE).
