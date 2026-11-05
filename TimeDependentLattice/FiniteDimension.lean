/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Finite-dimensional data

This file defines the finite-dimensional state and noise spaces used in the paper, together with
the diffusion-column sums from Equation `eq:column-sums`.  It also proves the monotonicity estimate
in Equation `eq:column-monotonicity`.

The column norms and their sums are represented in `ℝ≥0`.  This records their nonnegativity in the
type and avoids carrying separate nonnegativity hypotheses through later estimates.
-/

namespace TimeDependentLattice

noncomputable section

/-- The state space `ℝ^d`, equipped with its Euclidean norm. -/
abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Brownian-noise space `ℝ^d`, equipped with its Euclidean norm. -/
abbrev Noise (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A constant diffusion matrix, represented as a continuous linear map. -/
abbrev Diffusion (stateDim noiseDim : ℕ) := Noise noiseDim →L[ℝ] State stateDim

/-- The `r`-th standard basis vector in the noise space. -/
def noiseBasis {d : ℕ} (r : Fin d) : Noise d := PiLp.single 2 r 1

/-- Paper notation `σ_r = |Σ e_r|₂`. -/
def columnNorm {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (r : Fin noiseDim) : NNReal :=
  ‖diffusion (noiseBasis r)‖₊

/-- Paper notation `Θ_p = ∑_r σ_r^p`. -/
def columnSum {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (p : ℝ) : NNReal :=
  ∑ r, columnNorm diffusion r ^ p

/-- For a finite family of nonnegative numbers and `1 ≤ p`, the sum of the `p`-th powers is at
most the `p`-th power of the sum. -/
lemma sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (f : ι → NNReal) {p : ℝ}
    (hp : 1 ≤ p) :
    ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hp)]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        f a ^ p + ∑ i ∈ s, f i ^ p ≤ f a ^ p + (∑ i ∈ s, f i) ^ p :=
          add_le_add (le_refl _) ih
        _ ≤ (f a + ∑ i ∈ s, f i) ^ p := NNReal.add_rpow_le_rpow_add _ _ hp

/-- Finite-sequence `ℓ^p` monotonicity in the unnormalized form used by the paper. -/
theorem columnSum_mono {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {q p : ℝ} (hq : 0 < q) (hqp : q ≤ p) :
    columnSum diffusion p ≤ columnSum diffusion q ^ (p / q) := by
  have hpq : 1 ≤ p / q := (le_div_iff₀ hq).2 (by simpa using hqp)
  calc
    columnSum diffusion p = ∑ r, (columnNorm diffusion r ^ q) ^ (p / q) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← NNReal.rpow_mul, div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    _ ≤ (∑ r, columnNorm diffusion r ^ q) ^ (p / q) :=
      sum_rpow_le_rpow_sum Finset.univ (fun r ↦ columnNorm diffusion r ^ q) hpq
    _ = columnSum diffusion q ^ (p / q) := rfl

/-- Equation `eq:column-monotonicity`: for `2/3 ≤ v`,
`Θ_v ≤ Θ_(2/3) ^ (3v/2)`. -/
theorem columnSum_le_twoThirds {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) {v : ℝ} (hv : 2 / 3 ≤ v) :
    columnSum diffusion v ≤ columnSum diffusion (2 / 3) ^ (3 * v / 2) := by
  have hexponent : v / (2 / 3) = 3 * v / 2 := by ring
  simpa only [hexponent] using
    columnSum_mono diffusion (q := 2 / 3) (p := v) (by norm_num) hv

/-- The uniform `Θ_(2/3)` assumption controls every `Θ_v` with `v ≥ 2/3`. -/
theorem columnSum_le_of_twoThirds_le {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) {M : NNReal} {v : ℝ}
    (hM : columnSum diffusion (2 / 3) ≤ M) (hv : 2 / 3 ≤ v) :
    columnSum diffusion v ≤ M ^ (3 * v / 2) := by
  refine (columnSum_le_twoThirds diffusion hv).trans ?_
  exact NNReal.rpow_le_rpow hM (by positivity)

end

end TimeDependentLattice
