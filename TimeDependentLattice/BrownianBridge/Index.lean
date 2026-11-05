/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Basic

/-!
# Brownian-bridge coordinate indices

For `m = 2^J` time steps, the paper uses one endpoint Gaussian coordinate for each Brownian
component and one detail coordinate for every triple `(ℓ, k, r)` with
`ℓ < J`, `k < 2^ℓ`, and `r < noiseDim`.

We represent this structure directly.  The paper's one-based flat coordinate `j` will be introduced
later through an explicit equivalence with `Fin (noiseDim * 2^J)`.
-/

namespace TimeDependentLattice.BrownianBridge

open scoped BigOperators

/-- The number of time steps at refinement depth `J`. -/
def numSteps (J : ℕ) : ℕ := 2 ^ J

@[simp]
theorem numSteps_zero : numSteps 0 = 1 := by
  simp [numSteps]

theorem numSteps_pos (J : ℕ) : 0 < numSteps J := by
  exact Nat.pow_pos (by decide)

/-- The dyadic geometric sum used to count the detail coordinates. -/
theorem sum_pow_two (J : ℕ) : ∑ level : Fin J, 2 ^ level.val = 2 ^ J - 1 := by
  induction J with
  | zero => simp
  | succ J inductionHypothesis =>
      rw [Fin.sum_univ_castSucc]
      simp only [inductionHypothesis, Fin.val_castSucc, Fin.val_last, pow_succ]
      have hpow : 1 ≤ 2 ^ J := Nat.one_le_two_pow
      omega

/-- A detail coordinate `(ℓ, k, r)` in the dyadic Brownian bridge.

The bounds `ℓ < J`, `k < 2^ℓ`, and `r < noiseDim` are carried by the three `Fin` types. -/
abbrev DetailIndex (J noiseDim : ℕ) :=
  Σ level : Fin J, Fin (2 ^ level.val) × Fin noiseDim

/-- All Brownian-bridge coordinates: endpoint coordinates followed by detail coordinates. -/
abbrev Index (J noiseDim : ℕ) := Fin noiseDim ⊕ DetailIndex J noiseDim

/-- The refinement level of a detail coordinate. -/
def DetailIndex.level {J noiseDim : ℕ} (j : DetailIndex J noiseDim) : Fin J := j.1

/-- The dyadic interval number `k` of a detail coordinate. -/
def DetailIndex.location {J noiseDim : ℕ} (j : DetailIndex J noiseDim) : Fin (2 ^ j.level.val) :=
  j.2.1

/-- The Brownian component `r` of a detail coordinate. -/
def DetailIndex.component {J noiseDim : ℕ} (j : DetailIndex J noiseDim) : Fin noiseDim :=
  j.2.2

/-- The Brownian component associated with either an endpoint or detail coordinate. -/
def Index.component {J noiseDim : ℕ} : Index J noiseDim → Fin noiseDim
  | Sum.inl r => r
  | Sum.inr j => j.component

/-- There are no detail coordinates when `J = 0`, matching the paper's convention. -/
theorem no_detail_at_level_zero {noiseDim : ℕ} (j : DetailIndex 0 noiseDim) : False :=
  Fin.elim0 j.level

/-- The exact finite cardinality before simplifying the geometric sum. -/
theorem card_detailIndex (J noiseDim : ℕ) :
    Fintype.card (DetailIndex J noiseDim) =
      ∑ level : Fin J, (2 ^ level.val) * noiseDim := by
  simp [DetailIndex]

/-- Endpoint coordinates plus all detail coordinates. -/
theorem card_index (J noiseDim : ℕ) :
    Fintype.card (Index J noiseDim) =
      noiseDim + ∑ level : Fin J, (2 ^ level.val) * noiseDim := by
  simp [Index]

/-- With `m = 2^J`, the complete Brownian-bridge index has size `noiseDim * m`. -/
theorem card_index_eq (J noiseDim : ℕ) :
    Fintype.card (Index J noiseDim) = noiseDim * numSteps J := by
  rw [card_index, ← Finset.sum_mul, sum_pow_two]
  change noiseDim + (2 ^ J - 1) * noiseDim = noiseDim * 2 ^ J
  have hpow : 1 ≤ 2 ^ J := Nat.one_le_two_pow
  have hsum : 1 + (2 ^ J - 1) = 2 ^ J := by omega
  calc
    noiseDim + (2 ^ J - 1) * noiseDim = (1 + (2 ^ J - 1)) * noiseDim := by
      simp [add_mul]
    _ = 2 ^ J * noiseDim := by rw [hsum]
    _ = noiseDim * 2 ^ J := Nat.mul_comm _ _

end TimeDependentLattice.BrownianBridge
