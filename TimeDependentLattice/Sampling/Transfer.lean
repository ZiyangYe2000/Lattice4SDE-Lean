/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Regularity.MajorantSummation

/-!
# Transfer from derivative envelopes to the lattice fractional scale

This file formalizes the finite-sum algebra between paper Lemma 5.2, Theorem 4.1, and the
definition of `C_lam(F)` in Equation (5.4).
-/

namespace TimeDependentLattice.Sampling

open scoped BigOperators
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

noncomputable section

/-- The exponent `2lam / (1 + lam)` used in the lattice moment estimate. -/
def latticeDerivativeExponent (lam : ℝ) : ℝ :=
  2 * lam / (1 + lam)

/-- The subset-weight base `ρ^(1/(1+lam))` used when applying Theorem 4.1. -/
def latticeSubsetBase (ρ lam : ℝ) : ℝ :=
  ρ ^ (1 / (1 + lam))

/-- The inner sum in Equation (5.4), before raising it to `1 + lam`. -/
def latticeFractionalSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ lam : ℝ) (B : Finset ι → ℝ) : ℝ :=
  ∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
    ρ ^ ((u.card : ℝ) / (1 + lam)) * B u ^ latticeDerivativeExponent lam

/-- Equation (5.4), expressed through its finite nonempty-subset sum. -/
def latticeMomentScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ lam : ℝ) (B : Finset ι → ℝ) : ℝ :=
  latticeFractionalSum ρ lam B ^ (1 + lam)

/-- The explicit right-hand side furnished by Theorem 4.1 for a given subset base and
derivative exponent. -/
def derivativeSummabilityConstant
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (ρ lam : ℝ) : ℝ :=
  let p := latticeDerivativeExponent lam
  let κ := latticeSubsetBase ρ lam
  let rhoIntermediate := intermediateExponent bounds.τ p
  let κrho := κ ^ (rhoIntermediate / p)
  let A := κrho * bounds.majorantConstant ^ rhoIntermediate
  let H := treeSubsetConstant diffusion T A rhoIntermediate bounds.τ
  derivativeRhoConstant H bounds.majorantConstant bounds.τ rhoIntermediate ^
    (p / rhoIntermediate)

theorem latticeSubsetBase_pow_card
    {ρ lam : ℝ} (hρ : 0 ≤ ρ) (hlam : lam ≠ -1) (n : ℕ) :
    latticeSubsetBase ρ lam ^ n = ρ ^ ((n : ℝ) / (1 + lam)) := by
  unfold latticeSubsetBase
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ]
  congr 1
  have hden : 1 + lam ≠ 0 := by
    intro hzero
    apply hlam
    linarith
  field_simp [hden]

/-- The fractional sum is exactly a `weightedDerivativeSum` with the paper's choices of
`κ` and `p`. -/
theorem latticeFractionalSum_eq_weightedDerivativeSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ lam : ℝ} (hρ : 0 ≤ ρ) (hlam : lam ≠ -1) (B : Finset ι → ℝ) :
    latticeFractionalSum ρ lam B =
      weightedDerivativeSum (latticeSubsetBase ρ lam)
        (latticeDerivativeExponent lam) B := by
  unfold latticeFractionalSum weightedDerivativeSum
  apply Finset.sum_congr rfl
  intro u hu
  rw [latticeSubsetBase_pow_card hρ hlam]

/-- Lemma 5.2 transfers the Theorem 4.1 derivative sum to the inner lattice scale. -/
theorem latticeFractionalSum_le_of_transfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ lam C : ℝ} {B D : Finset ι → ℝ}
    (hρ : 0 ≤ ρ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hB : ∀ u, u.Nonempty → 0 ≤ B u ∧ B u ≤ C * D u)
    (hD : ∀ u, u.Nonempty → 0 ≤ D u) :
    latticeFractionalSum ρ lam B ≤
      C ^ latticeDerivativeExponent lam *
        latticeFractionalSum ρ lam D := by
  have hp : 0 < latticeDerivativeExponent lam := by
    unfold latticeDerivativeExponent
    positivity
  unfold latticeFractionalSum
  calc
    (∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
        ρ ^ ((u.card : ℝ) / (1 + lam)) * B u ^ latticeDerivativeExponent lam) ≤
      ∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
        ρ ^ ((u.card : ℝ) / (1 + lam)) *
          (C * D u) ^ latticeDerivativeExponent lam := by
      apply Finset.sum_le_sum
      intro u hu
      have hnonempty : u.Nonempty := (Finset.mem_filter.mp hu).2
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hB u hnonempty).1 (hB u hnonempty).2 hp.le)
        (Real.rpow_nonneg hρ _)
    _ = ∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
        C ^ latticeDerivativeExponent lam *
          (ρ ^ ((u.card : ℝ) / (1 + lam)) *
            D u ^ latticeDerivativeExponent lam) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hnonempty : u.Nonempty := (Finset.mem_filter.mp hu).2
      rw [Real.mul_rpow hC (hD u hnonempty)]
      ring
    _ = C ^ latticeDerivativeExponent lam *
        ∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
          ρ ^ ((u.card : ℝ) / (1 + lam)) *
            D u ^ latticeDerivativeExponent lam := by
      rw [Finset.mul_sum]

/-- Direct combination of Lemma 5.2 with any Theorem 4.1 bound. -/
theorem latticeFractionalSum_le_of_derivativeSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ lam C derivativeBound : ℝ} {B D : Finset ι → ℝ}
    (hρ : 0 ≤ ρ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hB : ∀ u, u.Nonempty → 0 ≤ B u ∧ B u ≤ C * D u)
    (hD : ∀ u, u.Nonempty → 0 ≤ D u)
    (hsum : weightedDerivativeSum (latticeSubsetBase ρ lam)
      (latticeDerivativeExponent lam) D ≤ derivativeBound) :
    latticeFractionalSum ρ lam B ≤
      C ^ latticeDerivativeExponent lam * derivativeBound := by
  calc
    latticeFractionalSum ρ lam B ≤
        C ^ latticeDerivativeExponent lam * latticeFractionalSum ρ lam D :=
      latticeFractionalSum_le_of_transfer hρ hlam hC hB hD
    _ = C ^ latticeDerivativeExponent lam *
        weightedDerivativeSum (latticeSubsetBase ρ lam)
          (latticeDerivativeExponent lam) D := by
      rw [latticeFractionalSum_eq_weightedDerivativeSum hρ (by linarith) D]
    _ ≤ C ^ latticeDerivativeExponent lam * derivativeBound := by
      gcongr

/-- Lemma 5.2 and Theorem 4.1 give the uniform inner bound needed in the sampling proof. -/
theorem latticeFractionalSum_normalizedDerivativeEnvelope_le
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {ρ lam C : ℝ}
    (hρ : 0 < ρ) (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1)
    (hC : 0 ≤ C) (B : Finset (Index J noiseDim) → ℝ)
    (hB : ∀ u, u.Nonempty →
      0 ≤ B u ∧ B u ≤ C *
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ u) :
    latticeFractionalSum ρ lam B ≤
      C ^ latticeDerivativeExponent lam *
        (let p := latticeDerivativeExponent lam
         let κ := latticeSubsetBase ρ lam
         let rhoIntermediate := intermediateExponent bounds.τ p
         let κrho := κ ^ (rhoIntermediate / p)
         let A := κrho * bounds.majorantConstant ^ rhoIntermediate
         let H := treeSubsetConstant diffusion T A rhoIntermediate bounds.τ
         derivativeRhoConstant H bounds.majorantConstant bounds.τ rhoIntermediate ^
           (p / rhoIntermediate)) := by
  have hlam : 0 < lam := (by linarith : 0 < lam)
  have hp : 2 / 3 < latticeDerivativeExponent lam := by
    unfold latticeDerivativeExponent
    apply (lt_div_iff₀ (by linarith : 0 < 1 + lam)).2
    nlinarith
  have hκ : 0 < latticeSubsetBase ρ lam := by
    exact Real.rpow_pos_of_pos hρ _
  let D : Finset (Index J noiseDim) → ℝ :=
    normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀
  have hD : ∀ u, u.Nonempty → 0 ≤ D u := by
    intro u hu
    exact normalizedDerivativeEnvelope_nonneg drift diffusion payoff T bounds.β x₀ u
      (normalizedMixedDerivativeAt_bddAbove bounds hT x₀ u hu)
  have hsum := theorem4_1 (diffusion := diffusion) bounds hT x₀ hκ hp J
  simpa [D] using
    (latticeFractionalSum_le_of_derivativeSum hρ.le hlam hC hB hD hsum)

/-- Named-constant form of the preceding theorem. -/
theorem latticeFractionalSum_normalizedDerivativeEnvelope_le_constant
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {ρ lam C : ℝ}
    (hρ : 0 < ρ) (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1)
    (hC : 0 ≤ C) (B : Finset (Index J noiseDim) → ℝ)
    (hB : ∀ u, u.Nonempty →
      0 ≤ B u ∧ B u ≤ C *
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ u) :
    latticeFractionalSum ρ lam B ≤
      C ^ latticeDerivativeExponent lam *
        derivativeSummabilityConstant (diffusion := diffusion) bounds ρ lam := by
  simpa [derivativeSummabilityConstant] using
    (latticeFractionalSum_normalizedDerivativeEnvelope_le
      bounds hT x₀ hρ hlamLower hlamUpper hC B hB)

/-- Equation (5.8): Lemma 5.2 and Theorem 4.1 bound the optimized lattice scale. -/
theorem latticeMomentScale_normalizedDerivativeEnvelope_le
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {ρ lam C : ℝ}
    (hρ : 0 < ρ) (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1)
    (hC : 0 ≤ C) (B : Finset (Index J noiseDim) → ℝ)
    (hBall : ∀ u, 0 ≤ B u)
    (hB : ∀ u, u.Nonempty →
      B u ≤ C * normalizedDerivativeEnvelope
        drift diffusion payoff T bounds.β x₀ u) :
    latticeMomentScale ρ lam B ≤
      (C ^ latticeDerivativeExponent lam *
        derivativeSummabilityConstant (diffusion := diffusion) bounds ρ lam) ^ (1 + lam) := by
  have hsum := latticeFractionalSum_normalizedDerivativeEnvelope_le_constant
    bounds hT x₀ hρ hlamLower hlamUpper hC B
      (fun u hu ↦ ⟨hBall u, hB u hu⟩)
  have hsumNonneg : 0 ≤ latticeFractionalSum ρ lam B := by
    unfold latticeFractionalSum
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg (hBall u) _)
  unfold latticeMomentScale
  exact Real.rpow_le_rpow hsumNonneg hsum (by linarith)

end

end TimeDependentLattice.Sampling

