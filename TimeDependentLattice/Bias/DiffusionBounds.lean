/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.Constants

/-!
# The actual diffusion matrix in dimension-uniform Euler constants

The norm on Mathlib continuous linear maps is the operator norm. Appendix E instead uses
the Hilbert--Schmidt norm. For the paper's fixed Euclidean coordinates it is the square root
of the sum of the squared column norms; the existing `columnSum` already represents that sum.
The bounds below therefore use the actual diffusion map and Assumption 2.3, rather than an
unconnected scalar `sigmaHS` supplied with a separate uniform bound.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators
open TimeDependentLattice.Euler TimeDependentLattice.Trees

/-- The Hilbert--Schmidt norm of the finite-dimensional diffusion in the standard basis. -/
def diffusionHilbertSchmidt {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) : ℝ :=
  Real.sqrt (columnSum diffusion 2 : ℝ)

theorem diffusionHilbertSchmidt_nonneg {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) : 0 ≤ diffusionHilbertSchmidt diffusion :=
  Real.sqrt_nonneg _

/-- The paper's identity `‖Σ‖_HS² = Θ₂`. -/
theorem diffusionHilbertSchmidt_sq {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) :
    diffusionHilbertSchmidt diffusion ^ 2 = (columnSum diffusion 2 : ℝ) :=
  Real.sq_sqrt (NNReal.coe_nonneg _)

/-- The second spatial derivative constant `mathsf B_2` from Assumption 2.1. -/
def secondDriftDerivativeConstant
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) : ℝ :=
  bounds.B₀ * bounds.B₁ ^ 2 * ((2 : ℕ).factorial : ℝ) ^ bounds.τ

theorem secondDriftDerivativeConstant_nonneg
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) : 0 ≤ secondDriftDerivativeConstant bounds := by
  unfold secondDriftDerivativeConstant
  positivity [bounds.B₀_pos]

/-- The actual frozen Jacobian has the paper's first-derivative operator bound. -/
theorem drift_fderiv_norm_le
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T t : ℝ}
    (bounds : GevreyBounds drift payoff T) (ht₀ : 0 ≤ t) (htT : t ≤ T)
    (x : State stateDim) : ‖fderiv ℝ (drift t) x‖ ≤ bounds.driftLipschitzConstant := by
  rw [← norm_iteratedFDeriv_one]
  simpa [GevreyBounds.driftLipschitzConstant] using
    bounds.drift_derivative_norm 1 (by omega) t ht₀ htT x

/-- The Hilbert--Schmidt ideal bound, proved in the paper's fixed coordinates. -/
theorem diffusionHilbertSchmidt_comp_sq_le
    {stateDim noiseDim : ℕ} (A : State stateDim →L[ℝ] State stateDim)
    (diffusion : Diffusion stateDim noiseDim) {L : ℝ} (hL : 0 ≤ L) (hA : ‖A‖ ≤ L) :
    diffusionHilbertSchmidt (A.comp diffusion) ^ 2 ≤
      L ^ 2 * diffusionHilbertSchmidt diffusion ^ 2 := by
  have hterm (r : Fin noiseDim) :
      ‖A (diffusion (noiseBasis r))‖ ^ 2 ≤ L ^ 2 * ‖diffusion (noiseBasis r)‖ ^ 2 := by
    have hnorm := (A.le_opNorm (diffusion (noiseBasis r))).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    calc
      ‖A (diffusion (noiseBasis r))‖ ^ 2 ≤ (L * ‖diffusion (noiseBasis r)‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).2 hnorm
      _ = _ := mul_pow _ _ _
  rw [diffusionHilbertSchmidt_sq, diffusionHilbertSchmidt_sq]
  simp only [columnSum, NNReal.coe_sum, NNReal.coe_rpow, columnNorm, coe_nnnorm,
    Real.rpow_two, ContinuousLinearMap.comp_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ ↦ hterm r

/-- Paper Equation (E.12), with the actual Jacobian and diffusion map. -/
theorem drift_diffusion_hilbertSchmidt_sq_le
    {stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T t : ℝ}
    (bounds : GevreyBounds drift payoff T) (diffusion : Diffusion stateDim noiseDim)
    (ht₀ : 0 ≤ t) (htT : t ≤ T) (x : State stateDim) :
    diffusionHilbertSchmidt ((fderiv ℝ (drift t) x).comp diffusion) ^ 2 ≤
      bounds.driftLipschitzConstant ^ 2 * diffusionHilbertSchmidt diffusion ^ 2 :=
  diffusionHilbertSchmidt_comp_sq_le _ diffusion bounds.driftLipschitzConstant_pos.le
    (drift_fderiv_norm_le bounds ht₀ htT x)

/-- The actual Hessian trace term in the additive-noise Itô formula. -/
def driftDiffusionTrace {stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (t : ℝ) (x : State stateDim) : State stateDim :=
  ∑ r : Fin noiseDim,
    (iteratedFDeriv ℝ 2 (drift t) x) (fun _ ↦ diffusion (noiseBasis r))

/-- Equation (E.11) is a deterministic consequence of the operator norm and diffusion columns. -/
theorem drift_trace_norm_le
    {stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T t : ℝ}
    (bounds : GevreyBounds drift payoff T) (diffusion : Diffusion stateDim noiseDim)
    (ht₀ : 0 ≤ t) (htT : t ≤ T) (x : State stateDim) :
    ‖driftDiffusionTrace drift diffusion t x‖ ≤
      secondDriftDerivativeConstant bounds * diffusionHilbertSchmidt diffusion ^ 2 := by
  have hterm (r : Fin noiseDim) :
      ‖(iteratedFDeriv ℝ 2 (drift t) x) (fun _ ↦ diffusion (noiseBasis r))‖ ≤
        secondDriftDerivativeConstant bounds * ‖diffusion (noiseBasis r)‖ ^ 2 := by
    have h := ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
      (bounds.drift_derivative_norm 2 (by omega) t ht₀ htT x)
      (m := fun _ : Fin 2 ↦ diffusion (noiseBasis r)) (fun _ ↦ le_rfl)
    simpa [secondDriftDerivativeConstant, Fin.prod_univ_two, pow_two] using h
  have hsum : (∑ r : Fin noiseDim, ‖diffusion (noiseBasis r)‖ ^ 2) =
      (columnSum diffusion 2 : ℝ) := by
    simp [columnSum, columnNorm, NNReal.coe_sum]
  calc
    ‖driftDiffusionTrace drift diffusion t x‖ ≤
        ∑ r : Fin noiseDim,
          ‖(iteratedFDeriv ℝ 2 (drift t) x) (fun _ ↦ diffusion (noiseBasis r))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Fin noiseDim,
        secondDriftDerivativeConstant bounds * ‖diffusion (noiseBasis r)‖ ^ 2 :=
      Finset.sum_le_sum (fun r _ ↦ hterm r)
    _ = _ := by rw [← Finset.mul_sum, hsum, diffusionHilbertSchmidt_sq]

/-- Assumption 2.3 gives the actual Hilbert--Schmidt bound used by Appendix E. -/
theorem diffusionHilbertSchmidt_le_twoThirds
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) {M : NNReal}
    (hM : columnSum diffusion (2 / 3) ≤ M) :
    diffusionHilbertSchmidt diffusion ≤ sigmaBoundFromTwoThirds M := by
  have hcolumn := columnSum_le_of_twoThirds_le diffusion hM (v := 2) (by norm_num)
  norm_num at hcolumn
  have hsq : (columnSum diffusion 2 : ℝ) ≤ (M : ℝ) ^ (3 : ℝ) := by
    exact_mod_cast hcolumn
  unfold diffusionHilbertSchmidt sigmaBoundFromTwoThirds
  calc
    Real.sqrt (columnSum diffusion 2 : ℝ) ≤ Real.sqrt ((M : ℝ) ^ (3 : ℝ)) :=
      Real.sqrt_le_sqrt hsq
    _ = (M : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (NNReal.coe_nonneg M)]
      norm_num

/-- The half-order Euler-bias constant is bounded by the common constant using the actual
diffusion-column assumption, without a separate scalar Hilbert--Schmidt premise. -/
theorem biasHalfConstant_le_uniform_of_columns
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (x₀ : State stateDim) {M : NNReal}
    {G0 G1 beta T K0 L Ht R0 : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hbeta : 0 ≤ beta)
    (hinitial : ‖x₀‖ ≤ R0) (hM : columnSum diffusion (2 / 3) ≤ M) :
    biasHalfConstant G0 G1 beta T K0 L Ht ‖x₀‖ (diffusionHilbertSchmidt diffusion) ≤
      uniformBiasHalfConstant G0 G1 beta T K0 L Ht R0 M :=
  biasHalfConstant_le_uniform hT hK0 hL hHt hG0 hG1 hbeta (norm_nonneg x₀)
    hinitial (diffusionHilbertSchmidt_nonneg diffusion)
    (diffusionHilbertSchmidt_le_twoThirds diffusion hM)

/-- The corresponding dimension-uniform comparison for the first-order Euler-bias constant. -/
theorem biasOneConstant_le_uniform_of_columns
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (x₀ : State stateDim) {M : NNReal}
    {G0 G1 beta T K0 L B2 Lt R0 : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2) (hLt : 0 ≤ Lt)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hbeta : 0 ≤ beta)
    (hinitial : ‖x₀‖ ≤ R0) (hM : columnSum diffusion (2 / 3) ≤ M) :
    biasOneConstant G0 G1 beta T K0 L B2 Lt ‖x₀‖ (diffusionHilbertSchmidt diffusion) ≤
      uniformBiasOneConstant G0 G1 beta T K0 L B2 Lt R0 M :=
  biasOneConstant_le_uniform hT hK0 hL hB2 hLt hG0 hG1 hbeta (norm_nonneg x₀)
    hinitial (diffusionHilbertSchmidt_nonneg diffusion)
    (diffusionHilbertSchmidt_le_twoThirds diffusion hM)

end

end TimeDependentLattice.Bias
