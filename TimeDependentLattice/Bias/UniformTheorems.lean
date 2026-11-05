/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.EulerTheorems

/-!
# Dimension-uniform Euler convergence rates

These are the actual strong-error and payoff-bias conclusions of paper Theorems 3.7(ii)
and 3.8(ii). The constants are the paper's formulas evaluated at
`(initialNorm, sigmaHS) = (R0, M^(3/2))`. For a family of dimensions, the scalar model
parameters in `bounds`, `K0`, and `Ht` or `Lt` are the common parameters of Assumption 2.2.
The diffusion entering the stochastic inputs and the column-sum hypothesis is the same map.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped ENNReal
open MeasureTheory TimeDependentLattice.Euler TimeDependentLattice.Trees

/-- The paper's half-order strong constant evaluated at the common dimension bounds. -/
def uniformStrongHalfConstant (T K0 L Ht R0 : ℝ) (M : NNReal) : ℝ :=
  strongHalfConstant T K0 L Ht R0 (sigmaBoundFromTwoThirds M)

/-- Theorem 3.7(ii): a dimension-uniform bound for the actual maximum strong error. -/
theorem theorem3_7_coupled_strong_uniform
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {stateDim noiseDim m : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 Ht R0 : ℝ} {diffusion : Diffusion stateDim noiseDim}
    {bounds : GevreyBounds drift payoff T} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim} {M : NNReal}
    (data : HalfOrderStochasticInputs μ bounds m K0 Ht
      (diffusionHilbertSchmidt diffusion) x₀ noise X)
    (hinitial : ‖x₀‖ ≤ R0) (hM : columnSum diffusion (2 / 3) ≤ M) :
    lpNorm (gridMaxNorm
      (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X) m) 2 μ ≤
      uniformStrongHalfConstant T K0 bounds.driftLipschitzConstant Ht R0 M *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hconstant := strongHalfConstant_mono (K0 := K0)
    data.time_nonneg bounds.driftLipschitzConstant_pos.le data.holder_nonneg
    hinitial (diffusionHilbertSchmidt_le_twoThirds diffusion hM)
  exact (theorem3_7_coupled_strong data).trans
    (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Theorem 3.7(ii): the actual expectation bias with the common half-order constant. -/
theorem theorem3_7_coupled_bias_uniform
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {stateDim noiseDim m : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 Ht R0 : ℝ} {diffusion : Diffusion stateDim noiseDim}
    {bounds : GevreyBounds drift payoff T} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim} {M : NNReal}
    (data : HalfOrderStochasticInputs μ bounds m K0 Ht
      (diffusionHilbertSchmidt diffusion) x₀ noise X)
    (hinitial : ‖x₀‖ ≤ R0) (hM : columnSum diffusion (2 / 3) ≤ M) :
    |(∫ ω, payoff (coupledEulerChain drift (uniformEulerGrid T m)
        (T / (m : ℝ)) x₀ noise m ω) ∂μ) - (∫ ω, payoff (X T ω) ∂μ)| ≤
      uniformBiasHalfConstant bounds.G₀ bounds.G₁ bounds.β T K0
        bounds.driftLipschitzConstant Ht R0 M * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hconstant := biasHalfConstant_le_uniform_of_columns diffusion x₀
    data.time_nonneg data.origin_nonneg bounds.driftLipschitzConstant_pos.le
    data.holder_nonneg bounds.G₀_pos.le bounds.G₁_pos.le bounds.β_pos.le hinitial hM
  exact (theorem3_7_coupled_bias data).trans
    (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Theorem 3.8(ii): the actual expectation bias with the common first-order constant. -/
theorem theorem3_8_coupled_bias_uniform
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {stateDim noiseDim m : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 Lt R0 : ℝ} {diffusion : Diffusion stateDim noiseDim}
    {bounds : GevreyBounds drift payoff T} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim} {M : NNReal}
    (data : OneOrderStochasticInputs μ bounds diffusion m K0 Lt x₀ noise X)
    (hinitial : ‖x₀‖ ≤ R0) (hM : columnSum diffusion (2 / 3) ≤ M) :
    |(∫ ω, payoff (coupledEulerChain drift (uniformEulerGrid T m)
        (T / (m : ℝ)) x₀ noise m ω) ∂μ) - (∫ ω, payoff (X T ω) ∂μ)| ≤
      uniformBiasOneConstant bounds.G₀ bounds.G₁ bounds.β T K0
        bounds.driftLipschitzConstant (secondDriftDerivativeConstant bounds) Lt R0 M *
          (m : ℝ) ^ (-(1 : ℝ)) := by
  have hconstant := biasOneConstant_le_uniform_of_columns diffusion x₀
    data.time_nonneg data.origin_nonneg bounds.driftLipschitzConstant_pos.le
    (secondDriftDerivativeConstant_nonneg bounds) data.temporal_nonneg
    bounds.G₀_pos.le bounds.G₁_pos.le bounds.β_pos.le hinitial hM
  exact (theorem3_8_coupled_bias data).trans
    (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end

end TimeDependentLattice.Bias
