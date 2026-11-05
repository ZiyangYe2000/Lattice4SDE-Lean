/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.EulerTheorems
import TimeDependentLattice.Bias.TotalError

/-!
# Total error with the verified half-order and first-order Euler bias

These are the two sufficient-condition specializations of the paper's general bias
assumption. The sampling theorem is supplied for the chosen single or median estimator;
the Euler bias is deduced from the SDE input records by the proved convergence theorems.
No Euler-bias bound, scalar error recurrence, or payoff-transfer inequality is an input.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open MeasureTheory TimeDependentLattice.Euler TimeDependentLattice.Trees

/-- Corollary 3.9 with `theta = 1/2`, using Theorem 3.7 to verify the bias premise. -/
theorem corollary3_9_half_from_sde_inputs
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {stateDim m N : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 Ht sigmaHS samplingConstant epsilon q : ℝ}
    {x₀ : State stateDim} {noise X : ℝ → Ω → State stateDim}
    {bounds : GevreyBounds drift payoff T}
    (inputs : HalfOrderStochasticInputs μ bounds m K0 Ht sigmaHS x₀ noise X)
    (estimator : Ξ → ℝ) (hq : 1 ≤ q)
    (hmeas : AEStronglyMeasurable
      (fun ξ ↦ estimator ξ - ∫ ω,
        payoff (coupledEulerChain drift (uniformEulerGrid T m)
          (T / (m : ℝ)) x₀ noise m ω) ∂μ) ν)
    (hsampling : eLpNorm'
      (fun ξ ↦ estimator ξ - ∫ ω,
        payoff (coupledEulerChain drift (uniformEulerGrid T m)
          (T / (m : ℝ)) x₀ noise m ω) ∂μ) q ν ≤
        ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon))) :
    eLpNorm' (fun ξ ↦ estimator ξ - ∫ ω, payoff (X T ω) ∂μ) q ν ≤
      ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon)) +
        ENNReal.ofReal
          (biasHalfConstant bounds.G₀ bounds.G₁ bounds.β T K0
            bounds.driftLipschitzConstant Ht ‖x₀‖ sigmaHS *
              (m : ℝ) ^ (-(1 / 2 : ℝ))) := by
  exact totalError_of_sampling_and_real_bias estimator
    (∫ ω, payoff (coupledEulerChain drift (uniformEulerGrid T m)
      (T / (m : ℝ)) x₀ noise m ω) ∂μ)
    (∫ ω, payoff (X T ω) ∂μ) hq hmeas hsampling (theorem3_7_coupled_bias inputs)

/-- Corollary 3.9 with `theta = 1`, using Theorem 3.8 to verify the bias premise. -/
theorem corollary3_9_one_from_sde_inputs
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {stateDim noiseDim m N : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 Lt samplingConstant epsilon q : ℝ}
    {diffusion : Diffusion stateDim noiseDim}
    {x₀ : State stateDim} {noise X : ℝ → Ω → State stateDim}
    {bounds : GevreyBounds drift payoff T}
    (inputs : OneOrderStochasticInputs μ bounds diffusion m K0 Lt x₀ noise X)
    (estimator : Ξ → ℝ) (hq : 1 ≤ q)
    (hmeas : AEStronglyMeasurable
      (fun ξ ↦ estimator ξ - ∫ ω,
        payoff (coupledEulerChain drift (uniformEulerGrid T m)
          (T / (m : ℝ)) x₀ noise m ω) ∂μ) ν)
    (hsampling : eLpNorm'
      (fun ξ ↦ estimator ξ - ∫ ω,
        payoff (coupledEulerChain drift (uniformEulerGrid T m)
          (T / (m : ℝ)) x₀ noise m ω) ∂μ) q ν ≤
        ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon))) :
    eLpNorm' (fun ξ ↦ estimator ξ - ∫ ω, payoff (X T ω) ∂μ) q ν ≤
      ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon)) +
        ENNReal.ofReal
          (biasOneConstant bounds.G₀ bounds.G₁ bounds.β T K0
            bounds.driftLipschitzConstant (secondDriftDerivativeConstant bounds) Lt ‖x₀‖
              (diffusionHilbertSchmidt diffusion) * (m : ℝ) ^ (-(1 : ℝ))) := by
  exact totalError_of_sampling_and_real_bias estimator
    (∫ ω, payoff (coupledEulerChain drift (uniformEulerGrid T m)
      (T / (m : ℝ)) x₀ noise m ω) ∂μ)
    (∫ ω, payoff (X T ω) ∂μ) hq hmeas hsampling (theorem3_8_coupled_bias inputs)

end

end TimeDependentLattice.Bias
