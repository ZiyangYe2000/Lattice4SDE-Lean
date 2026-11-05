/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.GaussianSpaceNorm
import TimeDependentLattice.Sampling.Transfer

/-!
# Lemma 5.2 inserted into the lattice moment scale

This file specializes the abstract finite-sum transfer algebra to the actual Euler integrand and
the Gaussian-space components from Equation (5.1).
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open TimeDependentLattice.Analysis TimeDependentLattice.BrownianBridge
  TimeDependentLattice.Euler TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- The family `u ↦ B_u(F_m)` for the dyadic Euler integrand. -/
def eulerGaussianSpaceComponent
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T : ℝ)
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim)) : ℝ :=
  gaussianSpaceComponent support
    (hybridAlpha bounds.β T bounds.driftLipschitzConstant
      (diffusionThetaOne diffusion))
    (fun z : Index J noiseDim → ℝ =>
      mixedDerivative (integrand drift diffusion payoff T x₀) support
        (bridgeInput z))

theorem eulerGaussianSpaceComponent_nonneg
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T : ℝ)
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim)) :
    0 ≤ eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀ support := by
  unfold eulerGaussianSpaceComponent
  apply gaussianSpaceComponent_nonneg support
  exact (one_le_hybridAlpha bounds.β_pos.le
    (diffusionThetaOne_nonneg diffusion)).trans' zero_le_one

/-- Lemma 5.2 in the family-valued form consumed by the sampling proof. -/
theorem eulerGaussianSpaceComponent_le
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖)
    (support : Finset (Index J noiseDim)) (hsupport : support.Nonempty) :
    eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀ support ≤
      Real.sqrt
          (auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
            ‖x₀‖ (diffusionThetaOne diffusion)) *
        normalizedDerivativeEnvelope
          drift diffusion payoff T bounds.β x₀ support := by
  exact lemma5_2 bounds hT hK₀ x₀ support hsupport hdrift

/-- An intermediate moment bound for the actual Euler `B_u(F_m)` family.
`Sampling/PaperConstants.lean` lifts this bound to the paper's constant in (5.8). -/
theorem latticeMomentScale_eulerGaussianSpaceComponent_le
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖)
    {ρ lam : ℝ} (hρ : 0 < ρ)
    (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1) :
    latticeMomentScale ρ lam
        (eulerGaussianSpaceComponent (J := J)
          drift diffusion payoff T bounds x₀) ≤
      (Real.sqrt
          (auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
            ‖x₀‖ (diffusionThetaOne diffusion)) ^
          latticeDerivativeExponent lam *
        derivativeSummabilityConstant (diffusion := diffusion) bounds ρ lam) ^
          (1 + lam) := by
  apply latticeMomentScale_normalizedDerivativeEnvelope_le
    bounds hT x₀ hρ hlamLower hlamUpper
  · exact Real.sqrt_nonneg _
  · intro support
    exact eulerGaussianSpaceComponent_nonneg
      drift diffusion payoff T bounds x₀ support
  · intro support hsupport
    exact eulerGaussianSpaceComponent_le bounds hT hK₀ x₀ hdrift support hsupport

end

end TimeDependentLattice.Sampling
