/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.GaussianSpaceIdentification
import TimeDependentLattice.Sampling.GaussianSpaceDensity
import TimeDependentLattice.Sampling.PaperTheorems

/-!
# The iterated-density component in equation (5.1) of the paper

The inner integral uses the inactive standard Gaussian densities. The outer integral uses
the active unnormalized exponential weights. The equality with `gaussianSpaceComponent`
is proved below, including the normalization and the actual Euler mixed derivative.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.Analysis TimeDependentLattice.BrownianBridge
  TimeDependentLattice.Euler TimeDependentLattice.Regularity TimeDependentLattice.Trees

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The signed inner Gaussian integral in paper (5.1); the square is taken after this integral. -/
def paperInactiveIntegral (support : Finset ι) (f : (ι → ℝ) → ℝ) (a : ↥support → ℝ) : ℝ :=
  ∫ b : {j // j ∉ support} → ℝ,
    f ((splitActiveInactive support).symm (a, b)) * ∏ j, gaussianPDFReal 0 1 (b j)

/-- The iterated, density-weighted square in paper (5.1), applied to the derivative `f`. -/
def paperGaussianSpaceComponentSq
    (support : Finset ι) (α : ℝ) (f : (ι → ℝ) → ℝ) : ℝ :=
  ∫ a : ↥support → ℝ,
    paperInactiveIntegral support f a ^ 2 * ∏ j, Real.exp (-2 * α * |a j|)

/-- The nonnegative component whose square is the integral displayed in paper (5.1). -/
def paperGaussianSpaceComponent
    (support : Finset ι) (α : ℝ) (f : (ι → ℝ) → ℝ) : ℝ :=
  Real.sqrt (paperGaussianSpaceComponentSq support α f)

theorem inactiveGaussianIntegral_eq_paperInactiveIntegral
    (support : Finset ι) (f : (ι → ℝ) → ℝ) (a : ↥support → ℝ) :
    inactiveGaussianIntegral support f a = paperInactiveIntegral support f a := by
  exact integral_gaussianProductMeasure
    (fun b ↦ f ((splitActiveInactive support).symm (a, b)))

/-- The complete square identity with the Lebesgue densities of paper (5.1). -/
theorem gaussianSpaceComponent_sq_eq_paper
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (hybridProductMeasure support α)) :
    gaussianSpaceComponent support α f ^ 2 = paperGaussianSpaceComponentSq support α f := by
  rw [gaussianSpaceComponent_sq_eq_active_integral_of_memLp_two support hα hf]
  change α ^ (-(support.card : ℝ)) *
    (∫ a, inactiveGaussianIntegral support f a ^ 2
      ∂Measure.pi (fun _ : ↥support ↦ laplaceCoordinateMeasure α)) = _
  rw [integral_laplaceProductMeasure hα]
  simp only [Fintype.card_coe]
  rw [Real.rpow_neg hα.le, Real.rpow_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hα.ne'), one_mul]
  unfold paperGaussianSpaceComponentSq
  simp_rw [inactiveGaussianIntegral_eq_paperInactiveIntegral]

/-- The conditional-expectation component is exactly the paper's nonnegative component. -/
theorem gaussianSpaceComponent_eq_paper
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (hybridProductMeasure support α)) :
    gaussianSpaceComponent support α f = paperGaussianSpaceComponent support α f := by
  unfold paperGaussianSpaceComponent
  rw [← gaussianSpaceComponent_sq_eq_paper support hα hf]
  exact (Real.sqrt_sq (gaussianSpaceComponent_nonneg support hα.le f)).symm

/-- The actual Euler derivative identifies (5.1) using only the model and origin bounds. -/
theorem eulerGaussianSpaceComponent_eq_paper
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim) (horigin : ∀ t, 0 ≤ t → t ≤ T → ‖drift t 0‖ ≤ K₀)
    (support : Finset (Index J noiseDim)) (hsupport : support.Nonempty) :
    eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀ support =
      paperGaussianSpaceComponent support
        (hybridAlpha bounds.β T bounds.driftLipschitzConstant (diffusionThetaOne diffusion))
        (fun z ↦ mixedDerivative (integrand drift diffusion payoff T x₀) support
          (bridgeInput z)) := by
  have hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i) (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖ := by
    intro z i hi
    exact bounds.drift_norm_le_origin_add_lipschitz horigin
      (gridTime_nonneg hT.le J i) (gridTime_le_terminal hT.le J hi.le) _
  exact gaussianSpaceComponent_eq_paper support
    (zero_lt_one.trans_le (one_le_hybridAlpha bounds.β_pos.le
      (diffusionThetaOne_nonneg diffusion)))
    (mixedDerivative_eulerIntegrand_memLp_two bounds hT hK₀
      x₀ support hsupport hdrift)

/-- The sampling theorem's component is the paper component, with no extra input. -/
theorem EulerSamplingInputs.component_eq_paper
    {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε : ℝ}
    {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ}
    {x₀ : State stateDim}
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (support : Finset (Index J noiseDim)) (hsupport : support.Nonempty) :
    eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀ support =
      paperGaussianSpaceComponent support
        (hybridAlpha bounds.β T bounds.driftLipschitzConstant (diffusionThetaOne diffusion))
        (fun z ↦ mixedDerivative (integrand drift diffusion payoff T x₀) support
          (bridgeInput z)) := by
  exact eulerGaussianSpaceComponent_eq_paper bounds data.time_pos data.origin_nonneg
    x₀ data.drift_origin support hsupport

end

end TimeDependentLattice.Sampling
