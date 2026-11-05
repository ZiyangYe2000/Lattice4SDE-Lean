/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TimeDependentLattice.Sampling.HybridMomentAssembly
import TimeDependentLattice.Regularity.Envelope

/-!
# The derivative moment used in paper Lemma 5.2

This file combines the normalized derivative envelope with the hybrid exponential moment from
Lemma 5.1.  It is the probabilistic core of the estimate for `B_u(F_m)`.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped ContDiff ENNReal
open MeasureTheory
open TimeDependentLattice.Analysis TimeDependentLattice.BrownianBridge
  TimeDependentLattice.Euler TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- Smoothness of the finite-dimensional Euler integrand under Assumption 2.1. -/
theorem contDiff_eulerIntegrand
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim) :
    ContDiff ℝ ∞ (integrand (J := J) drift diffusion payoff T x₀) := by
  unfold integrand terminalState
  simpa [Function.comp_def] using
    (ContDiff.comp bounds.payoff_smooth
      (contDiff_stateNat drift diffusion T x₀ bounds.drift_smooth (numSteps J)))

/-- Hence every canonical mixed coordinate derivative used in the paper is continuous. -/
theorem continuous_mixedDerivative_eulerIntegrand
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim)) :
    Continuous (fun z : Input J noiseDim =>
      mixedDerivative (integrand drift diffusion payoff T x₀) support z) := by
  unfold mixedDerivative
  have hiter : Continuous (iteratedFDeriv ℝ support.card
      (integrand (J := J) drift diffusion payoff T x₀)) :=
    (contDiff_eulerIntegrand (J := J)
      (diffusion := diffusion) bounds x₀).continuous_iteratedFDeriv (by simp)
  exact hiter.eval continuous_const

/-- The normalized envelope gives the paper's pointwise estimate
`|∂_u F_m(z)| ≤ D_{m,u} exp (β |X_T^h(z)|)`. -/
theorem abs_mixedDerivative_integrand_le_envelope_mul_exp
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty) (z : Input J noiseDim) :
    |mixedDerivative (integrand drift diffusion payoff T x₀) support z| ≤
      normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support *
        Real.exp (bounds.β * ‖terminalState drift diffusion T x₀ z‖) := by
  have hbounded := normalizedMixedDerivativeAt_bddAbove
    (diffusion := diffusion) bounds hT x₀ support hsupport
  have henvelope := normalizedMixedDerivativeAt_le_envelope
    drift diffusion payoff T bounds.β x₀ support hbounded z
  have hexp : 0 < Real.exp (bounds.β * ‖terminalState drift diffusion T x₀ z‖) :=
    Real.exp_pos _
  calc
    |mixedDerivative (integrand drift diffusion payoff T x₀) support z| =
        normalizedMixedDerivativeAt drift diffusion payoff T bounds.β x₀ support z *
          Real.exp (bounds.β * ‖terminalState drift diffusion T x₀ z‖) := by
      unfold normalizedMixedDerivativeAt
      field_simp
    _ ≤ normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support *
          Real.exp (bounds.β * ‖terminalState drift diffusion T x₀ z‖) :=
      mul_le_mul_of_nonneg_right henvelope hexp.le

/-- The hybrid second moment of the actual mixed derivative of the Euler integrand. -/
def hybridDerivativeSecondMoment
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T : ℝ) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim)) (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Index J noiseDim → ℝ,
    ENNReal.ofReal
      (|mixedDerivative (integrand drift diffusion payoff T x₀) support
          (bridgeInput z)| ^ 2)
    ∂hybridProductMeasure support α

/-- The explicit constant from Equation (D.3) is nonnegative. -/
theorem auxiliaryMomentConstant_nonneg
    (β T K₀ L initialNorm Θ₁ : ℝ) :
    0 ≤ auxiliaryMomentConstant β T K₀ L initialNorm Θ₁ := by
  unfold auxiliaryMomentConstant
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le
      (zero_le_one.trans (one_le_hybridCoordinateMomentBound _ _)))
    (Real.rpow_nonneg (by norm_num) _)

/-- Lemmas 5.1 and 4.1's pointwise normalization imply the derivative second-moment bound
used in the proof of Lemma 5.2. -/
theorem hybridDerivativeSecondMoment_le
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖) :
    hybridDerivativeSecondMoment drift diffusion payoff T x₀ support
        (hybridAlpha bounds.β T bounds.driftLipschitzConstant
          (diffusionThetaOne diffusion)) ≤
      ENNReal.ofReal
          (normalizedDerivativeEnvelope
            drift diffusion payoff T bounds.β x₀ support ^ 2) *
        ENNReal.ofReal
          (auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
            ‖x₀‖ (diffusionThetaOne diffusion)) := by
  let D := normalizedDerivativeEnvelope
    drift diffusion payoff T bounds.β x₀ support
  let α₀ := hybridAlpha bounds.β T bounds.driftLipschitzConstant
    (diffusionThetaOne diffusion)
  have hD : 0 ≤ D := normalizedDerivativeEnvelope_nonneg
    drift diffusion payoff T bounds.β x₀ support
      (normalizedMixedDerivativeAt_bddAbove bounds hT x₀ support hsupport)
  have hmoment := hybridEulerTerminalMoment_le_auxiliaryMomentConstant
    drift diffusion x₀ support hT hK₀ bounds.driftLipschitzConstant_pos.le
      bounds.β_pos.le hdrift
  calc
    hybridDerivativeSecondMoment drift diffusion payoff T x₀ support α₀ ≤
        ∫⁻ z : Index J noiseDim → ℝ,
          ENNReal.ofReal
            (D ^ 2 * Real.exp
              (2 * bounds.β * ‖terminalState drift diffusion T x₀ (bridgeInput z)‖))
          ∂hybridProductMeasure support α₀ := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      have hpoint := abs_mixedDerivative_integrand_le_envelope_mul_exp
        (diffusion := diffusion) bounds hT x₀ support hsupport (bridgeInput z)
      have hright :
          0 ≤ D * Real.exp
            (bounds.β * ‖terminalState drift diffusion T x₀ (bridgeInput z)‖) :=
        mul_nonneg hD (Real.exp_pos _).le
      have hsquare :
          |mixedDerivative (integrand drift diffusion payoff T x₀) support
              (bridgeInput z)| ^ 2 ≤
            (D * Real.exp
              (bounds.β * ‖terminalState drift diffusion T x₀ (bridgeInput z)‖)) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) hpoint 2
      calc
        |mixedDerivative (integrand drift diffusion payoff T x₀) support
            (bridgeInput z)| ^ 2 ≤
            (D * Real.exp
              (bounds.β * ‖terminalState drift diffusion T x₀ (bridgeInput z)‖)) ^ 2 :=
          hsquare
        _ = D ^ 2 * Real.exp
            (2 * bounds.β * ‖terminalState drift diffusion T x₀ (bridgeInput z)‖) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          ring
    _ = ENNReal.ofReal (D ^ 2) *
        (∫⁻ z : Index J noiseDim → ℝ,
          ENNReal.ofReal (Real.exp
            (2 * bounds.β * ‖terminalState drift diffusion T x₀ (bridgeInput z)‖))
          ∂hybridProductMeasure support α₀) := by
      simp_rw [ENNReal.ofReal_mul (sq_nonneg D)]
      exact lintegral_const_mul' _ _ (by simp)
    _ ≤ ENNReal.ofReal (D ^ 2) *
        ENNReal.ofReal
          (auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
            ‖x₀‖ (diffusionThetaOne diffusion)) := by
      gcongr
      simpa [terminalState, α₀] using hmoment

/-- The actual mixed derivative belongs to `L²` under its hybrid product law. -/
theorem mixedDerivative_eulerIntegrand_memLp_two
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖) :
    MemLp (fun z : Index J noiseDim → ℝ =>
      mixedDerivative (integrand drift diffusion payoff T x₀) support
        (bridgeInput z)) 2
      (hybridProductMeasure support
        (hybridAlpha bounds.β T bounds.driftLipschitzConstant
          (diffusionThetaOne diffusion))) := by
  let α₀ := hybridAlpha bounds.β T bounds.driftLipschitzConstant
    (diffusionThetaOne diffusion)
  let f : (Index J noiseDim → ℝ) → ℝ := fun z =>
    mixedDerivative (integrand drift diffusion payoff T x₀) support (bridgeInput z)
  have hbridge : Continuous (bridgeInput :
      (Index J noiseDim → ℝ) → Input J noiseDim) := by
    unfold bridgeInput
    fun_prop
  have hf : Continuous f :=
    (continuous_mixedDerivative_eulerIntegrand
      (diffusion := diffusion) bounds x₀ support).comp hbridge
  have hmoment := hybridDerivativeSecondMoment_le
    bounds hT hK₀ x₀ support hsupport hdrift
  have hfinite :
      hybridDerivativeSecondMoment drift diffusion payoff T x₀ support α₀ <
        (⊤ : ℝ≥0∞) := by
    apply lt_of_le_of_lt hmoment
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  refine ⟨hf.pow 2 |>.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  change (∫⁻ z, ‖f z ^ 2‖ₑ
    ∂hybridProductMeasure support α₀) < (⊤ : ℝ≥0∞)
  calc
    (∫⁻ z, ‖f z ^ 2‖ₑ ∂hybridProductMeasure support α₀) =
        hybridDerivativeSecondMoment drift diffusion payoff T x₀ support α₀ := by
      apply lintegral_congr
      intro z
      rw [Real.enorm_eq_ofReal (sq_nonneg (f z))]
      simp only [f, sq_abs]
    _ < (⊤ : ℝ≥0∞) := hfinite

/-- The `L²` norm of the mixed derivative is bounded by `sqrt C_aux` times the normalized
derivative envelope. -/
theorem lpNorm_mixedDerivative_eulerIntegrand_le
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖) :
    lpNorm (fun z : Index J noiseDim → ℝ =>
        mixedDerivative (integrand drift diffusion payoff T x₀) support
          (bridgeInput z)) 2
        (hybridProductMeasure support
          (hybridAlpha bounds.β T bounds.driftLipschitzConstant
            (diffusionThetaOne diffusion))) ≤
      Real.sqrt
          (auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
            ‖x₀‖ (diffusionThetaOne diffusion)) *
        normalizedDerivativeEnvelope
          drift diffusion payoff T bounds.β x₀ support := by
  let α₀ := hybridAlpha bounds.β T bounds.driftLipschitzConstant
    (diffusionThetaOne diffusion)
  let μ := hybridProductMeasure support α₀
  let f : (Index J noiseDim → ℝ) → ℝ := fun z =>
    mixedDerivative (integrand drift diffusion payoff T x₀) support (bridgeInput z)
  let D := normalizedDerivativeEnvelope
    drift diffusion payoff T bounds.β x₀ support
  let C := auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
    ‖x₀‖ (diffusionThetaOne diffusion)
  have hf := mixedDerivative_eulerIntegrand_memLp_two
    bounds hT hK₀ x₀ support hsupport hdrift
  have hD : 0 ≤ D := normalizedDerivativeEnvelope_nonneg
    drift diffusion payoff T bounds.β x₀ support
      (normalizedMixedDerivativeAt_bddAbove
        (diffusion := diffusion) bounds hT x₀ support hsupport)
  have hC : 0 ≤ C := auxiliaryMomentConstant_nonneg _ _ _ _ _ _
  have hmoment := hybridDerivativeSecondMoment_le
    bounds hT hK₀ x₀ support hsupport hdrift
  have hsqIntegrable : Integrable (fun z => f z ^ 2) μ := by
    simpa [f, μ, α₀] using hf.integrable_sq
  have hENNIntegral :
      ENNReal.ofReal (∫ z, f z ^ 2 ∂μ) =
        hybridDerivativeSecondMoment drift diffusion payoff T x₀ support α₀ := by
    rw [ofReal_integral_eq_lintegral_ofReal hsqIntegrable
      (ae_of_all μ (fun z => sq_nonneg (f z)))]
    apply lintegral_congr
    intro z
    simp only [f, sq_abs]
  have hENN : ENNReal.ofReal (∫ z, f z ^ 2 ∂μ) ≤
      ENNReal.ofReal (D ^ 2 * C) := by
    rw [hENNIntegral]
    calc
      hybridDerivativeSecondMoment drift diffusion payoff T x₀ support α₀ ≤
          ENNReal.ofReal (D ^ 2) * ENNReal.ofReal C := by
        simpa [D, C, α₀] using hmoment
      _ = ENNReal.ofReal (D ^ 2 * C) :=
        (ENNReal.ofReal_mul (sq_nonneg D)).symm
  have hreal : (∫ z, f z ^ 2 ∂μ) ≤ D ^ 2 * C :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg D) hC)).mp hENN
  have hlp : lpNorm f 2 μ = Real.sqrt (∫ z, f z ^ 2 ∂μ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp)
      hf.aestronglyMeasurable]
    rw [Real.sqrt_eq_rpow]
    congr 1
    · apply integral_congr_ae
      filter_upwards with z
      simp [f, Real.norm_eq_abs, sq_abs]
    · norm_num
  rw [show (fun z : Index J noiseDim → ℝ =>
      mixedDerivative (integrand drift diffusion payoff T x₀) support
        (bridgeInput z)) = f from rfl]
  change lpNorm f 2 μ ≤ Real.sqrt C * D
  rw [hlp]
  calc
    Real.sqrt (∫ z, f z ^ 2 ∂μ) ≤ Real.sqrt (D ^ 2 * C) :=
      Real.sqrt_le_sqrt hreal
    _ = Real.sqrt C * D := by
      rw [mul_comm, Real.sqrt_mul hC, Real.sqrt_sq_eq_abs,
        abs_of_nonneg hD]

/-- Lemma 5.2 after its standard Jensen step has bounded `B_u(F_m)^2` by the hybrid
derivative second moment.  The conclusion uses exactly `sqrt C_aux`, as in the paper. -/
theorem lemma5_2_of_hybrid_jensen
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖)
    (B : ℝ) (hB : 0 ≤ B)
    (hJensen : ENNReal.ofReal (B ^ 2) ≤
      hybridDerivativeSecondMoment drift diffusion payoff T x₀ support
        (hybridAlpha bounds.β T bounds.driftLipschitzConstant
          (diffusionThetaOne diffusion))) :
    B ≤ Real.sqrt
        (auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
          ‖x₀‖ (diffusionThetaOne diffusion)) *
      normalizedDerivativeEnvelope
        drift diffusion payoff T bounds.β x₀ support := by
  let D := normalizedDerivativeEnvelope
    drift diffusion payoff T bounds.β x₀ support
  let C := auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
    ‖x₀‖ (diffusionThetaOne diffusion)
  have hD : 0 ≤ D := normalizedDerivativeEnvelope_nonneg
    drift diffusion payoff T bounds.β x₀ support
      (normalizedMixedDerivativeAt_bddAbove
        (diffusion := diffusion) bounds hT x₀ support hsupport)
  have hC : 0 ≤ C := auxiliaryMomentConstant_nonneg _ _ _ _ _ _
  have hmoment := hybridDerivativeSecondMoment_le
    bounds hT hK₀ x₀ support hsupport hdrift
  have hENN : ENNReal.ofReal (B ^ 2) ≤ ENNReal.ofReal (D ^ 2 * C) := by
    calc
      ENNReal.ofReal (B ^ 2) ≤
          hybridDerivativeSecondMoment drift diffusion payoff T x₀ support
            (hybridAlpha bounds.β T bounds.driftLipschitzConstant
              (diffusionThetaOne diffusion)) := hJensen
      _ ≤ ENNReal.ofReal (D ^ 2) * ENNReal.ofReal C := by
        simpa [D, C] using hmoment
      _ = ENNReal.ofReal (D ^ 2 * C) :=
        (ENNReal.ofReal_mul (sq_nonneg D)).symm
  have hsq : B ^ 2 ≤ D ^ 2 * C :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg D) hC)).mp hENN
  apply (sq_le_sq₀ hB (mul_nonneg (Real.sqrt_nonneg C) hD)).mp
  calc
    B ^ 2 ≤ D ^ 2 * C := hsq
    _ = (Real.sqrt C * D) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC]
      ring

end

end TimeDependentLattice.Sampling
