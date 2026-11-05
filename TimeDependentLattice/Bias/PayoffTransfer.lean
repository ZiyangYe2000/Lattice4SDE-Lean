/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.Constants
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Payoff transfer from the first derivative and exponential moments

The pointwise estimate preceding (E.7) in the paper follows from the first payoff derivative bound.
The integral estimate then follows by Cauchy--Schwarz.  The exponential state moment estimate
remains an explicit stochastic input; the payoff transfer itself is proved here.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open MeasureTheory
open TimeDependentLattice.Euler TimeDependentLattice.Trees

/-- The first payoff derivative bound gives the endpoint-exponential Lipschitz estimate used
immediately before (E.7) in the paper. -/
theorem payoff_sub_le_endpoint_exponentials
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x y : State stateDim) :
    |payoff y - payoff x| ≤ bounds.G₀ * bounds.G₁ * ‖y - x‖ *
      (Real.exp (bounds.β * ‖x‖) + Real.exp (bounds.β * ‖y‖)) := by
  let R := max ‖x‖ ‖y‖
  let C := bounds.G₀ * bounds.G₁ *
    (Real.exp (bounds.β * ‖x‖) + Real.exp (bounds.β * ‖y‖))
  have hderiv : ∀ z ∈ Metric.closedBall (0 : State stateDim) R,
      ‖fderiv ℝ payoff z‖ ≤ C := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have he : Real.exp (bounds.β * ‖z‖) ≤
        Real.exp (bounds.β * ‖x‖) + Real.exp (bounds.β * ‖y‖) := by
      have hmax : Real.exp (bounds.β * R) ≤
          Real.exp (bounds.β * ‖x‖) + Real.exp (bounds.β * ‖y‖) := by
        rcases le_total ‖x‖ ‖y‖ with h | h
        · simp only [R, max_eq_right h]
          linarith [Real.exp_pos (bounds.β * ‖x‖)]
        · simp only [R, max_eq_left h]
          linarith [Real.exp_pos (bounds.β * ‖y‖)]
      exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzR bounds.β_pos.le)).trans hmax
    have hd := bounds.payoff_derivative_norm 1 (by omega) z
    rw [norm_iteratedFDeriv_one] at hd
    have hd' : ‖fderiv ℝ payoff z‖ ≤
        bounds.G₀ * bounds.G₁ * Real.exp (bounds.β * ‖z‖) := by
      simpa using hd
    exact hd'.trans (mul_le_mul_of_nonneg_left he
      (mul_nonneg bounds.G₀_pos.le bounds.G₁_pos.le))
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le
    (x := x) (y := y)
    (fun z _ ↦ bounds.payoff_smooth.differentiable (by simp) z) hderiv
    (convex_closedBall (0 : State stateDim) R)
    (by simpa only [Metric.mem_closedBall, dist_zero_right, R] using le_max_left ‖x‖ ‖y‖)
    (by simpa only [Metric.mem_closedBall, dist_zero_right, R] using le_max_right ‖x‖ ‖y‖)
  change |payoff y - payoff x| ≤ C * ‖y - x‖ at hmean
  calc
    |payoff y - payoff x| ≤ C * ‖y - x‖ := hmean
    _ = _ := by dsimp [C]; ring

/-- The real `L²` norm written as the square root of the ordinary second moment. -/
theorem lpNorm_two_eq_sqrt_integral_norm_sq
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {f : Ω → E} (hf : AEStronglyMeasurable f μ) :
    lpNorm f 2 μ = Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp) hf,
    Real.sqrt_eq_rpow]
  congr 1
  · apply integral_congr_ae
    filter_upwards with ω
    norm_num
  · norm_num

private theorem integral_mul_le_lpNorm_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω * g ω ∂μ) ≤ lpNorm f 2 μ * lpNorm g 2 μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hf) (by simpa using hg)
  rw [lpNorm_two_eq_sqrt_integral_norm_sq hf.aestronglyMeasurable,
    lpNorm_two_eq_sqrt_integral_norm_sq hg.aestronglyMeasurable]
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs] using h

private theorem memLp_exp_norm_of_integrable_double
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Ω → E} {β : ℝ}
    (hX : AEStronglyMeasurable X μ)
    (hExp : Integrable (fun ω ↦ Real.exp (2 * β * ‖X ω‖)) μ) :
    MemLp (fun ω ↦ Real.exp (β * ‖X ω‖)) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω ↦ Real.exp (β * ‖X ω‖)) μ :=
    (hX.norm.aemeasurable.const_mul β).exp.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  convert hExp using 1
  ext ω
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The payoff is integrable under the standard second-moment and exponential-moment inputs.
No additional payoff growth assumption is needed. -/
theorem payoff_integrable_of_second_and_exponential_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) {X : Ω → State stateDim}
    (hX : MemLp X 2 μ)
    (hExp : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖X ω‖)) μ) :
    Integrable (fun ω ↦ payoff (X ω)) μ := by
  have hE := memLp_exp_norm_of_integrable_double hX.aestronglyMeasurable hExp
  have hOne : MemLp (fun _ : Ω ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hproduct := hX.norm.integrable_mul (hOne.add hE)
  have hmajorant : Integrable (fun ω ↦ |payoff 0| +
      (bounds.G₀ * bounds.G₁) * (‖X ω‖ * (1 + Real.exp (bounds.β * ‖X ω‖)))) μ :=
    (integrable_const _).add (hproduct.const_mul _)
  apply hmajorant.mono'
    (bounds.payoff_smooth.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  have hp := payoff_sub_le_endpoint_exponentials bounds 0 (X ω)
  simp only [sub_zero, norm_zero, mul_zero, Real.exp_zero] at hp
  have htriangle : |payoff (X ω)| ≤ |payoff (X ω) - payoff 0| + |payoff 0| := by
    simpa only [sub_add_cancel, Real.norm_eq_abs] using
      norm_add_le (payoff (X ω) - payoff 0) (payoff 0)
  simpa only [Real.norm_eq_abs] using htriangle.trans (by nlinarith [hp])

/-- Cauchy--Schwarz gives the payoff bias for two actual random state vectors from a bound on
their joint exponential moments.  The stochastic state-moment estimate is an explicit input. -/
theorem payoff_integral_sub_le_of_exponential_sum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) {X Y : Ω → State stateDim}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hExpX : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖X ω‖)) μ)
    (hExpY : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖Y ω‖)) μ)
    {M : ℝ}
    (hMoment : (∫ ω, Real.exp (2 * bounds.β * ‖X ω‖) ∂μ) +
      (∫ ω, Real.exp (2 * bounds.β * ‖Y ω‖) ∂μ) ≤ M) :
    |(∫ ω, payoff (Y ω) ∂μ) - ∫ ω, payoff (X ω) ∂μ| ≤
      bounds.G₀ * bounds.G₁ * Real.sqrt (2 * M) *
        lpNorm (fun ω ↦ Y ω - X ω) 2 μ := by
  let E : Ω → ℝ := fun ω ↦
    Real.exp (bounds.β * ‖X ω‖) + Real.exp (bounds.β * ‖Y ω‖)
  let D : Ω → ℝ := fun ω ↦ ‖Y ω - X ω‖
  have hExpX2 := memLp_exp_norm_of_integrable_double hX.aestronglyMeasurable hExpX
  have hExpY2 := memLp_exp_norm_of_integrable_double hY.aestronglyMeasurable hExpY
  have hE : MemLp E 2 μ := hExpX2.add hExpY2
  have hD : MemLp D 2 μ := (hY.sub hX).norm
  have hE0 : ∀ ω, 0 ≤ E ω := fun ω ↦
    add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hEsq : (∫ ω, E ω ^ 2 ∂μ) ≤ 2 * M := by
    calc
      (∫ ω, E ω ^ 2 ∂μ) ≤
          ∫ ω, 2 * (Real.exp (2 * bounds.β * ‖X ω‖) +
            Real.exp (2 * bounds.β * ‖Y ω‖)) ∂μ := by
        apply integral_mono hE.integrable_sq ((hExpX.add hExpY).const_mul 2)
        intro ω
        have hsqX : (Real.exp (bounds.β * ‖X ω‖)) ^ 2 =
            Real.exp (2 * bounds.β * ‖X ω‖) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        have hsqY : (Real.exp (bounds.β * ‖Y ω‖)) ^ 2 =
            Real.exp (2 * bounds.β * ‖Y ω‖) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        dsimp [E]
        nlinarith [sq_nonneg (Real.exp (bounds.β * ‖X ω‖) -
          Real.exp (bounds.β * ‖Y ω‖))]
      _ = 2 * ((∫ ω, Real.exp (2 * bounds.β * ‖X ω‖) ∂μ) +
          ∫ ω, Real.exp (2 * bounds.β * ‖Y ω‖) ∂μ) := by
        rw [integral_const_mul, integral_add hExpX hExpY]
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hMoment (by norm_num)
  have hElp : lpNorm E 2 μ ≤ Real.sqrt (2 * M) := by
    rw [lpNorm_two_eq_sqrt_integral_norm_sq hE.aestronglyMeasurable]
    simp only [Real.norm_eq_abs, sq_abs]
    exact Real.sqrt_le_sqrt hEsq
  have hpayX := payoff_integrable_of_second_and_exponential_moments bounds hX hExpX
  have hpayY := payoff_integrable_of_second_and_exponential_moments bounds hY hExpY
  have hProd : Integrable (fun ω ↦ bounds.G₀ * bounds.G₁ * (D ω * E ω)) μ :=
    (hD.integrable_mul hE).const_mul _
  have hCS := integral_mul_le_lpNorm_two hD hE (fun ω ↦ norm_nonneg _) hE0
  have hDnorm : lpNorm D 2 μ = lpNorm (fun ω ↦ Y ω - X ω) 2 μ :=
    lpNorm_norm (hY.sub hX).aestronglyMeasurable 2
  calc
    |(∫ ω, payoff (Y ω) ∂μ) - ∫ ω, payoff (X ω) ∂μ| =
        |∫ ω, payoff (Y ω) - payoff (X ω) ∂μ| := by
      rw [integral_sub hpayY hpayX]
    _ ≤ ∫ ω, |payoff (Y ω) - payoff (X ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, bounds.G₀ * bounds.G₁ * (D ω * E ω) ∂μ := by
      apply integral_mono (hpayY.sub hpayX).abs hProd
      intro ω
      simpa only [D, E, mul_assoc, Pi.sub_apply] using
        payoff_sub_le_endpoint_exponentials bounds (X ω) (Y ω)
    _ = (bounds.G₀ * bounds.G₁) * (∫ ω, D ω * E ω ∂μ) := integral_const_mul _ _
    _ ≤ (bounds.G₀ * bounds.G₁) * (lpNorm D 2 μ * lpNorm E 2 μ) :=
      mul_le_mul_of_nonneg_left hCS (mul_nonneg bounds.G₀_pos.le bounds.G₁_pos.le)
    _ ≤ (bounds.G₀ * bounds.G₁) *
        (lpNorm D 2 μ * Real.sqrt (2 * M)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hElp lpNorm_nonneg)
        (mul_nonneg bounds.G₀_pos.le bounds.G₁_pos.le)
    _ = _ := by rw [hDnorm]; ring

/-- Equation (E.7) of the paper, with exactly the paper's `C_pay`.  The input `hMoment` is the
terminal-time consequence of the joint exponential-moment estimate (E.5), evaluated at
`v = 2 beta`.
The only other inputs are the ordinary second moments and integrability of the two exponentials.
In particular, no payoff-difference estimate is assumed. -/
theorem payoff_integral_sub_le_payoffDifferenceConstant
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 initialNorm sigmaHS : ℝ}
    (bounds : GevreyBounds drift payoff T) {X Y : Ω → State stateDim}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hExpX : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖X ω‖)) μ)
    (hExpY : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖Y ω‖)) μ)
    (hMoment : (∫ ω, Real.exp (2 * bounds.β * ‖X ω‖) ∂μ) +
      (∫ ω, Real.exp (2 * bounds.β * ‖Y ω‖) ∂μ) ≤
        stateExponentialPrefactor (2 * bounds.β) T K0
          bounds.driftLipschitzConstant sigmaHS *
            Real.exp (2 * bounds.β * Real.exp (bounds.driftLipschitzConstant * T) *
              initialNorm)) :
    |(∫ ω, payoff (Y ω) ∂μ) - ∫ ω, payoff (X ω) ∂μ| ≤
      payoffDifferenceConstant bounds.G₀ bounds.G₁ bounds.β T K0
        bounds.driftLipschitzConstant initialNorm sigmaHS *
          lpNorm (fun ω ↦ Y ω - X ω) 2 μ := by
  have h := payoff_integral_sub_le_of_exponential_sum bounds hX hY hExpX hExpY hMoment
  have hC : bounds.G₀ * bounds.G₁ * Real.sqrt
      (2 * (stateExponentialPrefactor (2 * bounds.β) T K0
        bounds.driftLipschitzConstant sigmaHS *
          Real.exp (2 * bounds.β * Real.exp (bounds.driftLipschitzConstant * T) *
            initialNorm))) =
      payoffDifferenceConstant bounds.G₀ bounds.G₁ bounds.β T K0
        bounds.driftLipschitzConstant initialNorm sigmaHS := by
    unfold payoffDifferenceConstant
    rw [← mul_assoc 2, Real.sqrt_mul
      (mul_nonneg (by norm_num) (stateExponentialPrefactor_pos _ _ _ _ _).le),
      ← Real.exp_half]
    have hexponent :
        (2 * bounds.β * Real.exp (bounds.driftLipschitzConstant * T) * initialNorm) / 2 =
        bounds.β * Real.exp (bounds.driftLipschitzConstant * T) * initialNorm := by ring
    rw [hexponent]
    ring
  rwa [hC] at h

end

end TimeDependentLattice.Bias
