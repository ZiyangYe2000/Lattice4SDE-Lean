/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.ErrorRecursion
import TimeDependentLattice.Bias.DiffusionBounds
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Standard stochastic inputs and their numerical consequences

The installed Mathlib provides the weak Doob maximal inequality, but not the strong `L²`
version. `FiniteDoobL2` states that standard theorem for every square-integrable martingale.
The model-specific second-moment and maximal bounds are proved below from the actual
Jacobian--diffusion integrand and the Itô isometry/orthogonality identity.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory Set TimeDependentLattice.Euler TimeDependentLattice.Trees

/-- The standard finite-time Doob `L²` theorem, independently of any Euler model. -/
def FiniteDoobL2 {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure Ω) : Prop :=
  ∀ (m : ℕ) (S : ℕ → Ω → E) (ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›),
    Martingale (fun j : Fin (m + 1) ↦ S j) ℱ μ →
    (∀ j ≤ m, MemLp (S j) 2 μ) → ∀ j ≤ m,
      lpNorm (gridMaxNorm S j) 2 μ ≤ 2 * lpNorm (S j) 2 μ

/-- Squaring the actual `L²` norm gives the second moment. -/
theorem lpNorm_two_sq_eq_integral {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have h := lpNorm_eq_integral_norm_rpow_toReal
    (f := f) (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hf.aestronglyMeasurable
  norm_num at h
  rw [h, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (integral_nonneg fun ω ↦ sq_nonneg _)

/-- The Brownian increment bound follows from its actual second-moment identity. -/
theorem lpNorm_increment_le_of_isometry {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E}
    {sigma δ : ℝ} (hf : MemLp f 2 μ) (hsigma : 0 ≤ sigma) (hδ : 0 ≤ δ)
    (hisometry : (∫ ω, ‖f ω‖ ^ 2 ∂μ) = sigma ^ 2 * δ) :
    lpNorm f 2 μ ≤ sigma * Real.sqrt δ := by
  have hnorm := lpNorm_two_sq_eq_integral hf
  rw [hisometry] at hnorm
  have hsqrt := Real.sq_sqrt hδ
  have hright : (sigma * Real.sqrt δ) ^ 2 = sigma ^ 2 * δ := by
    rw [mul_pow, hsqrt]
  exact (sq_le_sq₀ lpNorm_nonneg (mul_nonneg hsigma (Real.sqrt_nonneg δ))).1
    (by rw [hnorm, hright])

/-- Exact integration of the stochastic-Fubini weight. -/
theorem integral_square_terminal_weight (t h : ℝ) :
    (∫ s in t..t + h, (t + h - s) ^ 2) = h ^ 3 / 3 := by
  rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ s ^ 2) (t + h)]
  simp only [sub_self, add_sub_cancel_left]
  rw [integral_pow]
  norm_num

/-- Sum of the stochastic-Fubini variance envelopes. The numerical factor `1/3` is
derived by integrating the square of the actual time weight. -/
theorem sum_weighted_variances_le
    {m j : ℕ} {T h C : ℝ} (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hmh : (m : ℝ) * h = T) (hj : j ≤ m) (grid : ℕ → ℝ) (V : ℕ → ℝ → ℝ)
    (hVint : ∀ i < m, IntervalIntegrable
      (fun s ↦ (grid i + h - s) ^ 2 * V i s) volume (grid i) (grid i + h))
    (hV : ∀ i < m, ∀ s ∈ Icc (grid i) (grid i + h), V i s ≤ C) :
    (∑ i ∈ Finset.range j,
      ∫ s in grid i..grid i + h, (grid i + h - s) ^ 2 * V i s) ≤
      C * T / 3 * h ^ 2 := by
  have hlocal (i : ℕ) (hi : i < m) :
      (∫ s in grid i..grid i + h, (grid i + h - s) ^ 2 * V i s) ≤ C * h ^ 3 / 3 := by
    have henv : IntervalIntegrable (fun s : ℝ ↦ (grid i + h - s) ^ 2 * C)
        volume (grid i) (grid i + h) := by
      apply Continuous.intervalIntegrable
      fun_prop
    calc
      (∫ s in grid i..grid i + h, (grid i + h - s) ^ 2 * V i s) ≤
          ∫ s in grid i..grid i + h, (grid i + h - s) ^ 2 * C :=
        intervalIntegral.integral_mono_on (by linarith) (hVint i hi) henv
          (fun s hs ↦ mul_le_mul_of_nonneg_left (hV i hi s hs) (sq_nonneg _))
      _ = C * h ^ 3 / 3 := by
        rw [intervalIntegral.integral_mul_const, integral_square_terminal_weight]
        ring
  calc
    (∑ i ∈ Finset.range j,
        ∫ s in grid i..grid i + h, (grid i + h - s) ^ 2 * V i s) ≤
        ∑ _i ∈ Finset.range j, C * h ^ 3 / 3 := by
      exact Finset.sum_le_sum fun i hi ↦ hlocal i ((Finset.mem_range.mp hi).trans_le hj)
    _ = (j : ℝ) * (C * h ^ 3 / 3) := by simp
    _ ≤ (m : ℝ) * (C * h ^ 3 / 3) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hj)
      positivity
    _ = C * T / 3 * h ^ 2 := by rw [← hmh]; ring

/-- The actual squared Hilbert--Schmidt integrand, averaged over the probability space. -/
def driftDiffusionSecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (t : ℝ) (X : Ω → State stateDim) : ℝ :=
  ∫ ω, diffusionHilbertSchmidt ((fderiv ℝ (drift t) (X ω)).comp diffusion) ^ 2 ∂μ

/-- Equation (E.12) controls the expectation in the actual Itô isometry integrand. -/
theorem driftDiffusionSecondMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T t : ℝ}
    (bounds : GevreyBounds drift payoff T) (diffusion : Diffusion stateDim noiseDim)
    (ht₀ : 0 ≤ t) (htT : t ≤ T) (X : Ω → State stateDim) :
    driftDiffusionSecondMoment μ drift diffusion t X ≤
      bounds.driftLipschitzConstant ^ 2 * diffusionHilbertSchmidt diffusion ^ 2 := by
  unfold driftDiffusionSecondMoment
  calc
    (∫ ω, diffusionHilbertSchmidt ((fderiv ℝ (drift t) (X ω)).comp diffusion) ^ 2 ∂μ) ≤
        ∫ _ω, bounds.driftLipschitzConstant ^ 2 * diffusionHilbertSchmidt diffusion ^ 2 ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun ω ↦
          drift_diffusion_hilbertSchmidt_sq_le bounds diffusion ht₀ htT (X ω))
    _ = _ := by simp

/-- The last numerical step of (E.15), after the standard Doob theorem and the variance
estimate. Its hypotheses do not contain the desired maximal Euler bound. -/
theorem maximal_le_of_second_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} (doob : FiniteDoobL2 (E := E) μ)
    (S : ℕ → Ω → E) {m j : ℕ} (ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›)
    (hM : Martingale (fun k : Fin (m + 1) ↦ S k) ℱ μ)
    (hmem : ∀ k ≤ m, MemLp (S k) 2 μ) (hj : j ≤ m)
    {L sigma T h : ℝ} (hL : 0 ≤ L) (hsigma : 0 ≤ sigma) (hT : 0 ≤ T) (hh : 0 ≤ h)
    (hvariance : (∫ ω, ‖S j ω‖ ^ 2 ∂μ) ≤ L ^ 2 * sigma ^ 2 * T / 3 * h ^ 2) :
    lpNorm (gridMaxNorm S j) 2 μ ≤ 2 * L * sigma * Real.sqrt (T / 3) * h := by
  have hnorm := lpNorm_two_sq_eq_integral (hmem j hj)
  have hsqrt := Real.sq_sqrt (show 0 ≤ T / 3 by positivity)
  have hnonneg := Real.sqrt_nonneg (T / 3)
  have hterminal : lpNorm (S j) 2 μ ≤ L * sigma * Real.sqrt (T / 3) * h := by
    have hright : (L * sigma * Real.sqrt (T / 3) * h) ^ 2 =
        L ^ 2 * sigma ^ 2 * T / 3 * h ^ 2 := by
      simp only [mul_pow]
      rw [hsqrt]
      ring
    exact (sq_le_sq₀ lpNorm_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hL hsigma) hnonneg) hh)).1
      (by rw [hright, hnorm]; exact hvariance)
  exact (doob m S ℱ hM hmem j hj).trans (by nlinarith)

end

end TimeDependentLattice.Bias
