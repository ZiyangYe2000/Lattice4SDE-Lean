/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.FractionalMoment
import TimeDependentLattice.Sampling.Median
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# From the fractional moment to the sampling rates

This file proves the last probabilistic and algebraic part of paper Theorem 3.1.  Starting from
the uniform `2 * lam` moment furnished by Proposition 5.3, it derives the single-rule `L^1` rate
and the `L^q` rate for an odd median of independent copies.
-/

namespace TimeDependentLattice.Sampling

open scoped ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section

/-- The choice `lam = 1 / (2(1-epsilon))` made in the proof of Theorem 3.1. -/
def samplingLambda (ε : ℝ) : ℝ :=
  1 / (2 * (1 - ε))

/-- The choice `r_* = 1 - epsilon / 2` in the proof of Theorem 3.1. -/
def samplingRStar (ε : ℝ) : ℝ :=
  1 - ε / 2

/-- The Gaussian coordinate constant `C_{α,r_*}` in equation (2.28). -/
def gaussianWCECoordinateConstant (α r : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi) * Real.exp (α ^ 2 / (1 - r))) /
    (Real.pi ^ (2 * r) * r * (1 - r))

/-- The paper's concrete `ρ_λ` from (2.28), with the choices of `λ` and `r_*`
made in the proof of Theorem 3.1. -/
def samplingRho (α ε : ℝ) : ℝ :=
  2 * gaussianWCECoordinateConstant α (samplingRStar ε) ^ samplingLambda ε *
    (riemannZeta
      (2 * samplingRStar ε * samplingLambda ε : ℝ)).re

theorem samplingLambda_mem_interval
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    1 / 2 < samplingLambda ε ∧ samplingLambda ε < 1 := by
  unfold samplingLambda
  have hden : 0 < 2 * (1 - ε) := by linarith
  constructor
  · apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden).2
    nlinarith
  · apply (div_lt_one hden).2
    linarith

theorem two_mul_samplingLambda (ε : ℝ) :
    2 * samplingLambda ε = 1 / (1 - ε) := by
  unfold samplingLambda
  field_simp

theorem one_div_two_mul_samplingLambda
    {ε : ℝ} (hεOne : ε < 1) :
    1 / (2 * samplingLambda ε) = 1 - ε := by
  unfold samplingLambda
  have hne : 1 - ε ≠ 0 := by linarith
  field_simp

theorem samplingRStar_mem_interval
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    1 / (2 * samplingLambda ε) < samplingRStar ε ∧ samplingRStar ε < 1 := by
  rw [one_div_two_mul_samplingLambda (by linarith)]
  unfold samplingRStar
  constructor <;> linarith

theorem one_lt_two_mul_samplingRStar_mul_samplingLambda
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    1 < 2 * samplingRStar ε * samplingLambda ε := by
  have hlam := (samplingLambda_mem_interval hεPos hεHalf).1
  have hr := (samplingRStar_mem_interval hεPos hεHalf).1
  have htwoLam : 0 < 2 * samplingLambda ε := by positivity
  rw [div_lt_iff₀ htwoLam] at hr
  nlinarith

theorem gaussianWCECoordinateConstant_pos
    {α r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < gaussianWCECoordinateConstant α r := by
  unfold gaussianWCECoordinateConstant
  positivity

theorem gaussianWCECoordinateConstant_mono_alpha
    {r α α' : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hα0 : 0 ≤ α) (hα : α ≤ α') :
    gaussianWCECoordinateConstant α r ≤
      gaussianWCECoordinateConstant α' r := by
  unfold gaussianWCECoordinateConstant
  have hsquare : α ^ 2 ≤ α' ^ 2 := by nlinarith
  have hden : 0 < 1 - r := by linarith
  have hexp : Real.exp (α ^ 2 / (1 - r)) ≤
      Real.exp (α' ^ 2 / (1 - r)) := by
    exact Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hden).2 hsquare)
  gcongr

theorem samplingRho_pos
    {α ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    0 < samplingRho α ε := by
  have hr := samplingRStar_mem_interval hεPos hεHalf
  have hlam := samplingLambda_mem_interval hεPos hεHalf
  have hr0 : 0 < samplingRStar ε := by
    have : 0 < 1 / (2 * samplingLambda ε) :=
      div_pos zero_lt_one (mul_pos (by norm_num) (by linarith [hlam.1]))
    linarith
  have hcoordinate :
      0 < gaussianWCECoordinateConstant α (samplingRStar ε) :=
    gaussianWCECoordinateConstant_pos (α := α) hr0 hr.2
  have hzeta : 0 < (riemannZeta
      (2 * samplingRStar ε * samplingLambda ε : ℝ)).re :=
    riemannZeta_re_pos_of_one_lt
      (one_lt_two_mul_samplingRStar_mul_samplingLambda hεPos hεHalf)
  unfold samplingRho
  exact mul_pos
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hcoordinate (samplingLambda ε)))
    hzeta

theorem samplingRho_mono_alpha
    {α α' ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    (hα0 : 0 ≤ α) (hα : α ≤ α') :
    samplingRho α ε ≤ samplingRho α' ε := by
  have hr := samplingRStar_mem_interval hεPos hεHalf
  have hlam := samplingLambda_mem_interval hεPos hεHalf
  have hr0 : 0 < samplingRStar ε := by
    have : 0 < 1 / (2 * samplingLambda ε) :=
      div_pos zero_lt_one (mul_pos (by norm_num) (by linarith [hlam.1]))
    linarith
  have hcoordinate := gaussianWCECoordinateConstant_mono_alpha
    hr0 hr.2 hα0 hα
  have hlam0 : 0 ≤ samplingLambda ε := by linarith [hlam.1]
  have hpow :
      gaussianWCECoordinateConstant α (samplingRStar ε) ^ samplingLambda ε ≤
        gaussianWCECoordinateConstant α' (samplingRStar ε) ^ samplingLambda ε :=
    Real.rpow_le_rpow
      (gaussianWCECoordinateConstant_pos (α := α) hr0 hr.2).le
      hcoordinate hlam0
  have hzeta : 0 ≤ (riemannZeta
      (2 * samplingRStar ε * samplingLambda ε : ℝ)).re :=
    (riemannZeta_re_pos_of_one_lt
      (one_lt_two_mul_samplingRStar_mul_samplingLambda hεPos hεHalf)).le
  unfold samplingRho
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by norm_num)) hzeta

theorem latticeDerivativeExponent_samplingLambda
    {ε : ℝ} (hεOne : ε < 1) :
    latticeDerivativeExponent (samplingLambda ε) = 2 / (3 - 2 * ε) := by
  unfold latticeDerivativeExponent samplingLambda
  have hne : 1 - ε ≠ 0 := by linarith
  field_simp
  ring

theorem one_le_two_mul_samplingLambda
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    1 ≤ 2 * samplingLambda ε := by
  rw [two_mul_samplingLambda]
  have hden : 0 < 1 - ε := by linarith
  exact (le_div_iff₀ hden).2 (by linarith)

/-- Probability-space `L^p` monotonicity in the exact form used for the single estimator. -/
theorem eLpNorm'_one_le_of_lintegral_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {error : Ω → ℝ} (herror : Measurable error)
    {η : ℝ} (hη : 1 ≤ η) {M : ℝ≥0∞}
    (hmoment : (∫⁻ ω, ‖error ω‖ₑ ^ η ∂μ) ≤ M) :
    eLpNorm' error 1 μ ≤ M ^ (1 / η) := by
  calc
    eLpNorm' error 1 μ ≤ eLpNorm' error η μ :=
      eLpNorm'_le_eLpNorm'_of_exponent_le zero_lt_one hη μ
        herror.aestronglyMeasurable
    _ = (∫⁻ ω, ‖error ω‖ₑ ^ η ∂μ) ^ (1 / η) :=
      eLpNorm'_eq_lintegral_enorm error η μ
    _ ≤ M ^ (1 / η) :=
      ENNReal.rpow_le_rpow hmoment (by positivity)

/-- The elementary `N - 1 ≥ N / 2` estimate in extended nonnegative reals. -/
theorem div_nat_sub_one_le
    (C : ℝ≥0∞) {N : ℕ} (hN : 2 ≤ N) :
    C / ((N - 1 : ℕ) : ℝ≥0∞) ≤ (2 * C) / (N : ℝ≥0∞) := by
  have hnat : N ≤ 2 * (N - 1) := by omega
  have hcast : (N : ℝ≥0∞) ≤ 2 * ((N - 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hnat
  have hhalf : (N : ℝ≥0∞) / 2 ≤ ((N - 1 : ℕ) : ℝ≥0∞) := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    simpa [mul_comm] using hcast
  have hinv0 : ((N - 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((N : ℝ≥0∞) / 2)⁻¹ :=
    (ENNReal.inv_le_inv).2 hhalf
  have hinv : ((N - 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ 2 * (N : ℝ≥0∞)⁻¹ := by
    calc
      ((N - 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((N : ℝ≥0∞) / 2)⁻¹ := hinv0
      _ = 2 * (N : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.inv_div (by simp) (by norm_num)]
        rw [ENNReal.div_eq_inv_mul]
        ac_rfl
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    C * ((N - 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ C * (2 * (N : ℝ≥0∞)⁻¹) := by
      gcongr
    _ = 2 * C * (N : ℝ≥0∞)⁻¹ := by ac_rfl

/-- The single-rule conclusion of Theorem 3.1 from its uniform fractional-moment estimate. -/
theorem single_l1_rate_of_fractional_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {error : Ω → ℝ} (herror : Measurable error)
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    {C : ℝ≥0∞} {N : ℕ} (hN : 2 ≤ N)
    (hmoment :
      (∫⁻ ω, ‖error ω‖ₑ ^ (2 * samplingLambda ε) ∂μ) ≤
        C / ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm' error 1 μ ≤ ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
  have hnorm := eLpNorm'_one_le_of_lintegral_rpow_le herror
    (one_le_two_mul_samplingLambda hεPos hεHalf) hmoment
  have hexp : 0 ≤ 1 / (2 * samplingLambda ε) := by
    rw [one_div_two_mul_samplingLambda (by linarith)]
    linarith
  calc
    eLpNorm' error 1 μ ≤
        (C / ((N - 1 : ℕ) : ℝ≥0∞)) ^
          (1 / (2 * samplingLambda ε)) := hnorm
    _ ≤ ((2 * C) / (N : ℝ≥0∞)) ^
          (1 / (2 * samplingLambda ε)) :=
      ENNReal.rpow_le_rpow (div_nat_sub_one_le C hN) hexp
    _ = ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
      rw [one_div_two_mul_samplingLambda (by linarith)]

/-- The odd-median conclusion of Theorem 3.1 from the same single-copy moment estimate. -/
theorem median_lq_rate_of_fractional_moment
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    {q : ℝ} (hq : 0 < q) (hk : 0 < k) (hqRange : q < k / (1 - ε))
    {C : ℝ≥0∞} {N : ℕ} (hN : 2 ≤ N)
    (hcopyMoment : ∀ i,
      (∫⁻ ω, ‖value i ω‖ₑ ^ (2 * samplingLambda ε) ∂μ) ≤
        C / ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm' median q μ ≤
      ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / q) *
        ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
  let η := 2 * samplingLambda ε
  let K := (C / ((N - 1 : ℕ) : ℝ≥0∞)) ^ (1 / η)
  have hηPos : 0 < η := by
    dsimp [η]
    have := (samplingLambda_mem_interval hεPos hεHalf).1
    positivity
  have hqη : q < η * k := by
    dsimp [η]
    rw [two_mul_samplingLambda]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hqRange
  have hcopyNorm : ∀ i, eLpNorm' (value i) η μ ≤ K := by
    intro i
    rw [eLpNorm'_eq_lintegral_enorm]
    exact ENNReal.rpow_le_rpow (hcopyMoment i) (by positivity)
  have hmedianBound := median_eLpNorm'_le
    hmedian hmeas hindep hk hq hqη hcopyNorm
  have hexp : 0 ≤ 1 / (2 * samplingLambda ε) := by
    rw [one_div_two_mul_samplingLambda (by linarith)]
    linarith
  have hK : K ≤ ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
    dsimp [K, η]
    calc
      (C / ((N - 1 : ℕ) : ℝ≥0∞)) ^
          (1 / (2 * samplingLambda ε)) ≤
          ((2 * C) / (N : ℝ≥0∞)) ^
            (1 / (2 * samplingLambda ε)) :=
        ENNReal.rpow_le_rpow (div_nat_sub_one_le C hN) hexp
      _ = ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
        rw [one_div_two_mul_samplingLambda (by linarith)]
  exact hmedianBound.trans (mul_le_mul_of_nonneg_left hK bot_le)

end

end TimeDependentLattice.Sampling
