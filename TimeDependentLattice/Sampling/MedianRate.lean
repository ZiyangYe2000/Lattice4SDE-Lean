/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.Rate
import TimeDependentLattice.Sampling.MedianTail

/-!
# Median sampling rate with the paper's constant

This module specializes the layer-cake estimate in Lemma 5.4 of the paper to the single-copy
fractional moment used in Theorem 3.1. The multiplier is exactly equation (5.11).
-/

namespace TimeDependentLattice.Sampling

open scoped ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section

/-- The paper's median sampling rate, retaining the exact multiplier in equation (5.11). -/
theorem median_lq_rate_of_fractional_moment_paper
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hcard : Fintype.card ι = 2 * k - 1)
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    {q : ℝ} (hq : 0 < q) (hk : 0 < k) (hqRange : q < k / (1 - ε))
    {C : ℝ≥0∞} {N : ℕ} (hN : 2 ≤ N)
    (hcopyMoment : ∀ i,
      (∫⁻ ω, ‖value i ω‖ₑ ^ (2 * samplingLambda ε) ∂μ) ≤
        C / ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm' median q μ ≤
      medianPaperPrefactor (Fintype.card ι) k (2 * samplingLambda ε) q *
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
  have hmedianBound := median_eLpNorm'_le_paper
    hcard hmedian hmeas hindep hk hq hqη hcopyNorm
  have hexp : 0 ≤ 1 / (2 * samplingLambda ε) := by
    rw [one_div_two_mul_samplingLambda (by linarith)]
    linarith
  have hK : K ≤ ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
    dsimp [K, η]
    calc
      (C / ((N - 1 : ℕ) : ℝ≥0∞)) ^ (1 / (2 * samplingLambda ε)) ≤
          ((2 * C) / (N : ℝ≥0∞)) ^ (1 / (2 * samplingLambda ε)) :=
        ENNReal.rpow_le_rpow (div_nat_sub_one_le C hN) hexp
      _ = ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
        rw [one_div_two_mul_samplingLambda (by linarith)]
  exact hmedianBound.trans (mul_le_mul_of_nonneg_left hK bot_le)

end

end TimeDependentLattice.Sampling
