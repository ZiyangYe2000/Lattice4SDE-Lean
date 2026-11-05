/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Finite real sampling bounds

The real `L^q` conclusions in the paper follow from the extended-nonnegative integral bounds
once measurability and finiteness have been established.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open MeasureTheory
open scoped ENNReal

theorem memLp_of_eLpNorm'_le_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    {q C : ℝ} (hq : 0 < q) (hf : AEStronglyMeasurable f μ)
    (hbound : eLpNorm' f q μ ≤ ENNReal.ofReal C) :
    MemLp f (ENNReal.ofReal q) μ := by
  change eLpNorm f (ENNReal.ofReal q) μ < ∞
  rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le]
  exact hbound.trans_lt ENNReal.ofReal_lt_top

theorem lpNorm_le_of_eLpNorm'_le_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C) (hf : AEStronglyMeasurable f μ)
    (hbound : eLpNorm' f q μ ≤ ENNReal.ofReal C) :
    lpNorm f (ENNReal.ofReal q) μ ≤ C := by
  rw [lpNorm, eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le]
  simpa only [ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

/-- Rewrite the paper's sampling rate without an extended-real denominator. -/
theorem ennreal_sampling_rate_eq {C a : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hN : 0 < N) :
    ((2 * ENNReal.ofReal C) / (N : ℝ≥0∞)) ^ a =
      ENNReal.ofReal ((2 ^ a * C ^ a) * (N : ℝ) ^ (-a)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase : 2 * ENNReal.ofReal C / (N : ℝ≥0∞) =
      ENNReal.ofReal (2 * C / (N : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hNreal, ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [hbase, ENNReal.ofReal_rpow_of_nonneg (by positivity) ha]
  congr 1
  rw [Real.div_rpow (by positivity) hNreal.le, Real.mul_rpow (by norm_num) hC,
    Real.rpow_neg hNreal.le, div_eq_mul_inv]

end

end TimeDependentLattice.Sampling
