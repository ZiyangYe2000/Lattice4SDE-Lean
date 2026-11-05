/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib

/-!
# Fractional lattice moments from a random worst-case-error bound

This file proves the probability-space part of paper Proposition 5.3.  The only external input is
the displayed moment bound for the shift-averaged worst-case error (paper Lemma 2.5, specialized
from the cited QMC literature).
-/

namespace TimeDependentLattice.Sampling

open scoped ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section

/-- Conditional Jensen in the precise form used in Proposition 5.3.  It is derived from
monotonicity of `L^p` seminorms on a probability space. -/
theorem fractional_moment_le_second_moment_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {error : Ω → ℝ} (herror : Measurable error)
    {lam : ℝ} (hlamPos : 0 < lam) (hlamOne : lam ≤ 1) :
    (∫⁻ ω, ‖error ω‖ₑ ^ (2 * lam) ∂μ) ≤
      (∫⁻ ω, ‖error ω‖ₑ ^ (2 : ℝ) ∂μ) ^ lam := by
  have htwoLam : 0 < 2 * lam := mul_pos (by positivity) hlamPos
  have htwoLamLe : 2 * lam ≤ 2 := by nlinarith
  have hnorm : eLpNorm' error (2 * lam) μ ≤ eLpNorm' error 2 μ :=
    eLpNorm'_le_eLpNorm'_of_exponent_le htwoLam htwoLamLe μ
      herror.aestronglyMeasurable
  calc
    (∫⁻ ω, ‖error ω‖ₑ ^ (2 * lam) ∂μ) =
        eLpNorm' error (2 * lam) μ ^ (2 * lam) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' htwoLam
    _ ≤ eLpNorm' error 2 μ ^ (2 * lam) :=
      ENNReal.rpow_le_rpow hnorm htwoLam.le
    _ = (eLpNorm' error 2 μ ^ (2 : ℝ)) ^ lam :=
      ENNReal.rpow_mul _ _ _
    _ = (∫⁻ ω, ‖error ω‖ₑ ^ (2 : ℝ) ∂μ) ^ lam := by
      congr 1
      exact (lintegral_rpow_enorm_eq_rpow_eLpNorm'
        (μ := μ) (f := error) (by positivity : (0 : ℝ) < 2)).symm

/-- Paper Proposition 5.3 before the subset weights are optimized.

`hshift` is the defining worst-case-error estimate for each generating vector.  `hwce` is exactly
the external random-wce moment interface. -/
theorem fractional_lattice_moment_from_randomWCE
    {Generator Shift : Type*}
    [MeasurableSpace Generator] [MeasurableSpace Shift]
    {μGenerator : Measure Generator} {μShift : Measure Shift}
    [IsProbabilityMeasure μGenerator] [IsProbabilityMeasure μShift]
    {error : Generator → Shift → ℝ} {wce : Generator → ℝ≥0∞}
    (herror : ∀ generator, Measurable (error generator))
    (hwceMeas : Measurable wce)
    {lam : ℝ} (hlamPos : 0 < lam) (hlamOne : lam ≤ 1)
    {sobolevNormSq weightSum denominator : ℝ≥0∞}
    (hshift : ∀ generator,
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 : ℝ) ∂μShift) ≤
        sobolevNormSq * wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator, wce generator ^ (2 * lam) ∂μGenerator) ≤
      weightSum / denominator) :
    (∫⁻ generator, ∫⁻ shift,
      ‖error generator shift‖ₑ ^ (2 * lam) ∂μShift ∂μGenerator) ≤
      sobolevNormSq ^ lam * (weightSum / denominator) := by
  have hconditional (generator : Generator) :
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 * lam) ∂μShift) ≤
        sobolevNormSq ^ lam * wce generator ^ (2 * lam) := by
    calc
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 * lam) ∂μShift) ≤
          (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 : ℝ) ∂μShift) ^ lam :=
        fractional_moment_le_second_moment_rpow
          (herror generator) hlamPos hlamOne
      _ ≤ (sobolevNormSq * wce generator ^ (2 : ℝ)) ^ lam :=
        ENNReal.rpow_le_rpow (hshift generator) hlamPos.le
      _ = sobolevNormSq ^ lam * wce generator ^ (2 * lam) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hlamPos.le]
        congr 1
        exact (ENNReal.rpow_mul _ _ _).symm
  calc
    (∫⁻ generator, ∫⁻ shift,
        ‖error generator shift‖ₑ ^ (2 * lam) ∂μShift ∂μGenerator) ≤
      ∫⁻ generator,
        sobolevNormSq ^ lam * wce generator ^ (2 * lam) ∂μGenerator :=
      lintegral_mono hconditional
    _ = sobolevNormSq ^ lam *
        ∫⁻ generator, wce generator ^ (2 * lam) ∂μGenerator := by
      have hpowMeas : Measurable (fun generator ↦ wce generator ^ (2 * lam)) := by
        simpa [Function.comp_def] using
          (ENNReal.continuous_rpow_const.measurable.comp hwceMeas)
      exact lintegral_const_mul (sobolevNormSq ^ lam) hpowMeas
    _ ≤ sobolevNormSq ^ lam * (weightSum / denominator) := by
      gcongr

end

end TimeDependentLattice.Sampling
