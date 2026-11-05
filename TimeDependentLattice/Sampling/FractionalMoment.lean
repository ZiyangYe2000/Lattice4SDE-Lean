/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.Optimization
import TimeDependentLattice.Sampling.RandomWCE

/-!
# The fractional-moment estimate for a random lattice rule

This file assembles paper Proposition 5.3.  The random worst-case-error estimate from the cited
QMC literature remains an explicit hypothesis.  The conditional Jensen step, the treatment of
zero subset weights, and the optimization of all nonempty subset weights are proved here.
-/

namespace TimeDependentLattice.Sampling

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section

theorem latticeFractionalSum_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ lam : ℝ} {B : Finset ι → ℝ}
    (hρ : 0 ≤ ρ) (hB : ∀ u, 0 ≤ B u) :
    0 ≤ latticeFractionalSum ρ lam B := by
  unfold latticeFractionalSum
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (Real.rpow_nonneg hρ _) (Real.rpow_nonneg (hB u) _)

private theorem optimized_ennreal_product_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ lam : ℝ} {B : Finset ι → ℝ} {denominator : ℝ≥0∞}
    (hρ : 0 ≤ ρ) (hlam : 0 < lam) (hB : ∀ u, 0 ≤ B u) :
    ENNReal.ofReal (latticeFractionalSum ρ lam B) ^ lam *
        (ENNReal.ofReal (latticeFractionalSum ρ lam B) / denominator) =
      ENNReal.ofReal (latticeMomentScale ρ lam B) / denominator := by
  let S := latticeFractionalSum ρ lam B
  have hS : 0 ≤ S := latticeFractionalSum_nonneg hρ hB
  by_cases hSzero : S = 0
  · simp [S, hSzero, latticeMomentScale, Real.zero_rpow (by linarith : 1 + lam ≠ 0)]
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSzero)
    have hofPos : 0 < ENNReal.ofReal S := ENNReal.ofReal_pos.mpr hSpos
    calc
      ENNReal.ofReal S ^ lam * (ENNReal.ofReal S / denominator) =
          (ENNReal.ofReal S ^ lam * ENNReal.ofReal S) / denominator :=
        (mul_div_assoc _ _ _).symm
      _ = (ENNReal.ofReal S ^ lam * ENNReal.ofReal S ^ (1 : ℝ)) / denominator := by
        rw [ENNReal.rpow_one]
      _ = ENNReal.ofReal S ^ (lam + 1) / denominator := by
        rw [ENNReal.rpow_add _ _ hofPos.ne' ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal S ^ (1 + lam) / denominator := by
        congr 2
        ring
      _ = ENNReal.ofReal (S ^ (1 + lam)) / denominator := by
        rw [ENNReal.ofReal_rpow_of_nonneg hS (by linarith)]
      _ = ENNReal.ofReal (latticeMomentScale ρ lam B) / denominator := by
        rfl

/-- Paper Proposition 5.3, with the cited random-wce theorem exposed as `hwce`.

The two finite sums in `hshift` and `hwce` use the auxiliary subset weights selected in (5.6).
The theorem proves that their product is exactly the optimized scale `C_lam(F)` from (5.4).
-/
theorem proposition5_3
    {ι Generator Shift : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Generator] [MeasurableSpace Shift]
    {μGenerator : Measure Generator} {μShift : Measure Shift}
    [IsProbabilityMeasure μGenerator] [IsProbabilityMeasure μShift]
    {error : Generator → Shift → ℝ} {wce : Generator → ℝ≥0∞}
    (herror : ∀ generator, Measurable (error generator))
    (hwceMeas : Measurable wce)
    {ρ lam : ℝ} (hρ : 0 < ρ) (hlamLower : 1 / 2 < lam)
    (hlamUpper : lam < 1) {B : Finset ι → ℝ} (hB : ∀ u, 0 ≤ B u)
    {denominator : ℝ≥0∞}
    (hshift : ∀ generator,
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 : ℝ) ∂μShift) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
              zeroDiv (B u ^ 2) (auxiliarySubsetWeight ρ lam B u)) *
          wce generator ^ (2 : ℝ))
    /- The cited random-wce moment estimate, specialized to the weights (5.6). -/
    (hwce : (∫⁻ generator, wce generator ^ (2 * lam) ∂μGenerator) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
            auxiliarySubsetWeight ρ lam B u ^ lam * ρ ^ u.card) /
        denominator) :
    (∫⁻ generator, ∫⁻ shift,
      ‖error generator shift‖ₑ ^ (2 * lam) ∂μShift ∂μGenerator) ≤
      ENNReal.ofReal (latticeMomentScale ρ lam B) / denominator := by
  have hlamPos : 0 < lam := by linarith
  have hraw := fractional_lattice_moment_from_randomWCE
    herror hwceMeas hlamPos hlamUpper.le hshift hwce
  rw [sum_zeroDiv_auxiliarySubsetWeight_eq_latticeFractionalSum
      hρ hlamPos hB,
    sum_auxiliarySubsetWeight_rpow_eq_latticeFractionalSum
      hρ hlamPos hB] at hraw
  exact hraw.trans_eq (optimized_ennreal_product_eq hρ.le hlamPos hB)

/-- Product-probability-space form of Proposition 5.3.  It lets the generating vector and shift
be treated as one random input when applying the `L^p` rate lemmas. -/
theorem proposition5_3_prod
    {ι Generator Shift : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Generator] [MeasurableSpace Shift]
    {μGenerator : Measure Generator} {μShift : Measure Shift}
    [IsProbabilityMeasure μGenerator] [IsProbabilityMeasure μShift]
    {error : Generator → Shift → ℝ} {wce : Generator → ℝ≥0∞}
    (herror : ∀ generator, Measurable (error generator))
    (herrorJoint : Measurable (Function.uncurry error))
    (hwceMeas : Measurable wce)
    {ρ lam : ℝ} (hρ : 0 < ρ) (hlamLower : 1 / 2 < lam)
    (hlamUpper : lam < 1) {B : Finset ι → ℝ} (hB : ∀ u, 0 ≤ B u)
    {denominator : ℝ≥0∞}
    (hshift : ∀ generator,
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 : ℝ) ∂μShift) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
              zeroDiv (B u ^ 2) (auxiliarySubsetWeight ρ lam B u)) *
          wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator, wce generator ^ (2 * lam) ∂μGenerator) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
            auxiliarySubsetWeight ρ lam B u ^ lam * ρ ^ u.card) /
        denominator) :
    (∫⁻ input : Generator × Shift,
      ‖Function.uncurry error input‖ₑ ^ (2 * lam)
        ∂μGenerator.prod μShift) ≤
      ENNReal.ofReal (latticeMomentScale ρ lam B) / denominator := by
  rw [lintegral_prod]
  · exact proposition5_3 herror hwceMeas hρ hlamLower hlamUpper hB hshift hwce
  · exact (ENNReal.continuous_rpow_const.measurable.comp herrorJoint.enorm).aemeasurable

end

end TimeDependentLattice.Sampling
