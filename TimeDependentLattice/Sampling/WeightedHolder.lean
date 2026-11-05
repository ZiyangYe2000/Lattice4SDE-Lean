/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Finite weighted Hölder inequality

The proof of paper Lemma 5.1 uses generalized Hölder with a finite family of weights whose
sum is at most one.  Mathlib states the inequality when the exponents sum exactly to one.
This wrapper inserts the missing mass as the exponent of the constant function `1`.
-/

namespace TimeDependentLattice.Sampling

open scoped ENNReal BigOperators
open MeasureTheory

/-- Generalized Hölder on a probability space for nonnegative weights with total mass at
most one. -/
theorem lintegral_weightedProduct_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) {f : ι → Ω → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    (weight : ι → ℝ) (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hsum : ∑ i ∈ s, weight i ≤ 1) :
    (∫⁻ ω, ∏ i ∈ s, f i ω ^ weight i ∂μ) ≤
      ∏ i ∈ s, (∫⁻ ω, f i ω ∂μ) ^ weight i := by
  let slack := 1 - ∑ i ∈ s, weight i
  have hslack : 0 ≤ slack := sub_nonneg.mpr hsum
  have htotal : slack + ∑ i ∈ s, weight i = 1 := by
    dsimp [slack]
    ring
  have hholder := ENNReal.lintegral_mul_prod_norm_pow_le
    (μ := μ) s (g := fun _ : Ω => 1) (f := f)
    (by fun_prop) hf slack htotal hslack hweight
  simpa using hholder

/-- The form used in Lemma 5.1 after inserting a separate moment bound for every factor. -/
theorem lintegral_weightedProduct_le_of_momentBounds
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) {f : ι → Ω → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    (weight : ι → ℝ) (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hsum : ∑ i ∈ s, weight i ≤ 1) (momentBound : ι → ℝ≥0∞)
    (hmoment : ∀ i ∈ s, (∫⁻ ω, f i ω ∂μ) ≤ momentBound i) :
    (∫⁻ ω, ∏ i ∈ s, f i ω ^ weight i ∂μ) ≤
      ∏ i ∈ s, momentBound i ^ weight i := by
  refine (lintegral_weightedProduct_le s hf weight hweight hsum).trans ?_
  apply Finset.prod_le_prod
  intro i hi
  exact ENNReal.rpow_le_rpow (hmoment i hi) (hweight i hi)

/-- Exponentiating a weighted finite sum is the weighted product of the individual
exponentials, in `ℝ≥0∞`. -/
theorem ofReal_exp_weightedSum_eq_prod
    {ι : Type*} (s : Finset ι) (weight value : ι → ℝ) (lam : ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i) :
    ENNReal.ofReal (Real.exp (lam * ∑ i ∈ s, weight i * value i)) =
      ∏ i ∈ s,
        ENNReal.ofReal (Real.exp (lam * value i)) ^ weight i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      rw [mul_add, Real.exp_add]
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hexponent : lam * (weight i * value i) = (lam * value i) * weight i := by ring
      rw [hexponent]
      rw [Real.exp_mul]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (hweight i (Finset.mem_insert_self ..))]
      rw [ih (fun j hj => hweight j (Finset.mem_insert_of_mem hj))]

/-- A factorwise upper bound on the individual exponentials yields the corresponding
upper bound on the exponential of their weighted sum. -/
theorem ofReal_exp_weightedSum_le_prod
    {ι : Type*} (s : Finset ι) (weight value : ι → ℝ) (lam : ℝ)
    (factor : ι → ℝ≥0∞) (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hfactor : ∀ i ∈ s,
      ENNReal.ofReal (Real.exp (lam * value i)) ≤ factor i) :
    ENNReal.ofReal (Real.exp (lam * ∑ i ∈ s, weight i * value i)) ≤
      ∏ i ∈ s, factor i ^ weight i := by
  classical
  rw [ofReal_exp_weightedSum_eq_prod s weight value lam hweight]
  apply Finset.prod_le_prod
  intro i hi
  exact ENNReal.rpow_le_rpow (hfactor i hi) (hweight i hi)

/-- Algebraic collection of two common bases in a finite weighted product. -/
theorem prod_mul_rpow_weight_eq
    {ι : Type*} (s : Finset ι) (A B : ℝ≥0∞) (weight exponent : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤) (hB0 : B ≠ 0) (hBtop : B ≠ ⊤) :
    (∏ i ∈ s, (A * B ^ exponent i) ^ weight i) =
      A ^ (∑ i ∈ s, weight i) *
        B ^ (∑ i ∈ s, exponent i * weight i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (hweight i (Finset.mem_insert_self ..))]
      rw [← ENNReal.rpow_mul]
      rw [ih (fun j hj => hweight j (Finset.mem_insert_of_mem hj))]
      rw [ENNReal.rpow_add _ _ hA0 hAtop, ENNReal.rpow_add _ _ hB0 hBtop]
      ac_rfl

end TimeDependentLattice.Sampling
