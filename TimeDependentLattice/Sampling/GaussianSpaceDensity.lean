/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.HybridMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The density of the active Laplace product

The normalized active-coordinate product has density `alpha^n` times the unnormalized
weight in equation (5.1) of the paper. The integral identity below removes that normalization.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

/-- A finite product of integrable nonnegative densities has the product density. -/
theorem pi_withDensity_ofReal
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ j, Integrable (f j)) (hnonneg : ∀ j x, 0 ≤ f j x) :
    Measure.pi (fun j ↦ volume.withDensity (fun x ↦ ENNReal.ofReal (f j x))) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun z ↦ ENNReal.ofReal (∏ j, f j (z j))) := by
  classical
  have (j : ι) : IsFiniteMeasure (volume.withDensity (fun x ↦ ENNReal.ofReal (f j x))) :=
    isFiniteMeasure_withDensity (by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf j)
        (Filter.Eventually.of_forall (hnonneg j))]
      exact ENNReal.ofReal_ne_top)
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ z, ENNReal.ofReal (∏ j, f j (z j))
      ∂(Measure.pi (fun _ : ι ↦ volume)).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  have hprod : Integrable (fun z : ι → ℝ ↦ ∏ j, f j (z j))
      (Measure.pi (fun j ↦ volume.restrict (s j))) :=
    Integrable.fintype_prod (fun j ↦ (hf j).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun z ↦ Finset.prod_nonneg
      (fun j _ ↦ hnonneg j (z j))))]
  rw [integral_fintype_prod_eq_prod f]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ integral_nonneg
    (hnonneg j))]
  apply Finset.prod_congr rfl
  intro j hj
  rw [withDensity_apply _ (hs j)]
  exact ofReal_integral_eq_lintegral_ofReal (hf j).restrict
    (Filter.Eventually.of_forall (hnonneg j))

/-- Integration against finite density products is the paper's density-weighted integral. -/
theorem integral_pi_withDensity_ofReal
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ j, Integrable (f j)) (hm : ∀ j, Measurable (f j))
    (hnonneg : ∀ j x, 0 ≤ f j x) (g : (ι → ℝ) → ℝ) :
    (∫ z, g z ∂Measure.pi
      (fun j ↦ volume.withDensity (fun x ↦ ENNReal.ofReal (f j x)))) =
      ∫ z, g z * ∏ j, f j (z j) := by
  rw [pi_withDensity_ofReal f hf hnonneg]
  have hmprod : Measurable (fun z : ι → ℝ ↦ ∏ j, f j (z j)) :=
    Finset.measurable_prod _ (fun j _ ↦ (hm j).comp (measurable_pi_apply j))
  rw [integral_withDensity_eq_integral_toReal_smul hmprod.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have hprod : ∀ z : ι → ℝ, 0 ≤ ∏ j, f j (z j) :=
    fun z ↦ Finset.prod_nonneg (fun j _ ↦ hnonneg j (z j))
  simp_rw [ENNReal.toReal_ofReal (hprod _), smul_eq_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z ↦ mul_comm _ _)

/-- The product of normalized Laplace coordinates, written as a density relative to volume. -/
theorem laplaceProductMeasure_eq_withDensity
    {ι : Type*} [Fintype ι] {α : ℝ} (hα : 0 < α) :
    Measure.pi (fun _ : ι ↦ laplaceCoordinateMeasure α) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun z ↦ ENNReal.ofReal (∏ j, α * Real.exp (-2 * α * |z j|))) := by
  have hf : Integrable (fun x : ℝ ↦ α * Real.exp (-2 * α * |x|)) :=
    by simpa [neg_mul] using
      (integrable_exp_neg_mul_abs (by positivity : 0 < 2 * α)).const_mul α
  exact pi_withDensity_ofReal (fun _ x ↦ α * Real.exp (-2 * α * |x|))
    (fun _ ↦ hf) (fun _ _ ↦ mul_nonneg hα.le (Real.exp_pos _).le)

/-- Integrating against the normalized product exposes the factor `alpha^n`. -/
theorem integral_laplaceProductMeasure
    {ι : Type*} [Fintype ι] {α : ℝ} (hα : 0 < α) (g : (ι → ℝ) → ℝ) :
    (∫ z, g z ∂Measure.pi (fun _ : ι ↦ laplaceCoordinateMeasure α)) =
      α ^ Fintype.card ι *
        ∫ z, g z * ∏ j, Real.exp (-2 * α * |z j|) := by
  rw [laplaceProductMeasure_eq_withDensity hα]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have hnonneg : ∀ z : ι → ℝ, 0 ≤ ∏ j, α * Real.exp (-2 * α * |z j|) :=
    fun _ ↦ Finset.prod_nonneg (fun j _ ↦ mul_nonneg hα.le (Real.exp_pos _).le)
  simp_rw [ENNReal.toReal_ofReal (hnonneg _)]
  simp only [smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z ↦ mul_comm _ _)

/-- The inactive Gaussian product is exactly integration against the product standard density. -/
theorem integral_gaussianProductMeasure
    {ι : Type*} [Fintype ι] (g : (ι → ℝ) → ℝ) :
    (∫ z, g z ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) =
      ∫ z, g z * ∏ j, gaussianPDFReal 0 1 (z j) := by
  have hgauss : gaussianReal 0 1 =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num), gaussianPDF_def]
  rw [hgauss]
  exact integral_pi_withDensity_ofReal (ι := ι) (fun _ ↦ gaussianPDFReal 0 1)
    (fun _ ↦ integrable_gaussianPDFReal 0 1) (fun _ ↦ measurable_gaussianPDFReal 0 1)
    (fun _ ↦ gaussianPDFReal_nonneg 0 1) g

end

end TimeDependentLattice.Sampling
