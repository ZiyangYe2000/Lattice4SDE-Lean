/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.MeasureTheory.Integral.Prod
import TimeDependentLattice.Sampling.GaussianSpaceNorm

/-!
# The iterated-integral form of the Gaussian-space component

The finite-coordinate product law splits into its active Laplace and inactive Gaussian factors.
Fubini's theorem and uniqueness of conditional expectation then identify the conditional
expectation in `gaussianSpaceComponent` with the inner integral in equation (5.1) of the paper.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped ENNReal
open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinates in `support` and its complement, represented by the standard measurable
product equivalence. -/
def splitActiveInactive (support : Finset ι) :
    (ι → ℝ) ≃ᵐ (↥support → ℝ) × ({j // j ∉ support} → ℝ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι ↦ ℝ) (· ∈ support)

/-- The normalized product Laplace law of the active coordinates. -/
def activeLaplaceMeasure (support : Finset ι) (α : ℝ) : Measure (↥support → ℝ) :=
  Measure.pi fun _ ↦ laplaceCoordinateMeasure α

/-- The standard Gaussian product law of the inactive coordinates. -/
def inactiveGaussianMeasure (support : Finset ι) :
    Measure ({j // j ∉ support} → ℝ) :=
  Measure.pi fun _ ↦ gaussianReal 0 1

instance inactiveGaussianMeasure_isProbability (support : Finset ι) :
    IsProbabilityMeasure (inactiveGaussianMeasure support) := by
  unfold inactiveGaussianMeasure
  infer_instance

omit [Fintype ι] [DecidableEq ι] in
theorem activeLaplaceMeasure_isProbability (support : Finset ι) {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (activeLaplaceMeasure support α) := by
  have := laplaceCoordinateMeasure_isProbability hα
  unfold activeLaplaceMeasure
  infer_instance

theorem splitActiveInactive_measurePreserving (support : Finset ι) {α : ℝ}
    (hα : 0 < α) :
    MeasurePreserving (splitActiveInactive support) (hybridProductMeasure support α)
      ((activeLaplaceMeasure support α).prod (inactiveGaussianMeasure support)) := by
  have (j : ι) : IsProbabilityMeasure (hybridCoordinateMeasure support α j) :=
    hybridCoordinateMeasure_isProbability support hα j
  have hactive : (@Measure.pi {j // j ∈ support} (fun _ ↦ ℝ)
      (Subtype.fintype (· ∈ support)) (fun _ ↦ inferInstance)
      (fun j ↦ hybridCoordinateMeasure support α j.1)) = activeLaplaceMeasure support α := by
    congr 1
    · exact Subsingleton.elim _ _
    · funext j
      simp [hybridCoordinateMeasure, j.2]
  have hinactive : (Measure.pi fun j : {j // j ∉ support} ↦
      hybridCoordinateMeasure support α j.1) = inactiveGaussianMeasure support := by
    congr 1
    funext j
    simp [hybridCoordinateMeasure, j.2]
  simpa only [splitActiveInactive, hybridProductMeasure, hactive, hinactive] using
    measurePreserving_piEquivPiSubtypeProd (hybridCoordinateMeasure support α) (· ∈ support)

/-- The Gaussian inner integral in equation (5.1) of the paper. The complement coordinates are
integrated against their standard Gaussian law; the active coordinates remain free. -/
def inactiveGaussianIntegral (support : Finset ι) (f : (ι → ℝ) → ℝ)
    (a : ↥support → ℝ) : ℝ :=
  ∫ b, f ((splitActiveInactive support).symm (a, b)) ∂inactiveGaussianMeasure support

private theorem inactiveGaussianIntegral_ae_eq_condExp_of_measurable
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hfint : Integrable f (hybridProductMeasure support α)) :
    (fun z ↦ inactiveGaussianIntegral support f (fun j ↦ z j.1)) =ᵐ[
      hybridProductMeasure support α]
      (hybridProductMeasure support α)[f | activeCoordinateMeasurableSpace support] := by
  let e := splitActiveInactive support
  let μ := hybridProductMeasure support α
  let μa := activeLaplaceMeasure support α
  let μb := inactiveGaussianMeasure support
  let F := fun ab ↦ f (e.symm ab)
  let G := inactiveGaussianIntegral support f
  have : IsProbabilityMeasure μ := hybridProductMeasure_isProbability support hα
  have : IsProbabilityMeasure μa := activeLaplaceMeasure_isProbability support hα
  have hpres : MeasurePreserving e μ (μa.prod μb) :=
    splitActiveInactive_measurePreserving support hα
  have hFint : Integrable F (μa.prod μb) :=
    (MeasurePreserving.symm e hpres).integrable_comp_of_integrable hfint
  have hGint : Integrable G μa := hFint.integral_prod_left
  have hGmeas : StronglyMeasurable G :=
    (hf.stronglyMeasurable.comp_measurable e.symm.measurable).integral_prod_right'
  have hgint : Integrable (fun z : ι → ℝ ↦ G (fun j ↦ z j.1)) μ := by
    have hp := hpres.integrable_comp_of_integrable (hGint.comp_fst μb)
    exact hp
  refine ae_eq_condExp_of_forall_setIntegral_eq
    (activeCoordinateMeasurableSpace_le support) hfint
    (fun _ _ _ ↦ hgint.integrableOn) ?_
    (hGmeas.comp_measurable (comap_measurable _)).aestronglyMeasurable
  intro s hs _
  rcases hs with ⟨t, ht, rfl⟩
  have hpre : e ⁻¹' (t ×ˢ Set.univ) =
      (fun z : ι → ℝ ↦ fun j : ↥support ↦ z j.1) ⁻¹' t := by
    ext z
    simp [e, splitActiveInactive]
  have hgchange := hpres.setIntegral_preimage_emb e.measurableEmbedding
    (fun ab ↦ G ab.1) (t ×ˢ Set.univ)
  have hfchange := hpres.setIntegral_preimage_emb e.measurableEmbedding F
    (t ×ˢ Set.univ)
  rw [hpre] at hgchange hfchange
  change (∫ z in (fun z : ι → ℝ ↦ fun j : ↥support ↦ z j.1) ⁻¹' t,
      G (fun j ↦ z j.1) ∂μ) = _
  calc
    _ = ∫ ab in t ×ˢ Set.univ, G ab.1 ∂μa.prod μb := hgchange
    _ = ∫ a in t, G a ∂μa := by
      rw [setIntegral_prod _ (hGint.comp_fst μb).integrableOn]
      simp
    _ = ∫ ab in t ×ˢ Set.univ, F ab ∂μa.prod μb := by
      rw [setIntegral_prod _ hFint.integrableOn]
      simp only [Measure.restrict_univ]
      rfl
    _ = ∫ z in (fun z : ι → ℝ ↦ fun j : ↥support ↦ z j.1) ⁻¹' t, f z ∂μ := by
      simpa [F] using hfchange.symm

/-- The active-coordinate projection has precisely the normalized active Laplace law. -/
theorem activeRestriction_measurePreserving (support : Finset ι) {α : ℝ}
    (hα : 0 < α) :
    MeasurePreserving (fun z : ι → ℝ ↦ fun j : ↥support ↦ z j.1)
      (hybridProductMeasure support α) (activeLaplaceMeasure support α) := by
  exact measurePreserving_fst.comp (splitActiveInactive_measurePreserving support hα)

/-- Fubini's formula identifies conditional expectation with the actual inactive Gaussian
inner integral. Only ordinary integrability is required, and equality is almost everywhere,
as is appropriate for conditional expectation. -/
theorem inactiveGaussianIntegral_ae_eq_condExp
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (hybridProductMeasure support α)) :
    (fun z ↦ inactiveGaussianIntegral support f (fun j ↦ z j.1)) =ᵐ[
      hybridProductMeasure support α]
      (hybridProductMeasure support α)[f | activeCoordinateMeasurableSpace support] := by
  let e := splitActiveInactive support
  let μ := hybridProductMeasure support α
  let μa := activeLaplaceMeasure support α
  let μb := inactiveGaussianMeasure support
  let f' := hf.aestronglyMeasurable.mk f
  have hff' : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hpres : MeasurePreserving e μ (μa.prod μb) :=
    splitActiveInactive_measurePreserving support hα
  have hFae := (MeasurePreserving.symm e hpres).quasiMeasurePreserving.ae_eq_comp hff'
  have hinner : inactiveGaussianIntegral support f =ᵐ[μa]
      inactiveGaussianIntegral support f' := by
    filter_upwards [Measure.ae_ae_of_ae_prod hFae] with a ha
    exact integral_congr_ae ha
  have hpull := (activeRestriction_measurePreserving support hα).quasiMeasurePreserving
    |>.ae_eq_comp hinner
  exact hpull.trans ((inactiveGaussianIntegral_ae_eq_condExp_of_measurable support hα
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hf.congr hff')).trans
      (condExp_congr_ae hff').symm)

/-- The inactive Gaussian inner integral is integrable under the active Laplace law. -/
theorem inactiveGaussianIntegral_integrable
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (hybridProductMeasure support α)) :
    Integrable (inactiveGaussianIntegral support f) (activeLaplaceMeasure support α) := by
  have hpres := splitActiveInactive_measurePreserving support hα
  exact ((MeasurePreserving.symm (splitActiveInactive support) hpres)
    |>.integrable_comp_of_integrable hf).integral_prod_left

/-- The normalized Laplace `L²` form of the paper component. -/
theorem gaussianSpaceComponent_eq_active_lpNorm
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (hybridProductMeasure support α)) :
    gaussianSpaceComponent support α f =
      α ^ (-((support.card : ℝ) / 2)) *
        lpNorm (inactiveGaussianIntegral support f) 2 (activeLaplaceMeasure support α) := by
  have hG := (inactiveGaussianIntegral_integrable support hα hf).aestronglyMeasurable
  dsimp only [gaussianSpaceComponent]
  congr 1
  exact congrArg ENNReal.toReal
    ((eLpNorm_congr_ae (inactiveGaussianIntegral_ae_eq_condExp support hα hf)).symm.trans
      (eLpNorm_comp_measurePreserving hG (activeRestriction_measurePreserving support hα)))

/-- Squaring the component leaves precisely the active Laplace second moment and the
normalization `α^(-|support|)`. This is the form before removing the normalized density. -/
theorem gaussianSpaceComponent_sq_eq_active_integral
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (hybridProductMeasure support α)) :
    gaussianSpaceComponent support α f ^ 2 =
      α ^ (-(support.card : ℝ)) *
        ∫ a, (inactiveGaussianIntegral support f a) ^ 2 ∂activeLaplaceMeasure support α := by
  have hG := (inactiveGaussianIntegral_integrable support hα hf).aestronglyMeasurable
  have hfactor : (α ^ (-((support.card : ℝ) / 2))) ^ 2 = α ^ (-(support.card : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hα.le]
    congr 1
    ring
  have hnorm : lpNorm (inactiveGaussianIntegral support f) 2
      (activeLaplaceMeasure support α) ^ 2 =
      ∫ a, (inactiveGaussianIntegral support f a) ^ 2 ∂activeLaplaceMeasure support α := by
    have h := lpNorm_eq_integral_norm_rpow_toReal
      (f := inactiveGaussianIntegral support f) (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hG
    norm_num only [ENNReal.toReal_ofNat, invOf_eq_inv, Real.rpow_two] at h
    rw [h, ← Real.sqrt_eq_rpow]
    simpa only [Real.norm_eq_abs, sq_abs] using
      Real.sq_sqrt (integral_nonneg fun a ↦ sq_nonneg (‖inactiveGaussianIntegral support f a‖))
  rw [gaussianSpaceComponent_eq_active_lpNorm support hα hf, mul_pow, hfactor, hnorm]

/-- `L²` input suffices for the exact conditional-expectation identification. -/
theorem inactiveGaussianIntegral_ae_eq_condExp_of_memLp_two
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (hybridProductMeasure support α)) :
    (fun z ↦ inactiveGaussianIntegral support f (fun j ↦ z j.1)) =ᵐ[
      hybridProductMeasure support α]
      (hybridProductMeasure support α)[f | activeCoordinateMeasurableSpace support] := by
  have := hybridProductMeasure_isProbability support hα
  exact inactiveGaussianIntegral_ae_eq_condExp support hα (hf.integrable (by norm_num))

/-- The Gaussian inner integral of an `L²` function belongs to the actual active Laplace
`L²` space; no separate outer-integrability assumption is needed. -/
theorem inactiveGaussianIntegral_memLp_two
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (hybridProductMeasure support α)) :
    MemLp (inactiveGaussianIntegral support f) 2 (activeLaplaceMeasure support α) := by
  have := hybridProductMeasure_isProbability support hα
  have hG := (inactiveGaussianIntegral_integrable support hα
    (hf.integrable (by norm_num))).aestronglyMeasurable
  have hcomp := (memLp_congr_ae
    (inactiveGaussianIntegral_ae_eq_condExp_of_memLp_two support hα hf).symm).1
      (hf.condExp (m := activeCoordinateMeasurableSpace support) (by norm_num))
  change eLpNorm (inactiveGaussianIntegral support f) 2 (activeLaplaceMeasure support α) < ∞
  rw [← eLpNorm_comp_measurePreserving hG (activeRestriction_measurePreserving support hα)]
  exact hcomp.eLpNorm_lt_top

/-- The normalized square identity under the natural `L²` hypothesis used in Lemma 5.2. -/
theorem gaussianSpaceComponent_sq_eq_active_integral_of_memLp_two
    (support : Finset ι) {α : ℝ} (hα : 0 < α) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (hybridProductMeasure support α)) :
    gaussianSpaceComponent support α f ^ 2 =
      α ^ (-(support.card : ℝ)) *
        ∫ a, (inactiveGaussianIntegral support f a) ^ 2 ∂activeLaplaceMeasure support α := by
  have := hybridProductMeasure_isProbability support hα
  exact gaussianSpaceComponent_sq_eq_active_integral support hα (hf.integrable (by norm_num))

end

end TimeDependentLattice.Sampling
