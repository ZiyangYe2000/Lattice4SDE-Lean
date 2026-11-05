/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib

/-!
# Median estimators

This file contains the finite combinatorial part of paper Lemma 5.4.  We use a predicate for an
odd median: at least `k` entries lie on either side of the selected value.  This formulation keeps
the probabilistic argument independent of a particular sorting implementation.
-/

namespace TimeDependentLattice.Sampling

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section

/-- `x` is a median with `k` witnesses on each side of the finite family `value`.

For a family of size `2 * k - 1`, this is the usual odd median condition.  The definition is also
useful on an arbitrary finite index type because Lemma 5.4 only uses the two cardinal inequalities.
-/
def IsOddMedian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (value : ι → ℝ) (x : ℝ) : Prop :=
  k ≤ (Finset.univ.filter fun i ↦ x ≤ value i).card ∧
    k ≤ (Finset.univ.filter fun i ↦ value i ≤ x).card

/-- Translating every entry and the selected median by the same constant preserves the odd-median
property. -/
theorem IsOddMedian.sub_const
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → ℝ} {x : ℝ}
    (hmedian : IsOddMedian k value x) (c : ℝ) :
    IsOddMedian k (fun i ↦ value i - c) (x - c) := by
  simpa [IsOddMedian, sub_le_sub_iff_right] using hmedian

/-- A strict sublevel set of an odd median is a finite union of intersections of copy sublevel
sets.  The cardinal hypothesis includes the paper's case `card ι = 2 * k - 1`. -/
theorem IsOddMedian.lt_iff_exists_subset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → ℝ} {x a : ℝ}
    (hmedian : IsOddMedian k value x) (hcard : Fintype.card ι < 2 * k) :
    x < a ↔ ∃ s ∈ Finset.univ.powersetCard k, ∀ i ∈ s, value i < a := by
  classical
  constructor
  · intro hxa
    obtain ⟨s, hs, hsk⟩ := Finset.exists_subset_card_eq hmedian.2
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hsk⟩, ?_⟩
    intro i hi
    exact ((Finset.mem_filter.mp (hs hi)).2).trans_lt hxa
  · rintro ⟨s, hs, hsa⟩
    by_contra hxa
    have hax : a ≤ x := le_of_not_gt hxa
    let upper := Finset.univ.filter fun i ↦ x ≤ value i
    have hdisj : Disjoint s upper := by
      apply Finset.disjoint_left.mpr
      intro i hi hu
      have hxv : x ≤ value i := (Finset.mem_filter.mp hu).2
      exact (hsa i hi).not_ge (hax.trans hxv)
    have hsum : s.card + upper.card ≤ Fintype.card ι := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hsk : s.card = k := (Finset.mem_powersetCard.mp hs).2
    have hup : k ≤ upper.card := hmedian.1
    omega

/-- Any pointwise odd median of measurable copies is measurable; no additional measurability
assumption on the selected representative is necessary. -/
theorem measurable_oddMedian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hcard : Fintype.card ι < 2 * k)
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) : Measurable median := by
  classical
  apply measurable_of_Iio
  intro a
  have hset : median ⁻¹' Set.Iio a =
      ⋃ s ∈ Finset.univ.powersetCard k, ⋂ i ∈ s, {ω | value i ω < a} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_ofPred_eq]
    simpa only [exists_prop] using (hmedian ω).lt_iff_exists_subset (a := a) hcard
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun s _ ↦
    s.measurableSet_biInter fun i _ ↦ (hmeas i) measurableSet_Iio

/-- The odd-median predicate determines a unique real value whenever fewer than `2k` copies
are present. -/
theorem IsOddMedian.unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → ℝ} {x y : ℝ}
    (hx : IsOddMedian k value x) (hy : IsOddMedian k value y)
    (hcard : Fintype.card ι < 2 * k) : x = y := by
  apply le_antisymm
  · by_contra hxy
    have hsub := (hy.lt_iff_exists_subset (a := x) hcard).mp (lt_of_not_ge hxy)
    exact (lt_irrefl x) ((hx.lt_iff_exists_subset hcard).mpr hsub)
  · by_contra hyx
    have hsub := (hx.lt_iff_exists_subset (a := y) hcard).mp (lt_of_not_ge hyx)
    exact (lt_irrefl y) ((hy.lt_iff_exists_subset hcard).mpr hsub)

/-- At least `k` entries have absolute value at least the absolute value of an odd median. -/
theorem exists_card_eq_of_abs_median_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → ℝ} {x : ℝ}
    (hmedian : IsOddMedian k value x) :
    ∃ indices : Finset ι,
      indices.card = k ∧ ∀ i ∈ indices, |x| ≤ |value i| := by
  rcases le_total 0 x with hx | hx
  · obtain ⟨indices, hsubset, hcard⟩ :=
      Finset.exists_subset_card_eq hmedian.1
    refine ⟨indices, hcard, ?_⟩
    intro i hi
    have hxi : x ≤ value i := by
      have : i ∈ Finset.univ.filter fun j ↦ x ≤ value j := hsubset hi
      exact (Finset.mem_filter.mp this).2
    simpa [abs_of_nonneg hx] using hxi.trans (le_abs_self _)
  · have hxnonpos : x ≤ 0 := hx
    obtain ⟨indices, hsubset, hcard⟩ :=
      Finset.exists_subset_card_eq hmedian.2
    refine ⟨indices, hcard, ?_⟩
    intro i hi
    have hix : value i ≤ x := by
      have : i ∈ Finset.univ.filter fun j ↦ value j ≤ x := hsubset hi
      exact (Finset.mem_filter.mp this).2
    simpa [abs_of_nonpos hxnonpos] using (neg_le_neg hix).trans (neg_le_abs _)

/-- Pointwise moment form of the median argument.  The `q`-th power of the median is bounded by
the sum, over all `k`-element subsets, of products of the `(q / k)`-th powers of the copies. -/
theorem enorm_median_rpow_le_sum_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → ℝ} {x q : ℝ}
    (hmedian : IsOddMedian k value x) (hk : 0 < k) (hq : 0 ≤ q) :
    ‖x‖ₑ ^ q ≤
      ∑ indices ∈ Finset.univ.powersetCard k,
        ∏ i ∈ indices, ‖value i‖ₑ ^ (q / k) := by
  obtain ⟨indices, hcard, hlarge⟩ := exists_card_eq_of_abs_median_le hmedian
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hqk : 0 ≤ q / (k : ℝ) := div_nonneg hq (Nat.cast_nonneg _)
  have hpower : (‖x‖ₑ ^ (q / (k : ℝ))) ^ k = ‖x‖ₑ ^ q := by
    calc
      (‖x‖ₑ ^ (q / (k : ℝ))) ^ k =
          (‖x‖ₑ ^ (q / (k : ℝ))) ^ (k : ℝ) :=
        (ENNReal.rpow_natCast _ k).symm
      _ = ‖x‖ₑ ^ ((q / (k : ℝ)) * (k : ℝ)) :=
        (ENNReal.rpow_mul _ _ _).symm
      _ = ‖x‖ₑ ^ q := by
        congr 1
        exact div_mul_cancel₀ q hkreal
  have hterm : ‖x‖ₑ ^ q ≤ ∏ i ∈ indices, ‖value i‖ₑ ^ (q / k) := by
    calc
      ‖x‖ₑ ^ q = ∏ _i ∈ indices, ‖x‖ₑ ^ (q / (k : ℝ)) := by
        simp [hcard, hpower]
      _ ≤ ∏ i ∈ indices, ‖value i‖ₑ ^ (q / (k : ℝ)) := by
        apply Finset.prod_le_prod
        intro i hi
        apply ENNReal.rpow_le_rpow _ hqk
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hlarge i hi)
  have hsingle :
      (∏ i ∈ indices, ‖value i‖ₑ ^ (q / k)) ≤
        ∑ candidate ∈ Finset.univ.powersetCard k,
          ∏ i ∈ candidate, ‖value i‖ₑ ^ (q / k) := by
    apply Finset.single_le_sum (f := fun candidate ↦
      ∏ i ∈ candidate, ‖value i‖ₑ ^ (q / k)) (fun _ _ ↦ bot_le)
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  exact hterm.trans hsingle

/-- If the absolute value of an odd median exceeds `t`, then `k` entries have absolute value
exceeding `t`.  This is the deterministic event inclusion used in paper Lemma 5.4. -/
theorem exists_card_eq_of_abs_median_gt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → ℝ} {x t : ℝ}
    (hmedian : IsOddMedian k value x) (hxt : t < |x|) :
    ∃ indices : Finset ι,
      indices.card = k ∧ ∀ i ∈ indices, t < |value i| := by
  rcases le_total 0 x with hx | hx
  · have htx : t < x := by simpa [abs_of_nonneg hx] using hxt
    obtain ⟨indices, hsubset, hcard⟩ :=
      Finset.exists_subset_card_eq hmedian.1
    refine ⟨indices, hcard, ?_⟩
    intro i hi
    have hxi : x ≤ value i := by
      have : i ∈ Finset.univ.filter fun j ↦ x ≤ value j := hsubset hi
      exact (Finset.mem_filter.mp this).2
    exact htx.trans_le hxi |>.trans_le (le_abs_self _)
  · have hxnonpos : x ≤ 0 := hx
    have htx : t < -x := by simpa [abs_of_nonpos hxnonpos] using hxt
    obtain ⟨indices, hsubset, hcard⟩ :=
      Finset.exists_subset_card_eq hmedian.2
    refine ⟨indices, hcard, ?_⟩
    intro i hi
    have hix : value i ≤ x := by
      have : i ∈ Finset.univ.filter fun j ↦ value j ≤ x := hsubset hi
      exact (Finset.mem_filter.mp this).2
    have hneg : -x ≤ -value i := neg_le_neg hix
    exact htx.trans_le hneg |>.trans_le (neg_le_abs _)

/-- Event form of `exists_card_eq_of_abs_median_gt`: a large median belongs to the union of the
events on which some `k`-element set of copies are all large. -/
theorem abs_median_gt_subset_iUnion
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ} {t : ℝ}
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω)) :
    {ω | t < |median ω|} ⊆
      ⋃ indices ∈ Finset.univ.powersetCard k,
        ⋂ i ∈ indices, {ω | t < |value i ω|} := by
  intro ω hω
  obtain ⟨indices, hcard, hlarge⟩ :=
    exists_card_eq_of_abs_median_gt (hmedian ω) hω
  refine Set.mem_iUnion.2 ⟨indices, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  simp only [Set.mem_iInter]
  intro i hi
  exact hlarge i hi

/-- The union bound following the deterministic median event inclusion. -/
theorem measure_abs_median_gt_le_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : MeasureTheory.Measure Ω)
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ} {t : ℝ}
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω)) :
    μ {ω | t < |median ω|} ≤
      ∑ indices ∈ Finset.univ.powersetCard k,
        μ (⋂ i ∈ indices, {ω | t < |value i ω|}) := by
  calc
    μ {ω | t < |median ω|} ≤
        μ (⋃ indices ∈ Finset.univ.powersetCard k,
          ⋂ i ∈ indices, {ω | t < |value i ω|}) :=
      MeasureTheory.measure_mono (abs_median_gt_subset_iUnion hmedian)
    _ ≤ _ := MeasureTheory.measure_biUnion_finset_le _ _

/-- Independence turns the probability of a finite intersection of large-copy events into a
product. -/
theorem measure_iInter_abs_gt_eq_prod
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {value : ι → Ω → ℝ}
    (hindep : iIndepFun value μ) (indices : Finset ι) (t : ℝ) :
    μ (⋂ i ∈ indices, {ω | t < |value i ω|}) =
      ∏ i ∈ indices, μ {ω | t < |value i ω|} := by
  apply hindep.meas_biInter
  intro i hi
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{x : ℝ | t < |x|}, measurableSet_Ioi.preimage measurable_abs, rfl⟩

/-- The union bound and independence give the binomial tail estimate for an odd median. -/
theorem measure_abs_median_gt_le_choose_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hindep : iIndepFun value μ) {t : ℝ} {tail : ℝ≥0∞}
    (htail : ∀ i, μ {ω | t < |value i ω|} ≤ tail) :
    μ {ω | t < |median ω|} ≤
      (Fintype.card ι).choose k * tail ^ k := by
  calc
    μ {ω | t < |median ω|} ≤
        ∑ indices ∈ Finset.univ.powersetCard k,
          μ (⋂ i ∈ indices, {ω | t < |value i ω|}) :=
      measure_abs_median_gt_le_sum μ hmedian
    _ = ∑ indices ∈ Finset.univ.powersetCard k,
          ∏ i ∈ indices, μ {ω | t < |value i ω|} := by
      apply Finset.sum_congr rfl
      intro indices hindices
      exact measure_iInter_abs_gt_eq_prod hindep indices t
    _ ≤ ∑ _indices ∈ Finset.univ.powersetCard k, tail ^ k := by
      apply Finset.sum_le_sum
      intro indices hindices
      have hcard : indices.card = k := (Finset.mem_powersetCard.mp hindices).2
      calc
        (∏ i ∈ indices, μ {ω | t < |value i ω|}) ≤
            ∏ _i ∈ indices, tail := by
          exact Finset.prod_le_prod fun i _ ↦ htail i
        _ = tail ^ k := by simp [hcard]
    _ = (Fintype.card ι).choose k * tail ^ k := by
      simp

/-- An auxiliary median moment bound from independent products.

The final sampling theorems use the paper's exact tail-integration constant, proved in
`Sampling/MedianTail.lean`. This product-moment estimate is a separate reusable bound. -/
theorem median_lintegral_rpow_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {η q : ℝ} {K : ℝ≥0∞} (hk : 0 < k) (hq : 0 < q)
    (hqη : q < η * k)
    (hcopy : ∀ i, eLpNorm' (value i) η μ ≤ K) :
    ∫⁻ ω, ‖median ω‖ₑ ^ q ∂μ ≤
      (Fintype.card ι).choose k * K ^ q := by
  let r : ℝ := q / k
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : 0 < r := div_pos hq hkreal
  have hrη : r ≤ η := by
    exact ((div_lt_iff₀ hkreal).mpr hqη).le
  let transformed : ι → Ω → ℝ≥0∞ := fun i ω ↦ ‖value i ω‖ₑ ^ r
  have htransformed_meas (i : ι) : Measurable (transformed i) := by
    exact ENNReal.continuous_rpow_const.measurable.comp (hmeas i).enorm
  have htransformed_indep : iIndepFun transformed μ := by
    have hcomp := hindep.comp
      (fun _i (x : ℝ) ↦ ‖x‖ₑ ^ r)
      (fun _i ↦ ENNReal.continuous_rpow_const.measurable.comp measurable_enorm)
    simpa [transformed, Function.comp_def] using hcomp
  have hfactor (i : ι) : ∫⁻ ω, transformed i ω ∂μ ≤ K ^ r := by
    calc
      (∫⁻ ω, transformed i ω ∂μ) = eLpNorm' (value i) r μ ^ r := by
        simpa [transformed] using
          (lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := value i) hr)
      _ ≤ K ^ r := by
        apply ENNReal.rpow_le_rpow _ hr.le
        exact (eLpNorm'_le_eLpNorm'_of_exponent_le hr hrη μ
          (hmeas i).aestronglyMeasurable).trans (hcopy i)
  calc
    (∫⁻ ω, ‖median ω‖ₑ ^ q ∂μ) ≤
        ∫⁻ ω, ∑ indices ∈ Finset.univ.powersetCard k,
          ∏ i ∈ indices, transformed i ω ∂μ := by
      apply lintegral_mono
      intro ω
      simpa [transformed, r] using
        enorm_median_rpow_le_sum_prod (hmedian ω) hk hq.le
    _ = ∑ indices ∈ Finset.univ.powersetCard k,
          ∫⁻ ω, ∏ i ∈ indices, transformed i ω ∂μ := by
      apply lintegral_finsetSum
      intro indices hindices
      exact indices.measurable_prod fun i hi ↦ htransformed_meas i
    _ = ∑ indices ∈ Finset.univ.powersetCard k,
          ∏ i ∈ indices, ∫⁻ ω, transformed i ω ∂μ := by
      apply Finset.sum_congr rfl
      intro indices hindices
      exact lintegral_prod_eq_prod_lintegral_of_indepFun
        indices transformed htransformed_indep htransformed_meas
    _ ≤ ∑ indices ∈ Finset.univ.powersetCard k,
          ∏ _i ∈ indices, K ^ r := by
      apply Finset.sum_le_sum
      intro indices hindices
      exact Finset.prod_le_prod fun i hi ↦ hfactor i
    _ = ∑ _indices ∈ Finset.univ.powersetCard k, K ^ q := by
      apply Finset.sum_congr rfl
      intro indices hindices
      have hcard : indices.card = k := (Finset.mem_powersetCard.mp hindices).2
      calc
        (∏ _i ∈ indices, K ^ r) = (K ^ r) ^ k := by simp [hcard]
        _ = (K ^ r) ^ (k : ℝ) := (ENNReal.rpow_natCast _ k).symm
        _ = K ^ (r * (k : ℝ)) := (ENNReal.rpow_mul _ _ _).symm
        _ = K ^ q := by
          congr 1
          exact div_mul_cancel₀ q hkreal.ne'
    _ = (Fintype.card ι).choose k * K ^ q := by simp

/-- `L^q`-seminorm form of `median_lintegral_rpow_le`.  This is the form used in
Theorem 3.1. -/
theorem median_eLpNorm'_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {η q : ℝ} {K : ℝ≥0∞} (hk : 0 < k) (hq : 0 < q)
    (hqη : q < η * k)
    (hcopy : ∀ i, eLpNorm' (value i) η μ ≤ K) :
    eLpNorm' median q μ ≤
      ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / q) * K := by
  have hmoment := median_lintegral_rpow_le
    hmedian hmeas hindep hk hq hqη hcopy
  rw [eLpNorm'_eq_lintegral_enorm]
  calc
    (∫⁻ ω, ‖median ω‖ₑ ^ q ∂μ) ^ (1 / q) ≤
        (((Fintype.card ι).choose k : ℝ≥0∞) * K ^ q) ^ (1 / q) :=
      ENNReal.rpow_le_rpow hmoment (by positivity)
    _ = ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / q) *
        (K ^ q) ^ (1 / q) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    _ = ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / q) * K := by
      congr 1
      rw [← ENNReal.rpow_mul]
      have hmul : q * (1 / q) = 1 := by field_simp
      rw [hmul, ENNReal.rpow_one]

end

end TimeDependentLattice.Sampling
