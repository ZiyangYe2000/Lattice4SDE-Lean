/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.Median

/-!
# The paper's median constant

The layer-cake proof below retains the exact prefactor in Lemma 5.4 of the paper.
The older product-moment estimate in `Median` remains an independent auxiliary bound.
-/

namespace TimeDependentLattice.Sampling

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The exact multiplier in the norm version of paper Lemma 5.4 and equation (5.11). -/
def medianPaperPrefactor (R k : ℕ) (η q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (η * k / (η * k - q)) ^ (1 / q) *
    (R.choose k : ℝ≥0∞) ^ (1 / (η * k))

/-- Real-valued version of the same multiplier, for the paper's real error constants. -/
def medianPaperPrefactorReal (R k : ℕ) (η q : ℝ) : ℝ :=
  (η * k / (η * k - q)) ^ (1 / q) * (R.choose k : ℝ) ^ (1 / (η * k))

theorem medianPaperPrefactor_eq_ofReal {R k : ℕ} {η q : ℝ}
    (hη : 0 < η) (hk : 0 < k) (hq : 0 < q) (hqη : q < η * k) :
    medianPaperPrefactor R k η q = ENNReal.ofReal (medianPaperPrefactorReal R k η q) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : 0 < η * k := mul_pos hη hkreal
  have hratio : 0 < η * k / (η * k - q) := div_pos hp (sub_pos.mpr hqη)
  rw [medianPaperPrefactor, medianPaperPrefactorReal,
    ENNReal.ofReal_mul (Real.rpow_nonneg hratio.le _),
    ← ENNReal.ofReal_rpow_of_pos hratio,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg (R.choose k)) (by positivity)]
  simp only [ENNReal.ofReal_natCast]

theorem medianPaperPrefactorReal_nonneg {R k : ℕ} {η q : ℝ}
    (hη : 0 < η) (hk : 0 < k) (hq : 0 < q) (hqη : q < η * k) :
    0 ≤ medianPaperPrefactorReal R k η q := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio : 0 < η * k / (η * k - q) :=
    div_pos (mul_pos hη hkreal) (sub_pos.mpr hqη)
  exact mul_nonneg (Real.rpow_nonneg hratio.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem medianPaperPrefactorReal_pos {R k : ℕ} {η q : ℝ}
    (hR : k ≤ R) (hη : 0 < η) (hk : 0 < k) (hq : 0 < q) (hqη : q < η * k) :
    0 < medianPaperPrefactorReal R k η q := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hchoose : 0 < (R.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hR
  have hratio : 0 < η * k / (η * k - q) :=
    div_pos (mul_pos hη hkreal) (sub_pos.mpr hqη)
  exact mul_pos (Real.rpow_pos_of_pos hratio _) (Real.rpow_pos_of_pos hchoose _)

/-- Integrating a normalized power tail gives the constant used in paper Lemma 5.4. -/
theorem lintegral_rpow_le_of_unit_power_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hnonneg : ∀ ω, 0 ≤ f ω)
    {p q : ℝ} (hq : 0 < q) (hqp : q < p)
    (htail : ∀ t > 0, μ {ω | t < f ω} ≤ ENNReal.ofReal (t ^ (-p))) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ) ≤ ENNReal.ofReal (p / (p - q)) := by
  have hq1 : -1 < q - 1 := by linarith
  have hexp : q - 1 - p < -1 := by linarith
  have hsmallInt : IntegrableOn (fun t : ℝ ↦ t ^ (q - 1)) (Ioc 0 1) := by
    exact (intervalIntegral.intervalIntegrable_rpow' hq1).1
  have hlargeInt : IntegrableOn (fun t : ℝ ↦ t ^ (q - 1 - p)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt hexp zero_lt_one
  have hsmall : (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q - 1))) =
      ENNReal.ofReal (1 / q) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hsmallInt]
    · rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hq1)]
      simp [show q - 1 + 1 = q by ring, Real.zero_rpow hq.ne']
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg ht.1.le _
  have hlarge : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (q - 1 - p))) =
      ENNReal.ofReal (1 / (p - q)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hlargeInt]
    · rw [integral_Ioi_rpow_of_lt hexp zero_lt_one]
      congr 1
      simp only [Real.one_rpow]
      rw [show q - 1 - p + 1 = -(p - q) by ring]
      simp only [one_div, neg_div, inv_neg, neg_neg]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (zero_lt_one.trans ht).le _
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ hnonneg)
    hf.aemeasurable hq]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by ext t; simp
  rw [hsplit, lintegral_union measurableSet_Ioi (by simp [Set.disjoint_left])]
  calc
    ENNReal.ofReal q *
        ((∫⁻ t in Ioc (0 : ℝ) 1,
          μ {ω | t < f ω} * ENNReal.ofReal (t ^ (q - 1))) +
         ∫⁻ t in Ioi (1 : ℝ),
          μ {ω | t < f ω} * ENNReal.ofReal (t ^ (q - 1))) ≤
        ENNReal.ofReal q *
          ((∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q - 1))) +
           ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (q - 1 - p))) := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      apply add_le_add
      · apply setLIntegral_mono' measurableSet_Ioc
        intro t ht
        simpa using mul_le_mul_of_nonneg_right (prob_le_one (μ := μ)) bot_le
      · apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := zero_lt_one.trans ht
        calc
          μ {ω | t < f ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
              ENNReal.ofReal (t ^ (-p)) * ENNReal.ofReal (t ^ (q - 1)) :=
            mul_le_mul_of_nonneg_right (htail t ht0) bot_le
          _ = ENNReal.ofReal (t ^ (q - 1 - p)) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _),
              ← Real.rpow_add ht0]
            congr 2
            ring
    _ = ENNReal.ofReal (p / (p - q)) := by
      rw [hsmall, hlarge, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul hq.le]
      congr 1
      field_simp [hq.ne', sub_ne_zero.mpr hqp.ne']
      ring

/-- Markov's inequality for an individual copy, with the real threshold used in the paper. -/
theorem measure_abs_gt_le_of_eLpNorm'_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) {η K t : ℝ}
    (hη : 0 < η) (hK : 0 ≤ K) (ht : 0 < t)
    (hcopy : eLpNorm' f η μ ≤ ENNReal.ofReal K) :
    μ {ω | t < |f ω|} ≤ ENNReal.ofReal ((K / t) ^ η) := by
  have hsubset : {ω | t < |f ω|} ⊆
      {ω | ENNReal.ofReal t ^ η ≤ ‖f ω‖ₑ ^ η} := by
    intro ω hω
    apply ENNReal.rpow_le_rpow _ hη.le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hω.le
  have hmoment : (∫⁻ ω, ‖f ω‖ₑ ^ η ∂μ) ≤ ENNReal.ofReal K ^ η := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hη]
    exact ENNReal.rpow_le_rpow hcopy hη.le
  have htne : ENNReal.ofReal t ^ η ≠ 0 := by positivity
  have htfin : ENNReal.ofReal t ^ η ≠ ⊤ := by finiteness
  calc
    μ {ω | t < |f ω|} ≤ μ {ω | ENNReal.ofReal t ^ η ≤ ‖f ω‖ₑ ^ η} :=
      measure_mono hsubset
    _ ≤ (∫⁻ ω, ‖f ω‖ₑ ^ η ∂μ) / (ENNReal.ofReal t ^ η) :=
      meas_ge_le_lintegral_div (hf.enorm.pow_const η).aemeasurable htne htfin
    _ ≤ ENNReal.ofReal K ^ η / ENNReal.ofReal t ^ η :=
      ENNReal.div_le_div_right hmoment _
    _ = ENNReal.ofReal ((K / t) ^ η) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hK hη.le,
        ENNReal.ofReal_rpow_of_pos ht, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht η),
        Real.div_rpow hK ht.le]

/-- Paper Lemma 5.4 in norm form, for a positive real copy bound. -/
theorem median_eLpNorm'_le_paper_of_pos
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hcard : Fintype.card ι = 2 * k - 1)
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {η q K : ℝ} (hk : 0 < k) (hq : 0 < q) (hqη : q < η * k) (hK : 0 < K)
    (hcopy : ∀ i, eLpNorm' (value i) η μ ≤ ENNReal.ofReal K) :
    eLpNorm' median q μ ≤
      ENNReal.ofReal (η * k / (η * k - q)) ^ (1 / q) *
        ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / (η * k)) * ENNReal.ofReal K := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hη : 0 < η := by nlinarith
  let p : ℝ := η * k
  have hp : 0 < p := mul_pos hη hkreal
  have hkp : k ≤ Fintype.card ι := by omega
  have hCnat : 0 < (Fintype.card ι).choose k := Nat.choose_pos hkp
  let C : ℝ := (Fintype.card ι).choose k
  have hC : 0 < C := by dsimp [C]; exact_mod_cast hCnat
  let A : ℝ := C ^ (1 / p) * K
  have hA : 0 < A := mul_pos (Real.rpow_pos_of_pos hC _) hK
  have hmedMeas : Measurable median := measurable_oddMedian (by omega) hmedian hmeas
  have hnormalizedTail : ∀ t > 0,
      μ {ω | t < |median ω| / A} ≤ ENNReal.ofReal (t ^ (-p)) := by
    intro t ht
    have hAt : 0 < A * t := mul_pos hA ht
    have htail := measure_abs_median_gt_le_choose_mul hmedian hindep
      (fun i ↦ measure_abs_gt_le_of_eLpNorm'_le (hmeas i) hη hK.le hAt (hcopy i))
    have hevent : {ω | t < |median ω| / A} = {ω | A * t < |median ω|} := by
      ext ω
      simp only [mem_ofPred_eq, lt_div_iff₀ hA]
      rw [mul_comm t A]
    rw [hevent]
    refine htail.trans_eq ?_
    have hbound : C * ((K / (A * t)) ^ η) ^ k = t ^ (-p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hK hAt).le]
      change C * (K / (A * t)) ^ p = t ^ (-p)
      rw [Real.div_rpow hK.le hAt.le, Real.mul_rpow hA.le ht.le]
      have hAp : A ^ p = C * K ^ p := by
        dsimp [A]
        rw [Real.mul_rpow (Real.rpow_pos_of_pos hC _).le hK.le,
          ← Real.rpow_mul hC.le]
        have hid : 1 / p * p = 1 := by field_simp
        rw [hid, Real.rpow_one]
      rw [hAp, Real.rpow_neg ht.le]
      field_simp
    calc
      ((Fintype.card ι).choose k : ℝ≥0∞) *
          ENNReal.ofReal ((K / (A * t)) ^ η) ^ k =
          ENNReal.ofReal (C * ((K / (A * t)) ^ η) ^ k) := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_pow
          (Real.rpow_nonneg (div_pos hK hAt).le _)]
        simp [C]
      _ = ENNReal.ofReal (t ^ (-p)) := congrArg ENNReal.ofReal hbound
  have hmoment := lintegral_rpow_le_of_unit_power_tail
    (hmedMeas.abs.div_const A) (fun ω ↦ div_nonneg (abs_nonneg _) hA.le)
    hq hqη hnormalizedTail
  have hnorm : eLpNorm' (fun ω ↦ median ω / A) q μ ≤
      ENNReal.ofReal (p / (p - q)) ^ (1 / q) := by
    rw [eLpNorm'_eq_lintegral_enorm]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    convert hmoment using 1
    congr 1
    ext ω
    rw [← ofReal_norm, Real.norm_eq_abs, abs_div, abs_of_pos hA,
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (abs_nonneg _) hA.le) hq.le]
  have hscale : eLpNorm' median q μ =
      ENNReal.ofReal A * eLpNorm' (fun ω ↦ median ω / A) q μ := by
    have hs := eLpNorm'_const_smul (μ := μ) (f := fun ω ↦ median ω / A) A hq
    have heq : A • (fun ω ↦ median ω / A) = median := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [heq, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos hA] at hs
    exact hs
  rw [hscale]
  refine (mul_le_mul_of_nonneg_left hnorm bot_le).trans_eq ?_
  dsimp [A, C, p]
  rw [ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hCnat)]
  simp only [ENNReal.ofReal_natCast]
  ring

/-- Exact norm prefactor in Lemma 5.4 of the paper.  Zero and infinite copy bounds are included. -/
theorem median_eLpNorm'_le_paper
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hcard : Fintype.card ι = 2 * k - 1)
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {η q : ℝ} {K : ℝ≥0∞} (hk : 0 < k) (hq : 0 < q) (hqη : q < η * k)
    (hcopy : ∀ i, eLpNorm' (value i) η μ ≤ K) :
    eLpNorm' median q μ ≤
      ENNReal.ofReal (η * k / (η * k - q)) ^ (1 / q) *
        ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / (η * k)) * K := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hηk : 0 < η * k := hq.trans hqη
  have hkp : k ≤ Fintype.card ι := by omega
  have hchoose : 0 < ((Fintype.card ι).choose k : ℝ≥0∞) := by
    exact_mod_cast Nat.choose_pos hkp
  have hratio : 0 < η * k / (η * k - q) := div_pos hηk (sub_pos.mpr hqη)
  have hpref : 0 < ENNReal.ofReal (η * k / (η * k - q)) ^ (1 / q) *
      ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / (η * k)) := by positivity
  by_cases hKtop : K = ⊤
  · rw [hKtop, ENNReal.mul_top hpref.ne']
    exact le_top
  by_cases hKzero : K = 0
  · have hold := median_eLpNorm'_le hmedian hmeas hindep hk hq hqη hcopy
    simpa [hKzero] using hold
  have hKreal : 0 < K.toReal := ENNReal.toReal_pos hKzero hKtop
  have hcopyReal : ∀ i, eLpNorm' (value i) η μ ≤ ENNReal.ofReal K.toReal := by
    simpa [ENNReal.ofReal_toReal hKtop] using hcopy
  simpa [ENNReal.ofReal_toReal hKtop] using
    median_eLpNorm'_le_paper_of_pos hcard hmedian hmeas hindep hk hq hqη hKreal hcopyReal

/-- The exact moment form (5.7) in Lemma 5.4 of the paper. -/
theorem median_lintegral_rpow_le_paper
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hcard : Fintype.card ι = 2 * k - 1)
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {η q : ℝ} {K : ℝ≥0∞} (hk : 0 < k) (hq : 0 < q) (hqη : q < η * k)
    (hcopy : ∀ i, eLpNorm' (value i) η μ ≤ K) :
    (∫⁻ ω, ‖median ω‖ₑ ^ q ∂μ) ≤
      ENNReal.ofReal (η * k / (η * k - q)) *
        ((Fintype.card ι).choose k : ℝ≥0∞) ^ (q / (η * k)) * K ^ q := by
  have hnorm := median_eLpNorm'_le_paper hcard hmedian hmeas hindep hk hq hqη hcopy
  calc
    (∫⁻ ω, ‖median ω‖ₑ ^ q ∂μ) = eLpNorm' median q μ ^ q :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' hq
    _ ≤ (ENNReal.ofReal (η * k / (η * k - q)) ^ (1 / q) *
        ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / (η * k)) * K) ^ q :=
      ENNReal.rpow_le_rpow hnorm hq.le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have hcancel : 1 / q * q = 1 := by field_simp
      rw [hcancel, ENNReal.rpow_one]
      rw [show 1 / (η * k) * q = q / (η * k) by ring]

/-- The paper's exact median bound for the standard measurable `L^q` seminorm. -/
theorem median_eLpNorm_le_paper
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : ι → Ω → ℝ} {median : Ω → ℝ}
    (hcard : Fintype.card ι = 2 * k - 1)
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {η q : ℝ} {K : ℝ≥0∞} (hk : 0 < k) (hq : 0 < q) (hqη : q < η * k)
    (hcopy : ∀ i, eLpNorm' (value i) η μ ≤ K) :
    eLpNorm median (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (η * k / (η * k - q)) ^ (1 / q) *
        ((Fintype.card ι).choose k : ℝ≥0∞) ^ (1 / (η * k)) * K := by
  have hmedianMeas := measurable_oddMedian (by omega) hmedian hmeas
  rw [eLpNorm_eq_eLpNorm' (by positivity) (by finiteness)
    hmedianMeas.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
  exact median_eLpNorm'_le_paper hcard hmedian hmeas hindep hk hq hqη hcopy

end

end TimeDependentLattice.Sampling
