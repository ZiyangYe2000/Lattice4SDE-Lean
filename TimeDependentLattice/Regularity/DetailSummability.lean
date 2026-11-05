/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Regularity.Eta
import TimeDependentLattice.Regularity.FiniteSums

/-!
# Summability of Brownian-bridge detail coordinates

This file formalizes the finite-level summation in Lemma 4.4.  The proof keeps the
paper's factor `3/2` and represents the list `A_{ℓ_*}` by level/component positions.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open scoped BigOperators
open TimeDependentLattice
open TimeDependentLattice.BrownianBridge

/-- The paper's `Θ_ρ`, the `ρ`-power sum of the diffusion-column norms. -/
def columnRhoSum {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (ρ : ℝ) : ℝ :=
  ∑ r : Fin noiseDim, columnNorm diffusion r ^ ρ

theorem columnRhoSum_nonneg {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (ρ : ℝ) :
    0 ≤ columnRhoSum diffusion ρ := by
  unfold columnRhoSum
  exact Finset.sum_nonneg fun r _ => Real.rpow_nonneg (columnNorm_nonneg diffusion r) ρ

/-- The entry of the paper's list `A_{ℓ_*}` associated with a detail coordinate. -/
def detailLevelWeight {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (ρ : ℝ)
    (j : DetailIndex J noiseDim) : ℝ :=
  (2 : ℝ) ^ (-ρ * (j.level.val : ℝ) / 2) *
    columnNorm diffusion j.component ^ ρ

theorem detailLevelWeight_nonneg {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (ρ : ℝ)
    (j : DetailIndex J noiseDim) :
    0 ≤ detailLevelWeight diffusion ρ j := by
  unfold detailLevelWeight
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (columnNorm_nonneg diffusion j.component) _)

/-- Raising a detail height to `ρ` separates the common `√T/2` factor from the
level/component weight. -/
theorem detailHeightFactor_rpow
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ) (j : DetailIndex J noiseDim) :
    detailHeightFactor diffusion T j ^ ρ =
      (√T / 2) ^ ρ * detailLevelWeight diffusion ρ j := by
  rw [detailHeightFactor, detailLevelWeight]
  rw [Real.mul_rpow (by positivity)
      (columnNorm_nonneg diffusion j.component)]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have hlevel :
      ((2 : ℝ) ^ (-(j.level.val : ℝ) / 2)) ^ ρ =
        (2 : ℝ) ^ (-ρ * (j.level.val : ℝ) / 2) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hlevel]
  ring

/-- Details of level at most `ℓ*` whose open support contains `t`. -/
def activeDetailsUpTo {J noiseDim : ℕ} (T t : ℝ) (ℓstar : ℕ) :
    Finset (DetailIndex J noiseDim) := by
  classical
  exact Finset.univ.filter fun j =>
    j.level.val ≤ ℓstar ∧ t ∈ j.supportInterior T

/-- Level/component positions up to `ℓ*`. -/
def levelComponentPositions (J noiseDim ℓstar : ℕ) :
    Finset (Fin J × Fin noiseDim) :=
  Finset.univ.filter fun q => q.1.val ≤ ℓstar

/-- The detail support intervals in `details` have a common interior point. -/
def detailSupportsMeet {J noiseDim : ℕ} (T : ℝ)
    (details : Finset (DetailIndex J noiseDim)) : Prop :=
  ∃ t : ℝ, ∀ j ∈ details, t ∈ j.supportInterior T

/-- The (possibly overcounting) class of `n`-element detail sets for which `jstar` is
one of the deepest coordinates. -/
def deepestDetailClass {J noiseDim : ℕ} (T : ℝ) (n : ℕ)
    (jstar : DetailIndex J noiseDim) : Finset (Finset (DetailIndex J noiseDim)) := by
  classical
  exact (Finset.univ.powersetCard n).filter fun details =>
    jstar ∈ details ∧
      (∀ j ∈ details, j.level.val ≤ jstar.level.val) ∧
      detailSupportsMeet T details

/-- Every remaining coordinate in a class with deepest coordinate `jstar` is an active
ancestor at the center of `jstar`. -/
theorem erase_subset_activeDetailsUpTo_center
    {J noiseDim : ℕ} {T : ℝ} (hT : 0 < T)
    (details : Finset (DetailIndex J noiseDim)) (jstar : DetailIndex J noiseDim)
    (hdeep : ∀ j ∈ details, j.level.val ≤ jstar.level.val)
    (hjstar : jstar ∈ details) (hmeet : detailSupportsMeet T details) :
    details.erase jstar ⊆
      activeDetailsUpTo T (jstar.center T) jstar.level.val := by
  rcases hmeet with ⟨t, ht⟩
  intro j hj
  have hjDetails : j ∈ details := Finset.mem_of_mem_erase hj
  have hcontains := detailSupportInterior_subset_of_level_le_of_common_support
    hT j jstar (hdeep j hjDetails) (ht j hjDetails) (ht jstar hjstar)
  have hcenter := jstar.center_mem_supportInterior hT
  simpa [activeDetailsUpTo, hdeep j hjDetails] using hcontains hcenter

/-- On details active at one point, `(level, component)` is injective. -/
theorem levelComponent_injOn_activeDetailsUpTo
    {J noiseDim : ℕ} {T t : ℝ} (hT : 0 < T) (ℓstar : ℕ) :
    Set.InjOn (fun j : DetailIndex J noiseDim => (j.level, j.component))
      (activeDetailsUpTo (J := J) (noiseDim := noiseDim) T t ℓstar) := by
  intro j hj j' hj' heq
  have hjmem : j.level.val ≤ ℓstar ∧ t ∈ j.supportInterior T := by
    simpa [activeDetailsUpTo] using hj
  have hjmem' : j'.level.val ≤ ℓstar ∧ t ∈ j'.supportInterior T := by
    simpa [activeDetailsUpTo] using hj'
  exact detail_eq_of_same_level_component_of_common_support hT j j'
    (congrArg Prod.fst heq) (congrArg Prod.snd heq) hjmem.2 hjmem'.2

/-- The sum of active detail weights is bounded by the full list of level/component
positions used in the paper. -/
theorem sum_activeDetailsUpTo_weight_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T t : ℝ} (hT : 0 < T) (ρ : ℝ) (ℓstar : ℕ) :
    (∑ j ∈ activeDetailsUpTo (J := J) (noiseDim := noiseDim) T t ℓstar,
        detailLevelWeight diffusion ρ j) ≤
      ∑ q ∈ levelComponentPositions J noiseDim ℓstar,
        (2 : ℝ) ^ (-ρ * (q.1.val : ℝ) / 2) *
          columnNorm diffusion q.2 ^ ρ := by
  apply Finset.sum_le_sum_of_injOn
      (fun j : DetailIndex J noiseDim => (j.level, j.component))
      (levelComponent_injOn_activeDetailsUpTo hT ℓstar)
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
    have hj' : j.level.val ≤ ℓstar ∧ t ∈ j.supportInterior T := by
      simpa [activeDetailsUpTo] using hj
    simpa [levelComponentPositions] using hj'.1
  · intro j hj
    rfl
  · intro q hq hnot
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (columnNorm_nonneg diffusion q.2) _)

/-- The level/component position sum is exactly the truncated geometric factor times
`Θ_ρ`. -/
theorem sum_levelComponentPositions_eq
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (ρ : ℝ) (ℓstar : ℕ) :
    (∑ q ∈ levelComponentPositions J noiseDim ℓstar,
        (2 : ℝ) ^ (-ρ * (q.1.val : ℝ) / 2) *
          columnNorm diffusion q.2 ^ ρ) =
      (∑ level ∈ (Finset.univ : Finset (Fin J)).filter
          (fun level => level.val ≤ ℓstar),
          (2 : ℝ) ^ (-ρ * (level.val : ℝ) / 2)) *
        columnRhoSum diffusion ρ := by
  have hpositions : levelComponentPositions J noiseDim ℓstar =
      ((Finset.univ : Finset (Fin J)).filter
          (fun level => level.val ≤ ℓstar)) ×ˢ
        (Finset.univ : Finset (Fin noiseDim)) := by
    ext q
    simp [levelComponentPositions]
  rw [hpositions, Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

/-- Elementary-symmetric estimate for all active ancestor positions at a common point. -/
theorem sum_activeDetailsUpTo_powersetCard_prod_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T t : ℝ} (hT : 0 < T) (ρ : ℝ) (ℓstar n : ℕ) :
    (∑ s ∈ (activeDetailsUpTo (J := J) (noiseDim := noiseDim) T t ℓstar).powersetCard n,
        ∏ j ∈ s, detailLevelWeight diffusion ρ j) ≤
      ((∑ q ∈ levelComponentPositions J noiseDim ℓstar,
          (2 : ℝ) ^ (-ρ * (q.1.val : ℝ) / 2) *
            columnNorm diffusion q.2 ^ ρ) ^ n) / n.factorial := by
  let active := activeDetailsUpTo (J := J) (noiseDim := noiseDim) T t ℓstar
  let positionSum := ∑ q ∈ levelComponentPositions J noiseDim ℓstar,
    (2 : ℝ) ^ (-ρ * (q.1.val : ℝ) / 2) *
      columnNorm diffusion q.2 ^ ρ
  calc
    (∑ s ∈ active.powersetCard n,
        ∏ j ∈ s, detailLevelWeight diffusion ρ j) ≤
        (∑ j ∈ active, detailLevelWeight diffusion ρ j) ^ n /
          n.factorial :=
      sum_powersetCard_prod_le_sum_pow_div_factorial active
        (detailLevelWeight diffusion ρ) n
        (fun j hj => detailLevelWeight_nonneg diffusion ρ j)
    _ ≤ positionSum ^ n / n.factorial := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀
      · exact Finset.sum_nonneg fun j hj => detailLevelWeight_nonneg diffusion ρ j
      · exact sum_activeDetailsUpTo_weight_le diffusion hT ρ ℓstar

/-- A finite geometric sum is bounded by its infinite-series value. -/
theorem geom_sum_le_one_div_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) :
    (∑ i ∈ Finset.range n, q ^ i) ≤ 1 / (1 - q) := by
  rw [geom_sum_eq (ne_of_lt hq1)]
  have hdenom : 0 ≤ 1 - q := sub_nonneg.mpr hq1.le
  have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
  calc
    (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
      rw [show q ^ n - 1 = -(1 - q ^ n) by ring,
        show q - 1 = -(1 - q) by ring, neg_div_neg_eq]
    _ ≤ 1 / (1 - q) := by
      apply div_le_div_of_nonneg_right _ hdenom
      linarith

/-- The truncated level factor in `A_{ℓ_*}` is bounded by the corresponding infinite
geometric sum. -/
theorem sum_levelFactor_le
    {J : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (ℓstar : ℕ) :
    (∑ level ∈ (Finset.univ : Finset (Fin J)).filter
        (fun level => level.val ≤ ℓstar),
        (2 : ℝ) ^ (-ρ * (level.val : ℝ) / 2)) ≤
      1 / (1 - (2 : ℝ) ^ (-ρ / 2)) := by
  let q : ℝ := (2 : ℝ) ^ (-ρ / 2)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hfactor (level : Fin J) :
      (2 : ℝ) ^ (-ρ * (level.val : ℝ) / 2) = q ^ level.val := by
    rw [← Real.rpow_natCast]
    unfold q
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  calc
    (∑ level ∈ (Finset.univ : Finset (Fin J)).filter
        (fun level => level.val ≤ ℓstar),
        (2 : ℝ) ^ (-ρ * (level.val : ℝ) / 2)) =
        ∑ level ∈ (Finset.univ : Finset (Fin J)).filter
          (fun level => level.val ≤ ℓstar), q ^ level.val := by
            apply Finset.sum_congr rfl
            intro level hlevel
            exact hfactor level
    _ ≤ ∑ i ∈ Finset.range (ℓstar + 1), q ^ i := by
      apply Finset.sum_le_sum_of_injOn (fun level : Fin J => level.val)
      · intro left hleft right hright heq
        exact Fin.ext heq
      · intro i hi
        rcases Finset.mem_image.mp hi with ⟨level, hlevel, rfl⟩
        have hle : level.val ≤ ℓstar := by simpa using hlevel
        exact Finset.mem_range.mpr (by omega)
      · intro level hlevel
        rfl
      · intro i hi hnot
        exact pow_nonneg hq0 i
    _ ≤ 1 / (1 - q) := geom_sum_le_one_div_one_sub hq0 hq1 _

/-- Equation (C.4) in the form needed for one fixed deepest level and common support
point. -/
theorem sum_activeDetailsUpTo_powersetCard_prod_le_theta
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T t : ℝ} (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ)
    (ℓstar n : ℕ) :
    (∑ s ∈ (activeDetailsUpTo (J := J) (noiseDim := noiseDim) T t ℓstar).powersetCard n,
        ∏ j ∈ s, detailLevelWeight diffusion ρ j) ≤
      ((columnRhoSum diffusion ρ /
          (1 - (2 : ℝ) ^ (-ρ / 2))) ^ n) / n.factorial := by
  have hbase :
      (∑ q ∈ levelComponentPositions J noiseDim ℓstar,
          (2 : ℝ) ^ (-ρ * (q.1.val : ℝ) / 2) *
            columnNorm diffusion q.2 ^ ρ) ≤
        columnRhoSum diffusion ρ /
          (1 - (2 : ℝ) ^ (-ρ / 2)) := by
    rw [sum_levelComponentPositions_eq]
    have hlevel := sum_levelFactor_le (J := J) hρ ℓstar
    have htheta := columnRhoSum_nonneg diffusion ρ
    calc
      (∑ level ∈ (Finset.univ : Finset (Fin J)).filter
          (fun level => level.val ≤ ℓstar),
          (2 : ℝ) ^ (-ρ * (level.val : ℝ) / 2)) *
          columnRhoSum diffusion ρ ≤
        (1 / (1 - (2 : ℝ) ^ (-ρ / 2))) *
          columnRhoSum diffusion ρ :=
            mul_le_mul_of_nonneg_right hlevel htheta
      _ = columnRhoSum diffusion ρ /
          (1 - (2 : ℝ) ^ (-ρ / 2)) := by ring
  calc
    (∑ s ∈ (activeDetailsUpTo (J := J) (noiseDim := noiseDim) T t ℓstar).powersetCard n,
        ∏ j ∈ s, detailLevelWeight diffusion ρ j) ≤
      ((∑ q ∈ levelComponentPositions J noiseDim ℓstar,
          (2 : ℝ) ^ (-ρ * (q.1.val : ℝ) / 2) *
            columnNorm diffusion q.2 ^ ρ) ^ n) / n.factorial :=
        sum_activeDetailsUpTo_powersetCard_prod_le diffusion hT ρ ℓstar n
    _ ≤ ((columnRhoSum diffusion ρ /
          (1 - (2 : ℝ) ^ (-ρ / 2))) ^ n) / n.factorial := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀
      · exact Finset.sum_nonneg fun q hq =>
          mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (columnNorm_nonneg diffusion q.2) _)
      · exact hbase

/-- The weighted sum over one deepest-coordinate class is bounded by the elementary
symmetric sum over all ancestor positions. -/
theorem sum_deepestDetailClass_erase_prod_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) (ρ : ℝ) (n : ℕ)
    (jstar : DetailIndex J noiseDim) :
    (∑ details ∈ deepestDetailClass T n jstar,
        ∏ j ∈ details.erase jstar, detailLevelWeight diffusion ρ j) ≤
      ∑ remaining ∈
          (activeDetailsUpTo (J := J) (noiseDim := noiseDim)
            T (jstar.center T) jstar.level.val).powersetCard (n - 1),
        ∏ j ∈ remaining, detailLevelWeight diffusion ρ j := by
  classical
  apply Finset.sum_le_sum_of_injOn
      (fun details : Finset (DetailIndex J noiseDim) => details.erase jstar)
  · intro left hleft right hright herase
    change left.erase jstar = right.erase jstar at herase
    have hleftData := (Finset.mem_filter.mp hleft).2
    have hrightData := (Finset.mem_filter.mp hright).2
    calc
      left = insert jstar (left.erase jstar) :=
        (Finset.insert_erase hleftData.1).symm
      _ = insert jstar (right.erase jstar) := by rw [herase]
      _ = right := Finset.insert_erase hrightData.1
  · intro remaining hremaining
    rcases Finset.mem_image.mp hremaining with ⟨details, hdetails, rfl⟩
    have hbase := (Finset.mem_filter.mp hdetails).1
    have hdata := (Finset.mem_filter.mp hdetails).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact erase_subset_activeDetailsUpTo_center hT details jstar
        hdata.2.1 hdata.1 hdata.2.2
    · have hcard := (Finset.mem_powersetCard.mp hbase).2
      rw [Finset.card_erase_of_mem hdata.1, hcard]
  · intro details hdetails
    rfl
  · intro remaining hremaining hnot
    apply Finset.prod_nonneg
    intro j hj
    exact detailLevelWeight_nonneg diffusion ρ j

/-- The class bound after substituting `Θ_ρ` and the geometric-series estimate. -/
theorem sum_deepestDetailClass_erase_prod_le_theta
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ)
    (jstar : DetailIndex J noiseDim) :
    (∑ details ∈ deepestDetailClass T n jstar,
        ∏ j ∈ details.erase jstar, detailLevelWeight diffusion ρ j) ≤
      ((columnRhoSum diffusion ρ /
          (1 - (2 : ℝ) ^ (-ρ / 2))) ^ (n - 1)) /
        (n - 1).factorial := by
  calc
    (∑ details ∈ deepestDetailClass T n jstar,
        ∏ j ∈ details.erase jstar, detailLevelWeight diffusion ρ j) ≤
      ∑ remaining ∈
          (activeDetailsUpTo (J := J) (noiseDim := noiseDim)
            T (jstar.center T) jstar.level.val).powersetCard (n - 1),
        ∏ j ∈ remaining, detailLevelWeight diffusion ρ j :=
      sum_deepestDetailClass_erase_prod_le diffusion hT ρ n jstar
    _ ≤ ((columnRhoSum diffusion ρ /
          (1 - (2 : ℝ) ^ (-ρ / 2))) ^ (n - 1)) /
        (n - 1).factorial :=
      sum_activeDetailsUpTo_powersetCard_prod_le_theta diffusion hT hρ
        jstar.level.val (n - 1)

/-- Equation (C.1), kept in a factored form suited to the subsequent finite sums. -/
theorem eta_rpow_le_deepest_factored
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 ≤ ρ)
    (details : Finset (DetailIndex J noiseDim)) (n : ℕ)
    (hcard : details.card = n) (jstar : DetailIndex J noiseDim)
    (hjstar : jstar ∈ details) :
    eta diffusion T (detailIndices details) ^ ρ ≤
      (3 / 2 : ℝ) ^ ρ *
        (T / 2 ^ jstar.level.val) ^ ρ *
        ((√T / 2) ^ ρ) ^ n *
        detailLevelWeight diffusion ρ jstar *
        (∏ j ∈ details.erase jstar, detailLevelWeight diffusion ρ j) := by
  have heta := eta_nonneg diffusion hT.le (detailIndices details)
  have hbound := eta_detailIndices_laminar_bound diffusion hT details jstar hjstar
  have hheightProd : 0 ≤ ∏ j ∈ details, detailHeightFactor diffusion T j := by
    exact Finset.prod_nonneg fun j hj => detailHeightFactor_nonneg diffusion T j
  calc
    eta diffusion T (detailIndices details) ^ ρ ≤
        ((3 / 2 : ℝ) * (T / 2 ^ jstar.level.val) *
          ∏ j ∈ details, detailHeightFactor diffusion T j) ^ ρ :=
      Real.rpow_le_rpow heta hbound hρ
    _ = (3 / 2 : ℝ) ^ ρ *
        (T / 2 ^ jstar.level.val) ^ ρ *
        ((√T / 2) ^ ρ) ^ n *
        detailLevelWeight diffusion ρ jstar *
        (∏ j ∈ details.erase jstar, detailLevelWeight diffusion ρ j) := by
      rw [Real.mul_rpow (by positivity) hheightProd]
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      rw [← Real.finsetProd_rpow details
        (detailHeightFactor diffusion T)
        (fun j hj => detailHeightFactor_nonneg diffusion T j) ρ]
      simp_rw [detailHeightFactor_rpow diffusion hT.le ρ]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, hcard]
      rw [← Finset.mul_prod_erase _ _ hjstar]
      ring

/-- The factor in (C.1) that is independent of the remaining `n-1` ancestors. -/
def deepestDetailPrefactor {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T ρ : ℝ) (n : ℕ)
    (jstar : DetailIndex J noiseDim) : ℝ :=
  (3 / 2 : ℝ) ^ ρ *
    (T / 2 ^ jstar.level.val) ^ ρ *
    ((√T / 2) ^ ρ) ^ n *
    detailLevelWeight diffusion ρ jstar

/-- The two level factors attached to the deepest coordinate combine to
`2^{-3ρℓ/2}`. -/
theorem supportRpow_mul_detailLevelWeight
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ) (j : DetailIndex J noiseDim) :
    (T / 2 ^ j.level.val) ^ ρ * detailLevelWeight diffusion ρ j =
      T ^ ρ * (2 : ℝ) ^ (-3 * ρ * (j.level.val : ℝ) / 2) *
        columnNorm diffusion j.component ^ ρ := by
  rw [detailLevelWeight]
  rw [Real.div_rpow hT (by positivity)]
  have hdenom : ((2 : ℝ) ^ j.level.val) ^ ρ =
      (2 : ℝ) ^ ((j.level.val : ℝ) * ρ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hdenom, div_eq_mul_inv]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hcombine :
      (2 : ℝ) ^ (-(j.level.val : ℝ) * ρ) *
          (2 : ℝ) ^ (-ρ * (j.level.val : ℝ) / 2) =
        (2 : ℝ) ^ (-3 * ρ * (j.level.val : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [← hcombine]
  ring

/-- Counting the `2^ℓ` locations converts the deepest-level decay into the outer
geometric ratio from Lemma 4.4. -/
theorem locationCount_mul_deepestLevelFactor (ρ : ℝ) (ℓ : ℕ) :
    ((2 ^ ℓ : ℕ) : ℝ) * (2 : ℝ) ^ (-3 * ρ * (ℓ : ℝ) / 2) =
      ((2 : ℝ) ^ (1 - 3 * ρ / 2)) ^ ℓ := by
  calc
    ((2 ^ ℓ : ℕ) : ℝ) * (2 : ℝ) ^ (-3 * ρ * (ℓ : ℝ) / 2) =
        (2 : ℝ) ^ (ℓ : ℝ) * (2 : ℝ) ^ (-3 * ρ * (ℓ : ℝ) / 2) := by
          rw [Real.rpow_natCast]
          norm_num [Nat.cast_pow]
    _ = (2 : ℝ) ^ ((ℓ : ℝ) + (-3 * ρ * (ℓ : ℝ) / 2)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ ((1 - 3 * ρ / 2) * (ℓ : ℝ)) := by
      congr 1
      ring
    _ = ((2 : ℝ) ^ (1 - 3 * ρ / 2)) ^ ℓ := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Sum of the deepest-coordinate prefactors over all detail indices. -/
theorem sum_deepestDetailPrefactor_eq
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ) (n : ℕ) :
    (∑ jstar : DetailIndex J noiseDim,
        deepestDetailPrefactor diffusion T ρ n jstar) =
      (3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
        columnRhoSum diffusion ρ *
        ∑ level : Fin J, ((2 : ℝ) ^ (1 - 3 * ρ / 2)) ^ level.val := by
  rw [Fintype.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro level hlevel
  have hprefactor (location : Fin (2 ^ level.val)) (component : Fin noiseDim) :
      deepestDetailPrefactor diffusion T ρ n
          ⟨level, (location, component)⟩ =
        (3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n *
          (T ^ ρ * (2 : ℝ) ^ (-3 * ρ * (level.val : ℝ) / 2) *
            columnNorm diffusion component ^ ρ) := by
    unfold deepestDetailPrefactor
    have hsupport := supportRpow_mul_detailLevelWeight diffusion hT ρ
      (show DetailIndex J noiseDim from ⟨level, (location, component)⟩)
    simp only [DetailIndex.level, DetailIndex.component] at hsupport
    calc
      (3 / 2 : ℝ) ^ ρ * (T / 2 ^ level.val) ^ ρ *
          ((√T / 2) ^ ρ) ^ n *
          detailLevelWeight diffusion ρ ⟨level, (location, component)⟩ =
        (3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n *
          ((T / 2 ^ level.val) ^ ρ *
            detailLevelWeight diffusion ρ ⟨level, (location, component)⟩) := by ring
      _ = _ := by rw [hsupport]
  rw [Fintype.sum_prod_type]
  simp_rw [hprefactor]
  rw [← Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hlocation := locationCount_mul_deepestLevelFactor ρ level.val
  unfold columnRhoSum
  calc
    (3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n *
        (T ^ ρ * (2 : ℝ) ^ (-3 * ρ * (level.val : ℝ) / 2) *
          (((2 ^ level.val : ℕ) : ℝ) *
            ∑ i, columnNorm diffusion i ^ ρ)) =
      (3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
        ((((2 ^ level.val : ℕ) : ℝ) *
          (2 : ℝ) ^ (-3 * ρ * (level.val : ℝ) / 2)) *
          ∑ i, columnNorm diffusion i ^ ρ) := by ring
    _ = _ := by rw [hlocation]; ring

/-- The outer level sum is uniformly bounded exactly when `ρ > 2/3`. -/
theorem sum_deepestDetailPrefactor_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) {ρ : ℝ} (hρ : 2 / 3 < ρ) (n : ℕ) :
    (∑ jstar : DetailIndex J noiseDim,
        deepestDetailPrefactor diffusion T ρ n jstar) ≤
      ((3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
        columnRhoSum diffusion ρ) /
          (1 - (2 : ℝ) ^ (1 - 3 * ρ / 2)) := by
  let q : ℝ := (2 : ℝ) ^ (1 - 3 * ρ / 2)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hcommon : 0 ≤
      (3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
        columnRhoSum diffusion ρ := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (by norm_num) ρ)
          (pow_nonneg (Real.rpow_nonneg (by positivity) ρ) n))
        (Real.rpow_nonneg hT ρ))
      (columnRhoSum_nonneg diffusion ρ)
  rw [sum_deepestDetailPrefactor_eq diffusion hT]
  rw [Fin.sum_univ_eq_sum_range]
  have hgeom := geom_sum_le_one_div_one_sub hq0 hq1 J
  change _ * (∑ i ∈ Finset.range J, q ^ i) ≤ _
  calc
    ((3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
        columnRhoSum diffusion ρ) * (∑ i ∈ Finset.range J, q ^ i) ≤
      ((3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
        columnRhoSum diffusion ρ) * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left hgeom hcommon
    _ = ((3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
        columnRhoSum diffusion ρ) / (1 - q) := by ring

theorem deepestDetailPrefactor_nonneg
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ) (n : ℕ)
    (jstar : DetailIndex J noiseDim) :
    0 ≤ deepestDetailPrefactor diffusion T ρ n jstar := by
  unfold deepestDetailPrefactor
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (by norm_num) ρ)
        (Real.rpow_nonneg (div_nonneg hT (by positivity)) ρ))
      (pow_nonneg (Real.rpow_nonneg (by positivity) ρ) n))
    (detailLevelWeight_nonneg diffusion ρ jstar)

/-- Sum of `η^ρ` over one deepest-coordinate class. -/
theorem sum_deepestDetailClass_eta_rpow_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (n : ℕ)
    (jstar : DetailIndex J noiseDim) :
    (∑ details ∈ deepestDetailClass T n jstar,
        eta diffusion T (detailIndices details) ^ ρ) ≤
      deepestDetailPrefactor diffusion T ρ n jstar *
        (((columnRhoSum diffusion ρ /
            (1 - (2 : ℝ) ^ (-ρ / 2))) ^ (n - 1)) /
          (n - 1).factorial) := by
  classical
  let prefactor := deepestDetailPrefactor diffusion T ρ n jstar
  have hprefactor : 0 ≤ prefactor :=
    deepestDetailPrefactor_nonneg diffusion hT.le ρ n jstar
  calc
    (∑ details ∈ deepestDetailClass T n jstar,
        eta diffusion T (detailIndices details) ^ ρ) ≤
      ∑ details ∈ deepestDetailClass T n jstar,
        prefactor *
          (∏ j ∈ details.erase jstar, detailLevelWeight diffusion ρ j) := by
        apply Finset.sum_le_sum
        intro details hdetails
        have hbase := (Finset.mem_filter.mp hdetails).1
        have hdata := (Finset.mem_filter.mp hdetails).2
        have hcard := (Finset.mem_powersetCard.mp hbase).2
        simpa [prefactor, deepestDetailPrefactor] using
          eta_rpow_le_deepest_factored diffusion hT hρ.le details n hcard
            jstar hdata.1
    _ = prefactor *
        (∑ details ∈ deepestDetailClass T n jstar,
          ∏ j ∈ details.erase jstar, detailLevelWeight diffusion ρ j) := by
      rw [Finset.mul_sum]
    _ ≤ prefactor *
        (((columnRhoSum diffusion ρ /
            (1 - (2 : ℝ) ^ (-ρ / 2))) ^ (n - 1)) /
          (n - 1).factorial) := by
      exact mul_le_mul_of_nonneg_left
        (sum_deepestDetailClass_erase_prod_le_theta diffusion hT hρ n jstar)
        hprefactor

/-- If the detail supports have no common interior point, the corresponding time factor
vanishes. -/
theorem eta_detail_eq_zero_of_not_supportsMeet
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) (details : Finset (DetailIndex J noiseDim))
    (hmeet : ¬ detailSupportsMeet T details) :
    eta diffusion T (detailIndices details) = 0 := by
  apply eta_detail_eq_zero_of_supportIntersection_eq_empty diffusion hT details
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨t, ht⟩
  apply hmeet
  refine ⟨t, ?_⟩
  intro j hj
  have ht' : ∀ i : ↥details, t ∈ i.1.supportInterior T := by
    simpa [detailSupportIntersection] using ht
  exact ht' ⟨j, hj⟩

/-- Every nonzero `n`-element detail set is covered by at least one class indexed by a
deepest coordinate.  Summing over all such coordinates may overcount ties, which is harmless
for the upper bound. -/
theorem sum_detail_powersetCard_eta_rpow_le_sum_deepestClasses
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (n : ℕ) (hn : 0 < n) :
    (∑ details ∈ (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
        eta diffusion T (detailIndices details) ^ ρ) ≤
      ∑ jstar : DetailIndex J noiseDim,
        ∑ details ∈ deepestDetailClass T n jstar,
          eta diffusion T (detailIndices details) ^ ρ := by
  classical
  let allDetails := (Finset.univ : Finset (DetailIndex J noiseDim))
  let value : Finset (DetailIndex J noiseDim) → ℝ := fun details =>
    eta diffusion T (detailIndices details) ^ ρ
  have hvalueNonneg (details : Finset (DetailIndex J noiseDim)) :
      0 ≤ value details :=
    Real.rpow_nonneg (eta_nonneg diffusion hT.le (detailIndices details)) ρ
  have hcover : ∀ details ∈ allDetails.powersetCard n,
      value details ≤ ∑ jstar : DetailIndex J noiseDim,
        if details ∈ deepestDetailClass T n jstar then value details else 0 := by
    intro details hdetails
    by_cases hmeet : detailSupportsMeet T details
    · have hcard : details.card = n := (Finset.mem_powersetCard.mp hdetails).2
      have hnonempty : details.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨jstar, hjstar, hmax⟩ :=
        Finset.exists_max_image details (fun j => j.level.val) hnonempty
      have hclass : details ∈ deepestDetailClass T n jstar := by
        apply Finset.mem_filter.mpr
        exact ⟨hdetails, hjstar, hmax, hmeet⟩
      calc
        value details = if details ∈ deepestDetailClass T n jstar
            then value details else 0 := by rw [if_pos hclass]
        _ ≤ ∑ candidate : DetailIndex J noiseDim,
            if details ∈ deepestDetailClass T n candidate
              then value details else 0 := by
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun candidate : DetailIndex J noiseDim =>
              if details ∈ deepestDetailClass T n candidate
                then value details else 0)
            (fun candidate hcandidate => by
              split_ifs
              · exact hvalueNonneg details
              · rfl)
            (Finset.mem_univ jstar)
    · have hzero := eta_detail_eq_zero_of_not_supportsMeet diffusion hT details hmeet
      have hvalueZero : value details = 0 := by
        simp [value, hzero, Real.zero_rpow hρ.ne']
      rw [hvalueZero]
      exact Finset.sum_nonneg fun jstar hjstar => by
        split_ifs <;> rfl
  calc
    (∑ details ∈ allDetails.powersetCard n, value details) ≤
        ∑ details ∈ allDetails.powersetCard n,
          ∑ jstar : DetailIndex J noiseDim,
            if details ∈ deepestDetailClass T n jstar then value details else 0 :=
      Finset.sum_le_sum hcover
    _ = ∑ jstar : DetailIndex J noiseDim,
        ∑ details ∈ deepestDetailClass T n jstar, value details := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro jstar hjstar
      rw [← Finset.sum_filter]
      have hsubset : deepestDetailClass T n jstar ⊆ allDetails.powersetCard n := by
        intro details hdetails
        exact (Finset.mem_filter.mp hdetails).1
      have hfilter : (allDetails.powersetCard n).filter
          (fun details => details ∈ deepestDetailClass T n jstar) =
          deepestDetailClass T n jstar := by
        ext details
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨hsubset h, h⟩
      rw [hfilter]

/-- Fixed-cardinality detail-subset estimate in the factored form obtained directly from
the proof of Lemma 4.4. -/
theorem detail_powersetCard_eta_rpow_le_factored
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 2 / 3 < ρ) (n : ℕ) (hn : 0 < n) :
    (∑ details ∈ (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
        eta diffusion T (detailIndices details) ^ ρ) ≤
      (((3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
          columnRhoSum diffusion ρ) /
            (1 - (2 : ℝ) ^ (1 - 3 * ρ / 2))) *
        (((columnRhoSum diffusion ρ /
            (1 - (2 : ℝ) ^ (-ρ / 2))) ^ (n - 1)) /
          (n - 1).factorial) := by
  let ancestorBound :=
    ((columnRhoSum diffusion ρ /
      (1 - (2 : ℝ) ^ (-ρ / 2))) ^ (n - 1)) / (n - 1).factorial
  have hancestor : 0 ≤ ancestorBound := by
    unfold ancestorBound
    have hq : (2 : ℝ) ^ (-ρ / 2) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      linarith
    exact div_nonneg
      (pow_nonneg
        (div_nonneg (columnRhoSum_nonneg diffusion ρ)
          (sub_nonneg.mpr hq.le)) (n - 1))
      (Nat.cast_nonneg _)
  calc
    (∑ details ∈ (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
        eta diffusion T (detailIndices details) ^ ρ) ≤
      ∑ jstar : DetailIndex J noiseDim,
        ∑ details ∈ deepestDetailClass T n jstar,
          eta diffusion T (detailIndices details) ^ ρ :=
      sum_detail_powersetCard_eta_rpow_le_sum_deepestClasses
        diffusion hT (by linarith) n hn
    _ ≤ ∑ jstar : DetailIndex J noiseDim,
        deepestDetailPrefactor diffusion T ρ n jstar * ancestorBound := by
      apply Finset.sum_le_sum
      intro jstar hjstar
      exact sum_deepestDetailClass_eta_rpow_le diffusion hT (by linarith) n jstar
    _ = (∑ jstar : DetailIndex J noiseDim,
        deepestDetailPrefactor diffusion T ρ n jstar) * ancestorBound := by
      rw [Finset.sum_mul]
    _ ≤ (((3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ *
          columnRhoSum diffusion ρ) /
            (1 - (2 : ℝ) ^ (1 - 3 * ρ / 2))) * ancestorBound :=
      mul_le_mul_of_nonneg_right
        (sum_deepestDetailPrefactor_le diffusion hT.le hρ n) hancestor

/-- The geometric factor `A_{ρ,T}` in the proof of Lemma 4.4.  This expression is
algebraically identical to the paper's `2^{-ρ}T^{ρ/2}/(1-2^{-ρ/2})`. -/
def detailSummabilityA (T ρ : ℝ) : ℝ :=
  (√T / 2) ^ ρ / (1 - (2 : ℝ) ^ (-ρ / 2))

/-- The prefactor `B_{ρ,T}` in the proof of Lemma 4.4. -/
def detailSummabilityB (T ρ : ℝ) : ℝ :=
  (3 / 2 : ℝ) ^ ρ * T ^ ρ *
    (1 - (2 : ℝ) ^ (-ρ / 2)) /
      (1 - (2 : ℝ) ^ (1 - 3 * ρ / 2))

/-- The paper's dimension-independent constant `C_{ρ,T}`. -/
def detailSummabilityConstant (T ρ : ℝ) : ℝ :=
  detailSummabilityA T ρ * max 1 (detailSummabilityB T ρ)

private theorem factored_detail_bound_eq
    {a c t θ din dout : ℝ} (hdin : din ≠ 0) (n : ℕ) (hn : 0 < n) :
    (c * a ^ n * t * θ / dout) *
        ((θ / din) ^ (n - 1) / (n - 1).factorial) =
      ((c * t * din / dout) * (a / din) ^ n * θ ^ n) /
        (n - 1).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one, pow_succ]
  field_simp
  ring

private theorem mul_pow_le_mul_max_pow
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) (hn : 0 < n) :
    b * a ^ n ≤ (a * max 1 b) ^ n := by
  let M := max 1 b
  have hM : 1 ≤ M := le_max_left _ _
  have hbM : b ≤ M := le_max_right _ _
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hMpow : M ≤ M ^ (m + 1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ hM (n := m)]
  rw [mul_pow]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right (hbM.trans hMpow) (pow_nonneg ha (m + 1))

theorem detailSummabilityA_nonneg {T ρ : ℝ} (hT : 0 ≤ T) (hρ : 0 < ρ) :
    0 ≤ detailSummabilityA T ρ := by
  unfold detailSummabilityA
  have hq : (2 : ℝ) ^ (-ρ / 2) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  exact div_nonneg (Real.rpow_nonneg (by positivity) _)
    (sub_nonneg.mpr hq.le)

theorem detailSummabilityB_nonneg {T ρ : ℝ} (hT : 0 ≤ T)
    (hρ : 2 / 3 < ρ) :
    0 ≤ detailSummabilityB T ρ := by
  unfold detailSummabilityB
  have hinner : (2 : ℝ) ^ (-ρ / 2) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have houter : (2 : ℝ) ^ (1 - 3 * ρ / 2) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hT _))
      (sub_nonneg.mpr hinner.le))
    (sub_nonneg.mpr houter.le)

/-- Lemma 4.4, Equation (4.12), with the paper's constant and factor `3/2`. -/
theorem detail_powersetCard_eta_rpow_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T ρ : ℝ} (hT : 0 < T) (hρ : 2 / 3 < ρ) (n : ℕ) (hn : 0 < n) :
    (∑ details ∈ (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
        eta diffusion T (detailIndices details) ^ ρ) ≤
      (detailSummabilityConstant T ρ * columnRhoSum diffusion ρ) ^ n /
        (n - 1).factorial := by
  have hρpos : 0 < ρ := by linarith
  have hinner : 1 - (2 : ℝ) ^ (-ρ / 2) ≠ 0 := by
    have hq : (2 : ℝ) ^ (-ρ / 2) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      linarith
    linarith
  have hfactored := detail_powersetCard_eta_rpow_le_factored
    (J := J) diffusion hT hρ n hn
  let A := detailSummabilityA T ρ
  let B := detailSummabilityB T ρ
  let Θ := columnRhoSum diffusion ρ
  have hrewrite :
      (((3 / 2 : ℝ) ^ ρ * ((√T / 2) ^ ρ) ^ n * T ^ ρ * Θ) /
          (1 - (2 : ℝ) ^ (1 - 3 * ρ / 2))) *
        (((Θ / (1 - (2 : ℝ) ^ (-ρ / 2))) ^ (n - 1)) /
          (n - 1).factorial) =
      (B * A ^ n * Θ ^ n) / (n - 1).factorial := by
    simpa [A, B, Θ, detailSummabilityA, detailSummabilityB, mul_assoc] using
      factored_detail_bound_eq
        (a := (√T / 2) ^ ρ) (c := (3 / 2 : ℝ) ^ ρ)
        (t := T ^ ρ) (θ := Θ)
        (din := 1 - (2 : ℝ) ^ (-ρ / 2))
        (dout := 1 - (2 : ℝ) ^ (1 - 3 * ρ / 2)) hinner n hn
  rw [hrewrite] at hfactored
  calc
    (∑ details ∈ (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
        eta diffusion T (detailIndices details) ^ ρ) ≤
      (B * A ^ n * Θ ^ n) / (n - 1).factorial := hfactored
    _ ≤ ((A * max 1 B) ^ n * Θ ^ n) / (n - 1).factorial := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_pow_le_mul_max_pow
          (detailSummabilityA_nonneg hT.le hρpos)
          (detailSummabilityB_nonneg hT.le hρ) n hn)
        (pow_nonneg (columnRhoSum_nonneg diffusion ρ) n)
    _ = (detailSummabilityConstant T ρ * columnRhoSum diffusion ρ) ^ n /
        (n - 1).factorial := by
      simp [A, B, Θ, detailSummabilityConstant, mul_pow]


end

end TimeDependentLattice.Regularity
