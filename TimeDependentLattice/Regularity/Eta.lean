/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.BrownianBridge.Coefficients
import TimeDependentLattice.BrownianBridge.Path

/-!
# Time-factor sums for the derivative majorant

This file defines the quantity `η_m(S)` from Equation (4.9) for the dyadic grid `m = 2^J`.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open scoped BigOperators
open TimeDependentLattice
open TimeDependentLattice.BrownianBridge

/-- The paper's time-factor
`η_m(S) = h ∑_{i=0}^{m-1} ∏_{j∈S} ‖ξ_j(t_i)‖`. -/
def eta {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (support : Finset (Index J noiseDim)) : ℝ :=
  stepSize T J * ∑ i ∈ Finset.range (numSteps J),
    ∏ j ∈ support, ‖diffusionCoefficient diffusion T j (gridTime T J i)‖

/-- `η_m(S)` is nonnegative for nonnegative terminal time. -/
theorem eta_nonneg {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) {T : ℝ} (hT : 0 ≤ T)
    (support : Finset (Index J noiseDim)) :
    0 ≤ eta diffusion T support := by
  unfold eta
  apply mul_nonneg
  · exact div_nonneg hT (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro i hi
    apply Finset.prod_nonneg
    intro j hj
    exact norm_nonneg _

/-- The empty-set value, useful only while reorganizing finite sums. -/
@[simp]
theorem eta_empty {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) :
    eta (J := J) diffusion T ∅ = T := by
  simp only [eta, stepSize, numSteps, Finset.prod_empty, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp

/-- The column norm `σ_r` used by the paper. -/
def columnNorm {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (r : Fin noiseDim) : ℝ :=
  ‖diffusion (noiseBasis r)‖

theorem columnNorm_nonneg {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (r : Fin noiseDim) :
    0 ≤ columnNorm diffusion r := norm_nonneg _

/-- The endpoint factor `√T σ_r`. -/
def endpointFactor {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (r : Fin noiseDim) : ℝ :=
  √T * columnNorm diffusion r

/-- Uniform height of the vector-valued detail hat attached to `j`. -/
def detailHeightFactor {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (j : DetailIndex J noiseDim) : ℝ :=
  √T / 2 * (2 : ℝ) ^ (-(j.level.val : ℝ) / 2) *
    columnNorm diffusion j.component

theorem endpointFactor_nonneg {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (r : Fin noiseDim) :
    0 ≤ endpointFactor diffusion T r := by
  unfold endpointFactor
  exact mul_nonneg (Real.sqrt_nonneg T) (norm_nonneg _)

theorem detailHeightFactor_nonneg {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (j : DetailIndex J noiseDim) :
    0 ≤ detailHeightFactor diffusion T j := by
  unfold detailHeightFactor columnNorm
  positivity

/-- Vector form of the level-dependent detail height bound. -/
theorem norm_diffusionCoefficient_detail_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (j : DetailIndex J noiseDim) (t : ℝ) :
    ‖diffusionCoefficient diffusion T (Sum.inr j) t‖ ≤
      detailHeightFactor diffusion T j := by
  rw [diffusionCoefficient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (coefficient_detail_nonneg j t)]
  exact mul_le_mul_of_nonneg_right (coefficient_detail_le j t)
    (norm_nonneg _)

/-- At a dyadic grid point in `[0,T]`, an endpoint coefficient is bounded by its terminal
factor `√T σ_r`. -/
theorem norm_diffusionCoefficient_endpoint_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (r : Fin noiseDim) (i : ℕ) (hi : i ≤ numSteps J) :
    ‖diffusionCoefficient (J := J) diffusion T (Sum.inl r) (gridTime T J i)‖ ≤
      endpointFactor diffusion T r := by
  rw [diffusionCoefficient, coefficient_endpoint, norm_smul, Real.norm_eq_abs]
  have hsteps : (0 : ℝ) < numSteps J := by
    exact_mod_cast numSteps_pos J
  have hgridNonneg : 0 ≤ gridTime T J i := by
    unfold gridTime stepSize
    positivity
  have hgridLe : gridTime T J i ≤ T := by
    unfold gridTime stepSize
    have hiReal : (i : ℝ) ≤ numSteps J := by exact_mod_cast hi
    calc
      (i : ℝ) * (T / numSteps J) = T * ((i : ℝ) / numSteps J) := by ring
      _ ≤ T * ((numSteps J : ℝ) / numSteps J) := by gcongr
      _ = T := by field_simp
  have hsqrt : 0 ≤ √T := Real.sqrt_nonneg T
  by_cases hTzero : T = 0
  · subst T
    simp [gridTime, stepSize, endpointFactor, columnNorm]
  · have hsqrtPos : 0 < √T := Real.sqrt_pos.2 (lt_of_le_of_ne hT (Ne.symm hTzero))
    rw [abs_of_nonneg (div_nonneg hgridNonneg hsqrt), endpointFactor, columnNorm]
    simp only [Index.component]
    gcongr
    rw [div_le_iff₀ hsqrtPos]
    calc
      gridTime T J i ≤ T := hgridLe
      _ = √T * √T := by rw [Real.mul_self_sqrt hT]

/-- Endpoint coordinates as a finset of full Brownian-bridge indices. -/
def endpointIndices {J noiseDim : ℕ} (endpoints : Finset (Fin noiseDim)) :
    Finset (Index J noiseDim) :=
  endpoints.map Function.Embedding.inl

/-- Detail coordinates as a finset of full Brownian-bridge indices. -/
def detailIndices {J noiseDim : ℕ} (details : Finset (DetailIndex J noiseDim)) :
    Finset (Index J noiseDim) :=
  details.map Function.Embedding.inr

/-- Intersection of the open support intervals carried by a finite detail set. -/
def detailSupportIntersection {J noiseDim : ℕ} (T : ℝ)
    (details : Finset (DetailIndex J noiseDim)) : Set ℝ :=
  ⋂ j : ↥details, j.1.supportInterior T

theorem endpointIndices_disjoint_detailIndices {J noiseDim : ℕ}
    (endpoints : Finset (Fin noiseDim)) (details : Finset (DetailIndex J noiseDim)) :
    Disjoint (endpointIndices (J := J) endpoints) (detailIndices details) := by
  rw [Finset.disjoint_left]
  intro j hjEndpoint hjDetail
  rcases Finset.mem_map.mp hjEndpoint with ⟨r, hr, rfl⟩
  simp [detailIndices] at hjDetail

/-- First assertion of Lemma 4.4: if the detail support interiors have empty intersection,
then every grid-point product, and hence `η`, vanishes. -/
theorem eta_detail_eq_zero_of_supportIntersection_eq_empty
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) (details : Finset (DetailIndex J noiseDim))
    (hempty : detailSupportIntersection T details = ∅) :
    eta diffusion T (detailIndices details) = 0 := by
  unfold eta
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i hi
  let t := gridTime T J i
  have htNot : t ∉ detailSupportIntersection T details := by
    rw [hempty]
    simp
  simp only [detailSupportIntersection, Set.mem_iInter, not_forall] at htNot
  rcases htNot with ⟨j, hj⟩
  apply Finset.prod_eq_zero (i := Sum.inr j.1)
  · exact Finset.mem_map.mpr ⟨j.1, j.2, rfl⟩
  · have hcoefficient :=
      coefficient_detail_eq_zero_of_not_mem_supportInterior hT j.1 hj
    change ‖coefficient T (Sum.inr j.1) t •
      diffusion (noiseBasis (Index.component (Sum.inr j.1)))‖ = 0
    rw [hcoefficient, zero_smul, norm_zero]

/-- At a fixed dyadic level and Brownian component, two detail coordinates whose open
supports meet are equal.  This is the uniqueness of the ancestor position used in the
summation part of Lemma 4.4. -/
theorem detail_eq_of_same_level_component_of_common_support
    {J noiseDim : ℕ} {T t : ℝ} (hT : 0 < T)
    (j j' : DetailIndex J noiseDim)
    (hlevel : j.level = j'.level) (hcomponent : j.component = j'.component)
    (hj : t ∈ j.supportInterior T) (hj' : t ∈ j'.supportInterior T) :
    j = j' := by
  rcases j with ⟨level, location, component⟩
  rcases j' with ⟨level', location', component'⟩
  change level = level' at hlevel
  subst level'
  change component = component' at hcomponent
  subst component'
  change (location.val : ℝ) * T / 2 ^ level.val < t ∧
    t < (location.val + 1 : ℝ) * T / 2 ^ level.val at hj
  change (location'.val : ℝ) * T / 2 ^ level.val < t ∧
    t < (location'.val + 1 : ℝ) * T / 2 ^ level.val at hj'
  have hlocation : location.val = location'.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsucc : location.val + 1 ≤ location'.val := by omega
      have hdenom : (0 : ℝ) < 2 ^ level.val := by positivity
      have horder : (location.val + 1 : ℝ) * T / 2 ^ level.val ≤
          (location'.val : ℝ) * T / 2 ^ level.val := by
        apply div_le_div_of_nonneg_right _ hdenom.le
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsucc) hT.le
      exact (not_lt_of_ge horder) (lt_trans hj'.1 hj.2)
    · have hsucc : location'.val + 1 ≤ location.val := by omega
      have hdenom : (0 : ℝ) < 2 ^ level.val := by positivity
      have horder : (location'.val + 1 : ℝ) * T / 2 ^ level.val ≤
          (location.val : ℝ) * T / 2 ^ level.val := by
        apply div_le_div_of_nonneg_right _ hdenom.le
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsucc) hT.le
      exact (not_lt_of_ge horder) (lt_trans hj.1 hj'.2)
  congr 2
  exact Fin.ext hlocation

/-- Dyadic laminarity: if two detail supports meet and the first coordinate is at a
coarser level, then it contains the second support. -/
theorem detailSupportInterior_subset_of_level_le_of_common_support
    {J noiseDim : ℕ} {T t : ℝ} (hT : 0 < T)
    (coarse fine : DetailIndex J noiseDim)
    (hlevel : coarse.level.val ≤ fine.level.val)
    (hcoarse : t ∈ coarse.supportInterior T)
    (hfine : t ∈ fine.supportInterior T) :
    fine.supportInterior T ⊆ coarse.supportInterior T := by
  rcases coarse with ⟨level, location, component⟩
  rcases fine with ⟨level', location', component'⟩
  change level.val ≤ level'.val at hlevel
  change (location.val : ℝ) * T / 2 ^ level.val < t ∧
    t < (location.val + 1 : ℝ) * T / 2 ^ level.val at hcoarse
  change (location'.val : ℝ) * T / 2 ^ level'.val < t ∧
    t < (location'.val + 1 : ℝ) * T / 2 ^ level'.val at hfine
  have hsmall : (0 : ℝ) < 2 ^ level.val := by positivity
  have hlarge : (0 : ℝ) < 2 ^ level'.val := by positivity
  have hcommon : 0 < T * (2 : ℝ) ^ level.val := mul_pos hT hsmall
  have hpowNat : 2 ^ level'.val =
      2 ^ level.val * 2 ^ (level'.val - level.val) := by
    rw [← pow_add, Nat.add_sub_of_le hlevel]
  have hpowReal : (2 : ℝ) ^ level'.val =
      (2 : ℝ) ^ level.val * (2 : ℝ) ^ (level'.val - level.val) := by
    exact_mod_cast hpowNat
  have hleft :
      (location.val : ℝ) * T / 2 ^ level.val ≤
        (location'.val : ℝ) * T / 2 ^ level'.val := by
    by_contra hnot
    have hlt : (location'.val : ℝ) * T / 2 ^ level'.val <
        (location.val : ℝ) * T / 2 ^ level.val := lt_of_not_ge hnot
    have hcross := (div_lt_div_iff₀ hlarge hsmall).mp hlt
    have hscaledReal : (location'.val : ℝ) <
        location.val * (2 : ℝ) ^ (level'.val - level.val) := by
      rw [hpowReal] at hcross
      have hmul : (location'.val : ℝ) * (T * (2 : ℝ) ^ level.val) <
          (location.val * (2 : ℝ) ^ (level'.val - level.val)) *
            (T * (2 : ℝ) ^ level.val) := by
        convert hcross using 1 <;> ring
      exact lt_of_mul_lt_mul_right hmul hcommon.le
    have hscaledNat : location'.val <
        location.val * 2 ^ (level'.val - level.val) := by
      exact_mod_cast hscaledReal
    have hsucc : location'.val + 1 ≤
        location.val * 2 ^ (level'.val - level.val) := by omega
    have hrightLe :
        (location'.val + 1 : ℝ) * T / 2 ^ level'.val ≤
          (location.val : ℝ) * T / 2 ^ level.val := by
      apply (div_le_div_iff₀ hlarge hsmall).mpr
      rw [hpowReal]
      have hsuccReal : (location'.val + 1 : ℝ) ≤
          location.val * (2 : ℝ) ^ (level'.val - level.val) := by
        exact_mod_cast hsucc
      have hmul := mul_le_mul_of_nonneg_right hsuccReal hcommon.le
      convert hmul using 1 <;> ring
    exact (not_lt_of_ge hrightLe) (lt_trans hcoarse.1 hfine.2)
  have hright :
      (location'.val + 1 : ℝ) * T / 2 ^ level'.val ≤
        (location.val + 1 : ℝ) * T / 2 ^ level.val := by
    by_contra hnot
    have hlt : (location.val + 1 : ℝ) * T / 2 ^ level.val <
        (location'.val + 1 : ℝ) * T / 2 ^ level'.val := lt_of_not_ge hnot
    have hcross := (div_lt_div_iff₀ hsmall hlarge).mp hlt
    have hscaledReal : (location.val + 1 : ℝ) *
        (2 : ℝ) ^ (level'.val - level.val) < location'.val + 1 := by
      rw [hpowReal] at hcross
      have hmul : ((location.val + 1 : ℝ) *
          (2 : ℝ) ^ (level'.val - level.val)) *
            (T * (2 : ℝ) ^ level.val) <
          (location'.val + 1 : ℝ) * (T * (2 : ℝ) ^ level.val) := by
        convert hcross using 1 <;> ring
      exact lt_of_mul_lt_mul_right hmul hcommon.le
    have hscaledNat : (location.val + 1) *
        2 ^ (level'.val - level.val) < location'.val + 1 := by
      exact_mod_cast hscaledReal
    have hle : (location.val + 1) *
        2 ^ (level'.val - level.val) ≤ location'.val := by omega
    have hrightLe :
        (location.val + 1 : ℝ) * T / 2 ^ level.val ≤
          (location'.val : ℝ) * T / 2 ^ level'.val := by
      apply (div_le_div_iff₀ hsmall hlarge).mpr
      rw [hpowReal]
      have hleReal : (location.val + 1 : ℝ) *
          (2 : ℝ) ^ (level'.val - level.val) ≤ location'.val := by
        exact_mod_cast hle
      have hmul := mul_le_mul_of_nonneg_right hleReal hcommon.le
      convert hmul using 1 <;> ring
    exact (not_lt_of_ge hrightLe) (lt_trans hfine.1 hcoarse.2)
  intro x hx
  change (location.val : ℝ) * T / 2 ^ level.val < x ∧
    x < (location.val + 1 : ℝ) * T / 2 ^ level.val
  change (location'.val : ℝ) * T / 2 ^ level'.val < x ∧
    x < (location'.val + 1 : ℝ) * T / 2 ^ level'.val at hx
  exact ⟨lt_of_le_of_lt hleft hx.1, lt_of_lt_of_le hx.2 hright⟩

/-- At a dyadic grid point, membership in a detail support interval is the corresponding
strict inequality between integer grid indices. -/
theorem gridTime_mem_detailSupportInterior_iff
    {J noiseDim : ℕ} {T : ℝ} (hT : 0 < T)
    (j : DetailIndex J noiseDim) (i : ℕ) :
    gridTime T J i ∈ j.supportInterior T ↔
      j.location.val * 2 ^ (J - j.level.val) < i ∧
        i < (j.location.val + 1) * 2 ^ (J - j.level.val) := by
  have hlevel : j.level.val ≤ J := Nat.le_of_lt j.level.isLt
  have hpowEq : 2 ^ J = 2 ^ j.level.val * 2 ^ (J - j.level.val) := by
    rw [← pow_add, Nat.add_sub_of_le hlevel]
  have hsmall : (0 : ℝ) < (2 : ℝ) ^ j.level.val := by positivity
  have hlarge : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  simp only [DetailIndex.supportInterior, Set.mem_Ioo,
    DetailIndex.leftEndpoint, DetailIndex.rightEndpoint,
    gridTime, stepSize, numSteps]
  norm_num [Nat.cast_pow]
  change
    j.location.val * T / 2 ^ j.level.val <
          i * (T / 2 ^ J) ∧
        i * (T / 2 ^ J) <
          (j.location.val + 1) * T / 2 ^ j.level.val ↔ _
  constructor
  · rintro ⟨hleft, hright⟩
    have hleftRatio :
        (j.location.val : ℝ) / (2 : ℝ) ^ j.level.val <
          (i : ℝ) / (2 : ℝ) ^ J := by
      apply lt_of_mul_lt_mul_left (a := T) (b :=
        (j.location.val : ℝ) / (2 : ℝ) ^ j.level.val) (c :=
        (i : ℝ) / (2 : ℝ) ^ J) (a0 := hT.le)
      convert hleft using 1 <;> ring
    have hrightRatio :
        (i : ℝ) / (2 : ℝ) ^ J <
          (j.location.val + 1 : ℝ) / (2 : ℝ) ^ j.level.val := by
      apply lt_of_mul_lt_mul_left (a := T) (b :=
        (i : ℝ) / (2 : ℝ) ^ J) (c :=
        (j.location.val + 1 : ℝ) / (2 : ℝ) ^ j.level.val) (a0 := hT.le)
      convert hright using 1 <;> ring
    have hleftCross := (div_lt_div_iff₀ hsmall hlarge).mp hleftRatio
    have hrightCross := (div_lt_div_iff₀ hlarge hsmall).mp hrightRatio
    have hleftReal :
        (j.location.val * 2 ^ (J - j.level.val) : ℕ) < i := by
      exact_mod_cast (show
        (j.location.val : ℝ) * (2 : ℝ) ^ (J - j.level.val) < i by
          rw [show (2 : ℝ) ^ J = (2 : ℝ) ^ j.level.val *
            (2 : ℝ) ^ (J - j.level.val) by
              exact_mod_cast hpowEq] at hleftCross
          nlinarith [hsmall])
    have hrightReal :
        i < (j.location.val + 1) * 2 ^ (J - j.level.val) := by
      exact_mod_cast (show
        (i : ℝ) < (j.location.val + 1) * (2 : ℝ) ^ (J - j.level.val) by
          rw [show (2 : ℝ) ^ J = (2 : ℝ) ^ j.level.val *
            (2 : ℝ) ^ (J - j.level.val) by
              exact_mod_cast hpowEq] at hrightCross
          nlinarith [hsmall])
    exact ⟨hleftReal, hrightReal⟩
  · rintro ⟨hleft, hright⟩
    have hleftReal :
        (j.location.val : ℝ) * (2 : ℝ) ^ (J - j.level.val) < i := by
      exact_mod_cast hleft
    have hrightReal :
        (i : ℝ) < (j.location.val + 1) * (2 : ℝ) ^ (J - j.level.val) := by
      exact_mod_cast hright
    constructor
    · have hratio :
          (j.location.val : ℝ) / (2 : ℝ) ^ j.level.val <
            (i : ℝ) / (2 : ℝ) ^ J := by
        apply (div_lt_div_iff₀ hsmall hlarge).mpr
        rw [show (2 : ℝ) ^ J = (2 : ℝ) ^ j.level.val *
          (2 : ℝ) ^ (J - j.level.val) by exact_mod_cast hpowEq]
        nlinarith [hsmall]
      have hmul := mul_lt_mul_of_pos_left hratio hT
      convert hmul using 1 <;> ring
    · have hratio :
          (i : ℝ) / (2 : ℝ) ^ J <
            (j.location.val + 1 : ℝ) / (2 : ℝ) ^ j.level.val := by
        apply (div_lt_div_iff₀ hlarge hsmall).mpr
        rw [show (2 : ℝ) ^ J = (2 : ℝ) ^ j.level.val *
          (2 : ℝ) ^ (J - j.level.val) by exact_mod_cast hpowEq]
        nlinarith [hsmall]
      have hmul := mul_lt_mul_of_pos_left hratio hT
      convert hmul using 1 <;> ring

/-- Grid indices at which the detail hat can be nonzero. -/
noncomputable def detailActiveGrid {J noiseDim : ℕ} (T : ℝ)
    (j : DetailIndex J noiseDim) : Finset ℕ := by
  classical
  exact (Finset.range (numSteps J)).filter fun i =>
    gridTime T J i ∈ j.supportInterior T

/-- A level-`ℓ` detail hat is active at no more than `2^(J-ℓ)` grid points. -/
theorem card_detailActiveGrid_le
    {J noiseDim : ℕ} {T : ℝ} (hT : 0 < T) (j : DetailIndex J noiseDim) :
    (detailActiveGrid T j).card ≤ 2 ^ (J - j.level.val) := by
  let q := 2 ^ (J - j.level.val)
  let a := j.location.val * q
  let b := (j.location.val + 1) * q
  have hsubset : detailActiveGrid T j ⊆ Finset.Ioo a b := by
    intro i hi
    have hactive : gridTime T J i ∈ j.supportInterior T := by
      have hmem : i < numSteps J ∧
          gridTime T J i ∈ j.supportInterior T := by
        simpa [detailActiveGrid] using hi
      exact hmem.2
    have hbounds := (gridTime_mem_detailSupportInterior_iff hT j i).mp hactive
    exact Finset.mem_Ioo.mpr hbounds
  calc
    (detailActiveGrid T j).card ≤ (Finset.Ioo a b).card :=
      Finset.card_le_card hsubset
    _ = b - a - 1 := Nat.card_Ioo a b
    _ ≤ q := by
      dsimp [a, b]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
      exact Nat.sub_le _ _
    _ = 2 ^ (J - j.level.val) := rfl

/-- A grid-point product of detail coefficients is bounded by the product of their heights. -/
theorem detailCoefficientProduct_le_heightProduct
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (details : Finset (DetailIndex J noiseDim)) (i : ℕ) :
    (∏ j ∈ details,
      ‖diffusionCoefficient diffusion T (Sum.inr j) (gridTime T J i)‖) ≤
      ∏ j ∈ details, detailHeightFactor diffusion T j := by
  apply Finset.prod_le_prod₀
  · intro j hj
    exact norm_nonneg _
  · intro j hj
    exact norm_diffusionCoefficient_detail_le diffusion j (gridTime T J i)

/-- Internal grid-support estimate used to prove the displayed bound in Lemma 4.4. -/
private theorem eta_detailIndices_aux
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) (details : Finset (DetailIndex J noiseDim))
    (jstar : DetailIndex J noiseDim) (hjstar : jstar ∈ details) :
    eta diffusion T (detailIndices details) ≤
      (T / 2 ^ jstar.level.val) *
        ∏ j ∈ details, detailHeightFactor diffusion T j := by
  let heightProduct := ∏ j ∈ details, detailHeightFactor diffusion T j
  let active := detailActiveGrid T jstar
  have hstep : 0 ≤ stepSize T J := by
    unfold stepSize
    positivity
  have hpoint : ∀ i ∈ Finset.range (numSteps J),
      (∏ j ∈ details,
          ‖diffusionCoefficient diffusion T (Sum.inr j) (gridTime T J i)‖) ≤
        if i ∈ active then heightProduct else 0 := by
    intro i hi
    by_cases hactive : i ∈ active
    · rw [if_pos hactive]
      exact detailCoefficientProduct_le_heightProduct diffusion T details i
    · rw [if_neg hactive]
      have houtside : gridTime T J i ∉ jstar.supportInterior T := by
        simpa [active, detailActiveGrid, hi] using hactive
      have hcoefficient :=
        coefficient_detail_eq_zero_of_not_mem_supportInterior hT jstar houtside
      have hzero :
          ‖diffusionCoefficient diffusion T (Sum.inr jstar)
            (gridTime T J i)‖ = 0 := by
        change ‖coefficient T (Sum.inr jstar) (gridTime T J i) •
          diffusion (noiseBasis (Index.component (Sum.inr jstar)))‖ = 0
        rw [hcoefficient, zero_smul, norm_zero]
      exact le_of_eq (Finset.prod_eq_zero hjstar hzero)
  have hsum :
      (∑ i ∈ Finset.range (numSteps J),
        ∏ j ∈ details,
          ‖diffusionCoefficient diffusion T (Sum.inr j) (gridTime T J i)‖) ≤
        active.card * heightProduct := by
    have hactiveSubset : active ⊆ Finset.range (numSteps J) := by
      intro i hi
      have hmem : i < numSteps J ∧
          gridTime T J i ∈ jstar.supportInterior T := by
        simpa [active, detailActiveGrid] using hi
      exact Finset.mem_range.mpr hmem.1
    calc
      _ ≤ ∑ i ∈ Finset.range (numSteps J),
          if i ∈ active then heightProduct else 0 :=
        Finset.sum_le_sum fun i hi => hpoint i hi
      _ = ∑ i ∈ active, heightProduct := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hactiveSubset]
      _ = active.card * heightProduct := by simp
  have hcard := card_detailActiveGrid_le hT jstar
  have hheight : 0 ≤ heightProduct := by
    apply Finset.prod_nonneg
    intro j hj
    exact detailHeightFactor_nonneg diffusion T j
  have hprodMap (i : ℕ) :
      (∏ j ∈ detailIndices details,
          ‖diffusionCoefficient diffusion T j (gridTime T J i)‖) =
        ∏ j ∈ details,
          ‖diffusionCoefficient diffusion T (Sum.inr j) (gridTime T J i)‖ := by
    unfold detailIndices
    rw [Finset.prod_map]
    simp
  unfold eta
  simp_rw [hprodMap]
  change stepSize T J * _ ≤ (T / 2 ^ jstar.level.val) * heightProduct
  calc
    stepSize T J *
        (∑ i ∈ Finset.range (numSteps J),
          ∏ j ∈ details,
            ‖diffusionCoefficient diffusion T (Sum.inr j)
              (gridTime T J i)‖) ≤
      stepSize T J * (active.card * heightProduct) := by gcongr
    _ ≤ stepSize T J * (2 ^ (J - jstar.level.val) * heightProduct) := by
      gcongr
      exact_mod_cast hcard
    _ = (T / 2 ^ jstar.level.val) * heightProduct := by
      unfold stepSize numSteps
      have hlevel : jstar.level.val ≤ J := Nat.le_of_lt jstar.level.isLt
      have hpowEq : (2 : ℝ) ^ J =
          (2 : ℝ) ^ jstar.level.val * (2 : ℝ) ^ (J - jstar.level.val) := by
        rw [← pow_add, Nat.add_sub_of_le hlevel]
      norm_num [Nat.cast_pow]
      rw [hpowEq]
      field_simp

/-- The laminar-support bound in the displayed form used by paper Lemma 4.4. -/
theorem eta_detailIndices_laminar_bound
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) (details : Finset (DetailIndex J noiseDim))
    (jstar : DetailIndex J noiseDim) (hjstar : jstar ∈ details) :
    eta diffusion T (detailIndices details) ≤
      (3 / 2 : ℝ) * (T / 2 ^ jstar.level.val) *
        ∏ j ∈ details, detailHeightFactor diffusion T j := by
  have haux := eta_detailIndices_aux
    diffusion hT details jstar hjstar
  have hnonneg : 0 ≤
      (T / 2 ^ jstar.level.val) *
        ∏ j ∈ details, detailHeightFactor diffusion T j := by
    apply mul_nonneg
    · positivity
    · apply Finset.prod_nonneg
      intro j hj
      exact detailHeightFactor_nonneg diffusion T j
  calc
    eta diffusion T (detailIndices details) ≤
        (T / 2 ^ jstar.level.val) *
          ∏ j ∈ details, detailHeightFactor diffusion T j := haux
    _ ≤ (3 / 2 : ℝ) * (T / 2 ^ jstar.level.val) *
          ∏ j ∈ details, detailHeightFactor diffusion T j := by
      nlinarith

/-- Adding endpoint coordinates to a detail set costs only the product of their terminal
factors.  This is the endpoint/detail decomposition used in Lemma 4.5. -/
theorem eta_detail_union_endpoint_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (details : Finset (DetailIndex J noiseDim))
    (endpoints : Finset (Fin noiseDim)) :
    eta diffusion T (detailIndices details ∪ endpointIndices endpoints) ≤
      eta diffusion T (detailIndices details) *
        ∏ r ∈ endpoints, endpointFactor diffusion T r := by
  let endpointProduct := ∏ r ∈ endpoints, endpointFactor diffusion T r
  have hstep : 0 ≤ stepSize T J := by
    unfold stepSize
    exact div_nonneg hT (Nat.cast_nonneg _)
  have hterm : ∀ i ∈ Finset.range (numSteps J),
      (∏ j ∈ detailIndices details ∪ endpointIndices endpoints,
          ‖diffusionCoefficient diffusion T j (gridTime T J i)‖) ≤
        (∏ j ∈ detailIndices details,
          ‖diffusionCoefficient diffusion T j (gridTime T J i)‖) *
          endpointProduct := by
    intro i hi
    have hiLe : i ≤ numSteps J := Nat.le_of_lt (Finset.mem_range.mp hi)
    rw [Finset.prod_union (endpointIndices_disjoint_detailIndices endpoints details).symm]
    apply mul_le_mul_of_nonneg_left
    · dsimp only [endpointProduct]
      rw [endpointIndices, Finset.prod_map]
      induction endpoints using Finset.induction_on with
      | empty => simp
      | @insert r endpoints hr ih =>
          simp only [Finset.prod_insert hr]
          calc
            ‖diffusionCoefficient diffusion T (Sum.inl r) (gridTime T J i)‖ *
                ∏ x ∈ endpoints,
                  ‖diffusionCoefficient diffusion T (Sum.inl x) (gridTime T J i)‖ ≤
              endpointFactor diffusion T r *
                ∏ x ∈ endpoints,
                  ‖diffusionCoefficient diffusion T (Sum.inl x) (gridTime T J i)‖ := by
                gcongr
                exact norm_diffusionCoefficient_endpoint_le diffusion hT r i hiLe
            _ ≤ endpointFactor diffusion T r *
                ∏ x ∈ endpoints, endpointFactor diffusion T x := by
                  exact mul_le_mul_of_nonneg_left ih
                    (endpointFactor_nonneg diffusion T r)
    · positivity
  unfold eta
  calc
    stepSize T J *
        (∑ i ∈ Finset.range (numSteps J),
          ∏ j ∈ detailIndices details ∪ endpointIndices endpoints,
            ‖diffusionCoefficient diffusion T j (gridTime T J i)‖) ≤
      stepSize T J *
        (∑ i ∈ Finset.range (numSteps J),
          (∏ j ∈ detailIndices details,
            ‖diffusionCoefficient diffusion T j (gridTime T J i)‖) *
            endpointProduct) := by
        gcongr with i hi
        exact hterm i hi
    _ = (stepSize T J *
        (∑ i ∈ Finset.range (numSteps J),
          ∏ j ∈ detailIndices details,
            ‖diffusionCoefficient diffusion T j (gridTime T J i)‖)) *
          endpointProduct := by
      rw [← Finset.sum_mul]
      ring


end

end TimeDependentLattice.Regularity
