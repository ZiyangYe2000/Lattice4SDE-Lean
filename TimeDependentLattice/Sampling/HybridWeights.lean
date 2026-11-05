/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.SpecificLimits.Normed
import TimeDependentLattice.Sampling.PathMajorant
import TimeDependentLattice.Sampling.WeightedHolder

/-!
# Hölder weights for Lemma 5.1

This file verifies the two geometric-series calculations used in the hybrid exponential-moment
argument and records the endpoint/detail Hölder weights from the paper.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Regularity

/-- The level-to-level decay `2^{-1/2}` of the Brownian-bridge detail heights. -/
def bridgeLevelRatio : ℝ := 1 / √2

/-- Paper notation `2^{-ℓ/2}`, expressed as an ordinary natural power. -/
def bridgeLevelDecay (level : ℕ) : ℝ := bridgeLevelRatio ^ level

theorem sqrtTwo_gt_one : 1 < √(2 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)
  nlinarith

theorem bridgeLevelRatio_nonneg : 0 ≤ bridgeLevelRatio := by
  unfold bridgeLevelRatio
  positivity

theorem bridgeLevelRatio_lt_one : bridgeLevelRatio < 1 := by
  unfold bridgeLevelRatio
  exact (div_lt_one (Real.sqrt_pos.2 (by norm_num))).mpr sqrtTwo_gt_one

theorem bridgeLevelDecay_nonneg (level : ℕ) : 0 ≤ bridgeLevelDecay level := by
  exact pow_nonneg bridgeLevelRatio_nonneg _

/-- The rpow notation used by the coefficient functions is exactly the geometric decay used
in the series computation. -/
theorem rpow_two_neg_half_nat_eq_bridgeLevelDecay (level : ℕ) :
    (2 : ℝ) ^ (-(level : ℝ) / 2) = bridgeLevelDecay level := by
  unfold bridgeLevelDecay bridgeLevelRatio
  calc
    (2 : ℝ) ^ (-(level : ℝ) / 2) =
        (2 : ℝ) ^ (-(1 / 2 * (level : ℝ))) := by
      congr 1
      ring
    _ = ((2 : ℝ) ^ (1 / 2 * (level : ℝ)))⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    _ = (((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (level : ℝ))⁻¹ := by
      exact congrArg Inv.inv
        (Real.rpow_mul (x := (2 : ℝ)) (by norm_num) (1 / 2) (level : ℝ))
    _ = ((√2) ^ (level : ℝ))⁻¹ := by
      exact congrArg Inv.inv
        (congrArg (fun x : ℝ => Real.rpow x (level : ℝ))
          (Real.sqrt_eq_rpow (2 : ℝ)).symm)
    _ = ((√2) ^ level)⁻¹ := by
      exact congrArg Inv.inv (Real.rpow_natCast _ _)
    _ = (1 / √2) ^ level := by rw [one_div, inv_pow]

/-- The infinite sum `∑ 2^{-ℓ/2}` occurring in the total Hölder mass. -/
theorem tsum_bridgeLevelDecay :
    (∑' level : ℕ, bridgeLevelDecay level) = 2 + √2 := by
  rw [show (fun level => bridgeLevelDecay level) =
      (fun level : ℕ => bridgeLevelRatio ^ level) by rfl]
  rw [tsum_geometric_of_lt_one bridgeLevelRatio_nonneg bridgeLevelRatio_lt_one]
  unfold bridgeLevelRatio
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsub : √(2 : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr sqrtTwo_gt_one)
  calc
    (1 - 1 / √2)⁻¹ = √2 / (√2 - 1) := by field_simp
    _ = 2 + √2 := by
      apply (div_eq_iff hsub).2
      nlinarith

/-- The second infinite series used for the residual power of `2`. -/
theorem tsum_level_mul_bridgeLevelDecay :
    (∑' level : ℕ, (level : ℝ) * bridgeLevelDecay level) = 4 + 3 * √2 := by
  change (∑' level : ℕ, (level : ℝ) * bridgeLevelRatio ^ level) = _
  rw [tsum_coe_mul_geometric_of_norm_lt_one (r := bridgeLevelRatio) (by
    simpa [Real.norm_eq_abs, abs_of_nonneg bridgeLevelRatio_nonneg] using
      bridgeLevelRatio_lt_one)]
  unfold bridgeLevelRatio
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsub : √(2 : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr sqrtTwo_gt_one)
  calc
    (1 / √2) / (1 - 1 / √2) ^ 2 = √2 / (√2 - 1) ^ 2 := by field_simp
    _ = 4 + 3 * √2 := by
      apply (div_eq_iff (pow_ne_zero 2 hsub)).2
      nlinarith

theorem sum_bridgeLevelDecay_le (J : ℕ) :
    (∑ level : Fin J, bridgeLevelDecay level.val) ≤ 2 + √2 := by
  rw [Fin.sum_univ_eq_sum_range]
  calc
    (∑ level ∈ Finset.range J, bridgeLevelDecay level) ≤
        ∑' level : ℕ, bridgeLevelDecay level := by
      exact (summable_geometric_of_lt_one bridgeLevelRatio_nonneg
        bridgeLevelRatio_lt_one).sum_le_tsum _
        (fun level hlevel => bridgeLevelDecay_nonneg level)
    _ = 2 + √2 := tsum_bridgeLevelDecay

theorem sum_level_mul_bridgeLevelDecay_le (J : ℕ) :
    (∑ level : Fin J, (level.val : ℝ) * bridgeLevelDecay level.val) ≤
      4 + 3 * √2 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun level : ℕ => (level : ℝ) * bridgeLevelDecay level) J]
  have hsummable : Summable
      (fun level : ℕ => (level : ℝ) * bridgeLevelRatio ^ level) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (r := bridgeLevelRatio) (by
      simpa [Real.norm_eq_abs, abs_of_nonneg bridgeLevelRatio_nonneg] using
        bridgeLevelRatio_lt_one)).summable
  calc
    (∑ level ∈ Finset.range J, (level : ℝ) * bridgeLevelDecay level) ≤
        ∑' level : ℕ, (level : ℝ) * bridgeLevelDecay level := by
      exact hsummable.sum_le_tsum _ (fun level hlevel =>
        mul_nonneg (Nat.cast_nonneg _) (bridgeLevelDecay_nonneg level))
    _ = 4 + 3 * √2 := tsum_level_mul_bridgeLevelDecay

/-! ## The finite family of paper Hölder weights -/

/-- The normalizing denominator `2 + 1 / √2` in the paper's weights. -/
def hybridWeightDenominator : ℝ := 2 + 1 / √2

theorem hybridWeightDenominator_pos : 0 < hybridWeightDenominator := by
  unfold hybridWeightDenominator
  positivity

/-- Endpoint weight `w_r`. -/
def endpointHybridWeight {noiseDim : ℕ} (sigma : Fin noiseDim → ℝ)
    (r : Fin noiseDim) : ℝ :=
  sigma r / ((∑ q, sigma q) * hybridWeightDenominator)

/-- Detail weight `w_{ℓ,r}`. -/
def detailHybridWeight {J noiseDim : ℕ} (sigma : Fin noiseDim → ℝ)
    (level : Fin J) (r : Fin noiseDim) : ℝ :=
  sigma r * bridgeLevelDecay level.val /
    (2 * (∑ q, sigma q) * hybridWeightDenominator)

/-- One finite index type containing both endpoint and detail factors in generalized Hölder. -/
abbrev HybridHolderIndex (J noiseDim : ℕ) :=
  Fin noiseDim ⊕ (Fin J × Fin noiseDim)

def hybridHolderWeight {J noiseDim : ℕ} (sigma : Fin noiseDim → ℝ) :
    HybridHolderIndex J noiseDim → ℝ
  | Sum.inl r => endpointHybridWeight sigma r
  | Sum.inr pair => detailHybridWeight sigma pair.1 pair.2

/-- The power of `2` contributed by one factor: zero for endpoints and `ℓ` for a
level-`ℓ` detail group. -/
def hybridHolderLevel {J noiseDim : ℕ} : HybridHolderIndex J noiseDim → ℝ
  | Sum.inl _ => 0
  | Sum.inr pair => pair.1.val

theorem endpointHybridWeight_nonneg {noiseDim : ℕ} {sigma : Fin noiseDim → ℝ}
    (hsigma : ∀ r, 0 ≤ sigma r) (r : Fin noiseDim) :
    0 ≤ endpointHybridWeight sigma r := by
  unfold endpointHybridWeight
  apply div_nonneg (hsigma r)
  apply mul_nonneg
  · exact Finset.sum_nonneg fun q hq => hsigma q
  · exact hybridWeightDenominator_pos.le

theorem detailHybridWeight_nonneg {J noiseDim : ℕ} {sigma : Fin noiseDim → ℝ}
    (hsigma : ∀ r, 0 ≤ sigma r) (level : Fin J) (r : Fin noiseDim) :
    0 ≤ detailHybridWeight sigma level r := by
  unfold detailHybridWeight
  apply div_nonneg
  · exact mul_nonneg (hsigma r) (bridgeLevelDecay_nonneg level.val)
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun q hq => hsigma q))
      hybridWeightDenominator_pos.le

theorem hybridHolderWeight_nonneg {J noiseDim : ℕ} {sigma : Fin noiseDim → ℝ}
    (hsigma : ∀ r, 0 ≤ sigma r) (j : HybridHolderIndex J noiseDim) :
    0 ≤ hybridHolderWeight sigma j := by
  cases j with
  | inl r => exact endpointHybridWeight_nonneg hsigma r
  | inr pair => exact detailHybridWeight_nonneg hsigma pair.1 pair.2

/-- The paper's finite endpoint/detail weights have total mass at most one. -/
theorem sum_hybridHolderWeight_le_one
    {J noiseDim : ℕ} {sigma : Fin noiseDim → ℝ}
    (htheta : 0 < ∑ r, sigma r) :
    (∑ j : HybridHolderIndex J noiseDim, hybridHolderWeight sigma j) ≤ 1 := by
  let theta := ∑ r, sigma r
  let denominator := hybridWeightDenominator
  have hthetaNe : theta ≠ 0 := ne_of_gt htheta
  have hdenominator : 0 < denominator := hybridWeightDenominator_pos
  have hdenominatorNe : denominator ≠ 0 := ne_of_gt hdenominator
  have hendpoint :
      (∑ r : Fin noiseDim, endpointHybridWeight sigma r) = 1 / denominator := by
    calc
      (∑ r : Fin noiseDim, endpointHybridWeight sigma r) =
          theta / (theta * denominator) := by
        unfold endpointHybridWeight theta denominator
        rw [Finset.sum_div]
      _ = 1 / denominator := by field_simp
  have hdetail : ∀ level : Fin J,
      (∑ r : Fin noiseDim, detailHybridWeight sigma level r) =
        bridgeLevelDecay level.val / (2 * denominator) := by
    intro level
    calc
      (∑ r : Fin noiseDim, detailHybridWeight sigma level r) =
          (theta * bridgeLevelDecay level.val) /
            (2 * theta * denominator) := by
        unfold detailHybridWeight theta denominator
        rw [Finset.sum_mul, Finset.sum_div]
      _ = bridgeLevelDecay level.val / (2 * denominator) := by field_simp
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  change (∑ r : Fin noiseDim, endpointHybridWeight sigma r) +
      (∑ level : Fin J, ∑ r : Fin noiseDim, detailHybridWeight sigma level r) ≤ 1
  rw [hendpoint]
  simp_rw [hdetail]
  rw [← Finset.sum_div]
  let levelSum := ∑ level : Fin J, bridgeLevelDecay level.val
  have hlevelSum : levelSum ≤ 2 + √2 := sum_bridgeLevelDecay_le J
  have hidentity : denominator = 1 + (2 + √2) / 2 := by
    unfold denominator hybridWeightDenominator
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn : √(2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp
    nlinarith
  have hnumerator : 1 + levelSum / 2 ≤ denominator := by
    rw [hidentity]
    gcongr
  calc
    1 / denominator + levelSum / (2 * denominator) =
        (1 + levelSum / 2) / denominator := by field_simp
    _ ≤ denominator / denominator :=
      div_le_div_of_nonneg_right hnumerator hdenominator.le
    _ = 1 := div_self hdenominatorNe

/-- The weighted sum of detail levels is bounded by the exponent appearing in `C_aux`. -/
theorem sum_hybridHolderLevel_mul_weight_le
    {J noiseDim : ℕ} {sigma : Fin noiseDim → ℝ}
    (htheta : 0 < ∑ r, sigma r) :
    (∑ j : HybridHolderIndex J noiseDim,
        hybridHolderLevel j * hybridHolderWeight sigma j) ≤
      (4 + 3 * √2) / (4 + √2) := by
  let theta := ∑ r, sigma r
  let denominator := hybridWeightDenominator
  have hthetaNe : theta ≠ 0 := ne_of_gt htheta
  have hdenominator : 0 < denominator := hybridWeightDenominator_pos
  have hlevel : ∀ level : Fin J,
      (∑ r : Fin noiseDim,
        (level.val : ℝ) * detailHybridWeight sigma level r) =
        (level.val : ℝ) * bridgeLevelDecay level.val / (2 * denominator) := by
    intro level
    calc
      (∑ r : Fin noiseDim,
          (level.val : ℝ) * detailHybridWeight sigma level r) =
          ((level.val : ℝ) * theta * bridgeLevelDecay level.val) /
            (2 * theta * denominator) := by
        unfold detailHybridWeight theta denominator
        rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_mul]
        ring
      _ = (level.val : ℝ) * bridgeLevelDecay level.val /
          (2 * denominator) := by field_simp
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [hybridHolderLevel, hybridHolderWeight, zero_mul,
    Finset.sum_const_zero, zero_add]
  simp_rw [hlevel]
  rw [← Finset.sum_div]
  have hseries := sum_level_mul_bridgeLevelDecay_le J
  have htwoDenominator : 0 < 2 * denominator := mul_pos (by norm_num) hdenominator
  have hidentity : 2 * denominator = 4 + √2 := by
    unfold denominator hybridWeightDenominator
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn : √(2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp
    nlinarith
  calc
    (∑ level : Fin J, (level.val : ℝ) * bridgeLevelDecay level.val) /
        (2 * denominator) ≤
        (4 + 3 * √2) / (2 * denominator) :=
      div_le_div_of_nonneg_right hseries htwoDenominator.le
    _ = (4 + 3 * √2) / (4 + √2) := by rw [hidentity]

/-- The random quantity attached to each Hölder factor: endpoint absolute value or detail
level maximum. -/
def hybridHolderObservable {J noiseDim : ℕ} (z : Index J noiseDim → ℝ) :
    HybridHolderIndex J noiseDim → ℝ
  | Sum.inl r => |z (Sum.inl r)|
  | Sum.inr pair => detailLevelMaxAbs z pair.1 pair.2

/-- The real-valued paper column norm `σ_r`. -/
def diffusionSigma {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (r : Fin noiseDim) : ℝ :=
  Regularity.columnNorm diffusion r

/-- The paper's `Θ₁ = ∑ σ_r`. -/
def diffusionThetaOne {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) : ℝ :=
  ∑ r, diffusionSigma diffusion r

theorem diffusionSigma_nonneg {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (r : Fin noiseDim) :
    0 ≤ diffusionSigma diffusion r :=
  columnNorm_nonneg diffusion r

theorem hybridLambda_mul_endpointHybridWeight
    {noiseDim : ℕ} {sigma : Fin noiseDim → ℝ} (htheta : 0 < ∑ r, sigma r)
    (β T L : ℝ) (r : Fin noiseDim) :
    hybridLambda β T L (∑ q, sigma q) * endpointHybridWeight sigma r =
      2 * β * Real.exp (L * T) * √T * sigma r := by
  have hthetaNe : (∑ q, sigma q) ≠ 0 := ne_of_gt htheta
  have hdenominatorNe : hybridWeightDenominator ≠ 0 :=
    ne_of_gt hybridWeightDenominator_pos
  unfold hybridLambda hybridMomentScale endpointHybridWeight hybridWeightDenominator
  field_simp

theorem hybridLambda_mul_detailHybridWeight
    {J noiseDim : ℕ} {sigma : Fin noiseDim → ℝ} (htheta : 0 < ∑ r, sigma r)
    (β T L : ℝ) (level : Fin J) (r : Fin noiseDim) :
    hybridLambda β T L (∑ q, sigma q) * detailHybridWeight sigma level r =
      β * Real.exp (L * T) * √T * sigma r * bridgeLevelDecay level.val := by
  have hthetaNe : (∑ q, sigma q) ≠ 0 := ne_of_gt htheta
  have hdenominatorNe : hybridWeightDenominator ≠ 0 :=
    ne_of_gt hybridWeightDenominator_pos
  unfold hybridLambda hybridMomentScale detailHybridWeight hybridWeightDenominator
  field_simp

/-- The exponent built from the Hölder factors is exactly the exponent obtained from the
Brownian-path majorant.  This checks that the formal weights match the paper coefficients. -/
theorem hybridLambda_mul_weightedObservableSum_eq
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (htheta : 0 < diffusionThetaOne diffusion) (β T L : ℝ)
    (z : Index J noiseDim → ℝ) :
    hybridLambda β T L (diffusionThetaOne diffusion) *
        (∑ j : HybridHolderIndex J noiseDim,
          hybridHolderWeight (diffusionSigma diffusion) j * hybridHolderObservable z j) =
      2 * β * Real.exp (L * T) * brownianPathMajorant diffusion T z := by
  unfold diffusionThetaOne at htheta ⊢
  rw [Finset.mul_sum, Fintype.sum_sum_type]
  simp only [hybridHolderWeight, hybridHolderObservable]
  rw [Fintype.sum_prod_type]
  simp_rw [← mul_assoc]
  simp_rw [hybridLambda_mul_endpointHybridWeight htheta β T L]
  simp_rw [hybridLambda_mul_detailHybridWeight htheta β T L]
  unfold brownianPathMajorant endpointFactor detailHeightFactor diffusionSigma
  simp_rw [rpow_two_neg_half_nat_eq_bridgeLevelDecay]
  simp only [DetailIndex.level, DetailIndex.component]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro level hlevel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring

end

end TimeDependentLattice.Sampling
