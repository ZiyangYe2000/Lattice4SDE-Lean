/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Regularity.DetailSummability
import TimeDependentLattice.Regularity.Summability
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Summability over endpoint and detail coordinates

This file formalizes Lemma 4.5.  A Brownian-bridge coordinate subset is split using
`Finset.sumEquiv` into its endpoint and detail parts.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open scoped BigOperators
open TimeDependentLattice
open TimeDependentLattice.BrownianBridge

/-- The full coordinate finset formed from endpoint and detail parts. -/
def bridgeSubset {J noiseDim : ℕ} (endpoints : Finset (Fin noiseDim))
    (details : Finset (DetailIndex J noiseDim)) : Finset (Index J noiseDim) :=
  endpoints.disjSum details

theorem bridgeSubset_eq_union {J noiseDim : ℕ}
    (endpoints : Finset (Fin noiseDim))
    (details : Finset (DetailIndex J noiseDim)) :
    bridgeSubset endpoints details =
      endpointIndices (J := J) endpoints ∪ detailIndices details := by
  ext j
  cases j <;> simp [bridgeSubset, endpointIndices, detailIndices]

@[simp]
theorem bridgeSubset_card {J noiseDim : ℕ}
    (endpoints : Finset (Fin noiseDim))
    (details : Finset (DetailIndex J noiseDim)) :
    (bridgeSubset endpoints details).card = endpoints.card + details.card := by
  exact Finset.card_disjSum endpoints details

/-- Endpoint/detail form of the time-factor bound in Lemma 4.5. -/
theorem eta_bridgeSubset_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (endpoints : Finset (Fin noiseDim))
    (details : Finset (DetailIndex J noiseDim)) :
    eta diffusion T (bridgeSubset endpoints details) ≤
      eta diffusion T (detailIndices details) *
        ∏ r ∈ endpoints, endpointFactor diffusion T r := by
  rw [bridgeSubset_eq_union]
  simpa [Finset.union_comm] using
    eta_detail_union_endpoint_le diffusion hT details endpoints

/-- Raising an endpoint factor to `ρ` separates its common `√T` factor. -/
theorem endpointFactor_rpow
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ) (r : Fin noiseDim) :
    endpointFactor diffusion T r ^ ρ =
      (√T) ^ ρ * columnNorm diffusion r ^ ρ := by
  unfold endpointFactor
  exact Real.mul_rpow (Real.sqrt_nonneg T) (columnNorm_nonneg diffusion r)

/-- Fixed-cardinality endpoint subset estimate used in Equation (C.5). -/
theorem endpoint_powersetCard_prod_rpow_le
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ) (ℓ : ℕ) :
    (∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powersetCard ℓ,
        ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) ≤
      (((√T) ^ ρ * columnRhoSum diffusion ρ) ^ ℓ) / ℓ.factorial := by
  have hsymm := sum_powersetCard_prod_le_sum_pow_div_factorial
    (Finset.univ : Finset (Fin noiseDim))
    (fun r => endpointFactor diffusion T r ^ ρ) ℓ
    (fun r hr => Real.rpow_nonneg (endpointFactor_nonneg diffusion T r) ρ)
  calc
    (∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powersetCard ℓ,
        ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) ≤
      ((∑ r : Fin noiseDim, endpointFactor diffusion T r ^ ρ) ^ ℓ) /
        ℓ.factorial := hsymm
    _ = (((√T) ^ ρ * columnRhoSum diffusion ρ) ^ ℓ) / ℓ.factorial := by
      congr 2
      simp_rw [endpointFactor_rpow diffusion hT ρ]
      rw [← Finset.mul_sum]
      rfl

/-- The factorial inequality used to separate endpoint and detail cardinalities. -/
theorem factorial_add_rpow_le
    (d e : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    ((d + e).factorial : ℝ) ^ q ≤
      ((2 : ℝ) ^ q) ^ (d + e) *
        (d.factorial : ℝ) ^ q * (e.factorial : ℝ) ^ q := by
  have hchoose := Nat.choose_le_two_pow (d + e) d
  have hfactorial : (d + e).factorial =
      (d + e).choose d * d.factorial * e.factorial := by
    simpa [Nat.add_sub_cancel_left] using
      (Nat.choose_mul_factorial_mul_factorial
        (n := d + e) (k := d) (Nat.le_add_right d e)).symm
  have hnat : (d + e).factorial ≤
      2 ^ (d + e) * d.factorial * e.factorial := by
    rw [hfactorial]
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_right (d.factorial * e.factorial) hchoose
  have hreal : ((d + e).factorial : ℝ) ≤
      ((2 ^ (d + e) * d.factorial * e.factorial : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((d + e).factorial : ℝ) ^ q ≤
        ((2 ^ (d + e) * d.factorial * e.factorial : ℕ) : ℝ) ^ q :=
      Real.rpow_le_rpow (by positivity) hreal hq
    _ = ((2 : ℝ) ^ q) ^ (d + e) *
        (d.factorial : ℝ) ^ q * (e.factorial : ℝ) ^ q := by
      norm_num [Nat.cast_mul, Nat.cast_pow]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
      have htwo : ((2 : ℝ) ^ (d + e)) ^ q =
          ((2 : ℝ) ^ q) ^ (d + e) := by
        rw [← Real.rpow_natCast (2 : ℝ) (d + e)]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [htwo]

private theorem weighted_factorial_div_eq
    (κ X q : ℝ) (n : ℕ) :
    κ ^ n * (n.factorial : ℝ) ^ q * (X ^ n / n.factorial) =
      (κ * X) ^ n * (n.factorial : ℝ) ^ (q - 1) := by
  rw [Real.rpow_sub_one (by positivity : (n.factorial : ℝ) ≠ 0)]
  rw [mul_pow]
  field_simp

/-- Endpoint contribution in Lemma 4.5. -/
def endpointWeightedSum {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ τ : ℝ) : ℝ :=
  ∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powerset,
    κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
      ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ

/-- A positive geometric base dominating the endpoint series. -/
def endpointSeriesBase {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ : ℝ) : ℝ :=
  1 + κ * (√T) ^ ρ * columnRhoSum diffusion ρ

/-- Dimension-independent endpoint-series majorant. -/
def endpointSeriesConstant {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ τ : ℝ) : ℝ :=
  factorialDecaySeries (endpointSeriesBase diffusion T κ ρ) (τ * ρ)

theorem endpointSeriesBase_pos
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (ρ : ℝ) :
    0 < endpointSeriesBase diffusion T κ ρ := by
  unfold endpointSeriesBase
  have htheta := columnRhoSum_nonneg diffusion ρ
  have hsqrt := Real.rpow_nonneg (Real.sqrt_nonneg T) ρ
  positivity

theorem endpointSeriesConstant_summable
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hτρ : τ * ρ < 1) :
    Summable (fun n : ℕ =>
      endpointSeriesBase diffusion T κ ρ ^ n *
        (n.factorial : ℝ) ^ (τ * ρ - 1)) :=
  summable_factorialDecaySeries (endpointSeriesBase_pos diffusion hT hκ ρ) hτρ

/-- Equation (C.5): the endpoint contribution is bounded independently of `noiseDim`. -/
theorem endpointWeightedSum_le_seriesConstant
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hτρ : τ * ρ < 1) :
    endpointWeightedSum diffusion T κ ρ τ ≤
      endpointSeriesConstant diffusion T κ ρ τ := by
  classical
  let X := (√T) ^ ρ * columnRhoSum diffusion ρ
  let A := endpointSeriesBase diffusion T κ ρ
  have hX : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg T) ρ)
    (columnRhoSum_nonneg diffusion ρ)
  have hbase : κ * X ≤ A := by
    unfold A endpointSeriesBase X
    linarith
  have hA : 0 ≤ A := (endpointSeriesBase_pos diffusion hT hκ ρ).le
  have hsummable := endpointSeriesConstant_summable diffusion hT hκ hτρ
  unfold endpointWeightedSum endpointSeriesConstant
  have hdecompose :
      (∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powerset,
          κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
            ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) =
        ∑ ℓ ∈ Finset.range ((Finset.univ : Finset (Fin noiseDim)).card + 1),
          ∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powersetCard ℓ,
            κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
              ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ := by
    rw [Finset.powerset_card_disjiUnion]
    apply Finset.sum_disjiUnion
  rw [hdecompose]
  calc
    (∑ ℓ ∈ Finset.range ((Finset.univ : Finset (Fin noiseDim)).card + 1),
        ∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powersetCard ℓ,
          κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
            ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) ≤
      ∑ ℓ ∈ Finset.range ((Finset.univ : Finset (Fin noiseDim)).card + 1),
        A ^ ℓ * (ℓ.factorial : ℝ) ^ (τ * ρ - 1) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      have hfixed := endpoint_powersetCard_prod_rpow_le diffusion hT ρ ℓ
      have hcommon : 0 ≤ κ ^ ℓ * (ℓ.factorial : ℝ) ^ (τ * ρ) := by
        exact mul_nonneg (pow_nonneg hκ ℓ) (Real.rpow_nonneg (by positivity) _)
      calc
        (∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powersetCard ℓ,
            κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
              ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) =
          κ ^ ℓ * (ℓ.factorial : ℝ) ^ (τ * ρ) *
            (∑ endpoints ∈ (Finset.univ : Finset (Fin noiseDim)).powersetCard ℓ,
              ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro endpoints hendpoints
            have hcard := (Finset.mem_powersetCard.mp hendpoints).2
            rw [hcard]
        _ ≤ κ ^ ℓ * (ℓ.factorial : ℝ) ^ (τ * ρ) *
            (X ^ ℓ / ℓ.factorial) := by
          exact mul_le_mul_of_nonneg_left hfixed hcommon
        _ = (κ * X) ^ ℓ * (ℓ.factorial : ℝ) ^ (τ * ρ - 1) :=
          weighted_factorial_div_eq κ X (τ * ρ) ℓ
        _ ≤ A ^ ℓ * (ℓ.factorial : ℝ) ^ (τ * ρ - 1) := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (mul_nonneg hκ hX) hbase ℓ)
            (Real.rpow_nonneg (by positivity) _)
    _ ≤ ∑' ℓ : ℕ, A ^ ℓ * (ℓ.factorial : ℝ) ^ (τ * ρ - 1) := by
      exact hsummable.sum_le_tsum _ (fun ℓ hℓ => by positivity)

private theorem weighted_factorial_pred_div_eq
    (κ Y q : ℝ) (n : ℕ) (hn : 0 < n) :
    κ ^ n * (n.factorial : ℝ) ^ q * (Y ^ n / (n - 1).factorial) =
      (κ * Y) ^ n * n * (n.factorial : ℝ) ^ (q - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one, Nat.factorial_succ]
  rw [Real.rpow_sub_one (by positivity : (((m + 1) * m.factorial : ℕ) : ℝ) ≠ 0)]
  rw [mul_pow]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_succ]
  ring

/-- Nonempty detail contribution in Lemma 4.5. -/
def detailWeightedSum {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ τ : ℝ) : ℝ :=
  ∑ details ∈ (Finset.univ : Finset (DetailIndex J noiseDim)).powerset.filter
      (fun details => details.Nonempty),
    κ ^ details.card * (details.card.factorial : ℝ) ^ (τ * ρ) *
      eta diffusion T (detailIndices details) ^ ρ

/-- A positive base dominating the detail series. -/
def detailSeriesBase {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ : ℝ) : ℝ :=
  1 + 2 * κ * detailSummabilityConstant T ρ * columnRhoSum diffusion ρ

/-- Dimension-independent detail-series majorant. -/
def detailSeriesConstant {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ τ : ℝ) : ℝ :=
  factorialDecaySeries (detailSeriesBase diffusion T κ ρ) (τ * ρ)

theorem detailSummabilityConstant_nonneg {T ρ : ℝ} (hT : 0 ≤ T)
    (hρ : 2 / 3 < ρ) :
    0 ≤ detailSummabilityConstant T ρ := by
  unfold detailSummabilityConstant
  exact mul_nonneg (detailSummabilityA_nonneg hT (by linarith))
    (zero_le_one.trans (le_max_left 1 (detailSummabilityB T ρ)))

theorem detailSeriesBase_pos
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ) :
    0 < detailSeriesBase diffusion T κ ρ := by
  unfold detailSeriesBase
  have hC := detailSummabilityConstant_nonneg hT hρ
  have htheta := columnRhoSum_nonneg diffusion ρ
  positivity

theorem detailSeriesConstant_summable
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (hτρ : τ * ρ < 1) :
    Summable (fun n : ℕ =>
      detailSeriesBase diffusion T κ ρ ^ n *
        (n.factorial : ℝ) ^ (τ * ρ - 1)) :=
  summable_factorialDecaySeries
    (detailSeriesBase_pos diffusion hT hκ hρ) hτρ

/-- The detail contribution is bounded independently of the Brownian-bridge level `J`. -/
theorem detailWeightedSum_le_seriesConstant
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (hτρ : τ * ρ < 1) :
    detailWeightedSum (J := J) diffusion T κ ρ τ ≤
      detailSeriesConstant diffusion T κ ρ τ := by
  classical
  let CΘ := detailSummabilityConstant T ρ * columnRhoSum diffusion ρ
  let A := detailSeriesBase diffusion T κ ρ
  have hCΘ : 0 ≤ CΘ := mul_nonneg
    (detailSummabilityConstant_nonneg hT.le hρ)
    (columnRhoSum_nonneg diffusion ρ)
  have hbase : 2 * κ * CΘ ≤ A := by
    unfold A detailSeriesBase CΘ
    linarith
  have hA : 0 ≤ A := (detailSeriesBase_pos diffusion hT.le hκ hρ).le
  have hsummable := detailSeriesConstant_summable diffusion hT.le hκ hρ hτρ
  unfold detailWeightedSum detailSeriesConstant
  rw [Finset.sum_filter]
  have hdecompose :
      (∑ details ∈ (Finset.univ : Finset (DetailIndex J noiseDim)).powerset,
          if details.Nonempty then
            κ ^ details.card * (details.card.factorial : ℝ) ^ (τ * ρ) *
              eta diffusion T (detailIndices details) ^ ρ
          else 0) =
        ∑ n ∈ Finset.range
            ((Finset.univ : Finset (DetailIndex J noiseDim)).card + 1),
          ∑ details ∈
              (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
            if details.Nonempty then
              κ ^ details.card * (details.card.factorial : ℝ) ^ (τ * ρ) *
                eta diffusion T (detailIndices details) ^ ρ
            else 0 := by
    rw [Finset.powerset_card_disjiUnion]
    apply Finset.sum_disjiUnion
  rw [hdecompose]
  calc
    (∑ n ∈ Finset.range
          ((Finset.univ : Finset (DetailIndex J noiseDim)).card + 1),
        ∑ details ∈
            (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
          if details.Nonempty then
            κ ^ details.card * (details.card.factorial : ℝ) ^ (τ * ρ) *
              eta diffusion T (detailIndices details) ^ ρ
          else 0) ≤
      ∑ n ∈ Finset.range
          ((Finset.univ : Finset (DetailIndex J noiseDim)).card + 1),
        A ^ n * (n.factorial : ℝ) ^ (τ * ρ - 1) := by
      apply Finset.sum_le_sum
      intro n hnRange
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hn : 0 < n := Nat.pos_of_ne_zero hn0
        have hfixed := detail_powersetCard_eta_rpow_le
          (J := J) diffusion hT hρ n hn
        have hcommon : 0 ≤ κ ^ n * (n.factorial : ℝ) ^ (τ * ρ) :=
          mul_nonneg (pow_nonneg hκ n) (Real.rpow_nonneg (by positivity) _)
        calc
          (∑ details ∈
              (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
            if details.Nonempty then
              κ ^ details.card * (details.card.factorial : ℝ) ^ (τ * ρ) *
                eta diffusion T (detailIndices details) ^ ρ
            else 0) =
            κ ^ n * (n.factorial : ℝ) ^ (τ * ρ) *
              (∑ details ∈
                (Finset.univ : Finset (DetailIndex J noiseDim)).powersetCard n,
                eta diffusion T (detailIndices details) ^ ρ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro details hdetails
              have hcard := (Finset.mem_powersetCard.mp hdetails).2
              have hnonempty : details.Nonempty := Finset.card_pos.mp (by omega)
              rw [if_pos hnonempty, hcard]
          _ ≤ κ ^ n * (n.factorial : ℝ) ^ (τ * ρ) *
              (CΘ ^ n / (n - 1).factorial) :=
            mul_le_mul_of_nonneg_left hfixed hcommon
          _ = (κ * CΘ) ^ n * n *
              (n.factorial : ℝ) ^ (τ * ρ - 1) :=
            weighted_factorial_pred_div_eq κ CΘ (τ * ρ) n hn
          _ ≤ (2 * κ * CΘ) ^ n *
              (n.factorial : ℝ) ^ (τ * ρ - 1) := by
            have hnTwo : (n : ℝ) ≤ (2 : ℝ) ^ n := by
              exact_mod_cast (Nat.lt_two_pow_self.le : n ≤ 2 ^ n)
            have hpow : (κ * CΘ) ^ n * n ≤ (2 * κ * CΘ) ^ n := by
              rw [show (2 * κ * CΘ) ^ n = (2 : ℝ) ^ n * (κ * CΘ) ^ n by
                rw [← mul_pow]; congr 1 <;> ring]
              nlinarith [pow_nonneg (mul_nonneg hκ hCΘ) n]
            exact mul_le_mul_of_nonneg_right hpow
              (Real.rpow_nonneg (by positivity) _)
          _ ≤ A ^ n * (n.factorial : ℝ) ^ (τ * ρ - 1) := by
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (by positivity) hbase n)
              (Real.rpow_nonneg (by positivity) _)
    _ ≤ ∑' n : ℕ, A ^ n * (n.factorial : ℝ) ^ (τ * ρ - 1) := by
      exact hsummable.sum_le_tsum _ (fun n hn =>
        mul_nonneg (pow_nonneg hA n) (Real.rpow_nonneg (by positivity) _))

/-- The endpoint/detail time-factor estimate after raising to `ρ`. -/
theorem eta_bridgeSubset_rpow_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T ρ : ℝ} (hT : 0 ≤ T) (hρ : 0 ≤ ρ)
    (endpoints : Finset (Fin noiseDim))
    (details : Finset (DetailIndex J noiseDim)) :
    eta diffusion T (bridgeSubset endpoints details) ^ ρ ≤
      eta diffusion T (detailIndices details) ^ ρ *
        ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ := by
  have heta := eta_nonneg diffusion hT (bridgeSubset endpoints details)
  have hdetail := eta_nonneg diffusion hT (detailIndices details)
  have hendpoint : 0 ≤ ∏ r ∈ endpoints, endpointFactor diffusion T r :=
    Finset.prod_nonneg fun r hr => endpointFactor_nonneg diffusion T r
  calc
    eta diffusion T (bridgeSubset endpoints details) ^ ρ ≤
        (eta diffusion T (detailIndices details) *
          ∏ r ∈ endpoints, endpointFactor diffusion T r) ^ ρ :=
      Real.rpow_le_rpow heta
        (eta_bridgeSubset_le diffusion hT endpoints details) hρ
    _ = eta diffusion T (detailIndices details) ^ ρ *
        ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ := by
      rw [Real.mul_rpow hdetail hendpoint]
      rw [Real.finsetProd_rpow endpoints (endpointFactor diffusion T)
        (fun r hr => endpointFactor_nonneg diffusion T r) ρ]

/-- The binomial/factorial separation used with
`κ' = 2^(τρ) κ` in Lemma 4.5. -/
theorem combined_cardinality_weight_le
    {κ q : ℝ} (hκ : 0 ≤ κ) (hq : 0 ≤ q) (d e : ℕ) :
    κ ^ (d + e) * ((d + e).factorial : ℝ) ^ q ≤
      (((2 : ℝ) ^ q * κ) ^ d * (d.factorial : ℝ) ^ q) *
        (((2 : ℝ) ^ q * κ) ^ e * (e.factorial : ℝ) ^ q) := by
  have hfac := factorial_add_rpow_le d e hq
  have hκpow : 0 ≤ κ ^ (d + e) := pow_nonneg hκ _
  calc
    κ ^ (d + e) * ((d + e).factorial : ℝ) ^ q ≤
      κ ^ (d + e) *
        (((2 : ℝ) ^ q) ^ (d + e) *
          (d.factorial : ℝ) ^ q * (e.factorial : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_left hfac hκpow
    _ = (((2 : ℝ) ^ q * κ) ^ d * (d.factorial : ℝ) ^ q) *
        (((2 : ℝ) ^ q * κ) ^ e * (e.factorial : ℝ) ^ q) := by
      rw [pow_add, pow_add, mul_pow, mul_pow]
      ring

/-- The complete nonempty-subset time-factor sum in Lemma 4.5. -/
def allSubsetTimeFactorSum {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ τ : ℝ) : ℝ :=
  ∑ support : Finset (Index J noiseDim),
    if support.Nonempty then
      κ ^ support.card * (support.card.factorial : ℝ) ^ (τ * ρ) *
        eta diffusion T support ^ ρ
    else 0

/-- Reindex all coordinate subsets by their unique endpoint/detail decomposition. -/
theorem allSubsetTimeFactorSum_eq_pairSum
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T κ ρ τ : ℝ) :
    allSubsetTimeFactorSum (J := J) diffusion T κ ρ τ =
      ∑ endpoints : Finset (Fin noiseDim),
        ∑ details : Finset (DetailIndex J noiseDim),
          if (bridgeSubset endpoints details).Nonempty then
            κ ^ (endpoints.card + details.card) *
              ((endpoints.card + details.card).factorial : ℝ) ^ (τ * ρ) *
              eta diffusion T (bridgeSubset endpoints details) ^ ρ
          else 0 := by
  unfold allSubsetTimeFactorSum bridgeSubset
  have hsum := Equiv.sum_comp
    (Finset.sumEquiv (α := Fin noiseDim)
      (β := DetailIndex J noiseDim)).toEquiv.symm
    (fun support : Finset (Index J noiseDim) =>
      if support.Nonempty then
        κ ^ support.card * (support.card.factorial : ℝ) ^ (τ * ρ) *
          eta diffusion T support ^ ρ
      else 0)
  simpa [Finset.sumEquiv_symm_apply, Fintype.sum_prod_type] using hsum.symm

theorem endpointWeightedSum_eq_fintypeSum
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T κ ρ τ : ℝ) :
    endpointWeightedSum diffusion T κ ρ τ =
      ∑ endpoints : Finset (Fin noiseDim),
        κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
          ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ := by
  unfold endpointWeightedSum
  rw [Finset.powerset_univ]

theorem detailWeightedSum_eq_fintypeSum
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T κ ρ τ : ℝ) :
    detailWeightedSum (J := J) diffusion T κ ρ τ =
      ∑ details : Finset (DetailIndex J noiseDim),
        if details.Nonempty then
          κ ^ details.card * (details.card.factorial : ℝ) ^ (τ * ρ) *
            eta diffusion T (detailIndices details) ^ ρ
        else 0 := by
  unfold detailWeightedSum
  rw [Finset.powerset_univ, Finset.sum_filter]

/-- Pointwise endpoint/detail separation for a pair with nonempty detail part. -/
theorem bridge_pair_summand_le_of_details_nonempty
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hτρ : 0 ≤ τ * ρ) (endpoints : Finset (Fin noiseDim))
    (details : Finset (DetailIndex J noiseDim)) (hdetails : details.Nonempty) :
    κ ^ (endpoints.card + details.card) *
        ((endpoints.card + details.card).factorial : ℝ) ^ (τ * ρ) *
        eta diffusion T (bridgeSubset endpoints details) ^ ρ ≤
      (((2 : ℝ) ^ (τ * ρ) * κ) ^ endpoints.card *
          (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
          ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) *
        (((2 : ℝ) ^ (τ * ρ) * κ) ^ details.card *
          (details.card.factorial : ℝ) ^ (τ * ρ) *
          eta diffusion T (detailIndices details) ^ ρ) := by
  have hcard := combined_cardinality_weight_le hκ hτρ
    details.card endpoints.card
  have hcard' := combined_cardinality_weight_le hκ hτρ
    endpoints.card details.card
  have heta := eta_bridgeSubset_rpow_le diffusion hT hρ endpoints details
  have hweightNonneg : 0 ≤ κ ^ (endpoints.card + details.card) *
      ((endpoints.card + details.card).factorial : ℝ) ^ (τ * ρ) :=
    mul_nonneg (pow_nonneg hκ _) (Real.rpow_nonneg (by positivity) _)
  have hetaNonneg : 0 ≤ eta diffusion T (bridgeSubset endpoints details) ^ ρ :=
    Real.rpow_nonneg (eta_nonneg diffusion hT _) ρ
  have hseparatedNonneg : 0 ≤
      (((2 : ℝ) ^ (τ * ρ) * κ) ^ endpoints.card *
        (endpoints.card.factorial : ℝ) ^ (τ * ρ)) := by positivity
  calc
    κ ^ (endpoints.card + details.card) *
        ((endpoints.card + details.card).factorial : ℝ) ^ (τ * ρ) *
        eta diffusion T (bridgeSubset endpoints details) ^ ρ ≤
      ((((2 : ℝ) ^ (τ * ρ) * κ) ^ endpoints.card *
          (endpoints.card.factorial : ℝ) ^ (τ * ρ)) *
        (((2 : ℝ) ^ (τ * ρ) * κ) ^ details.card *
          (details.card.factorial : ℝ) ^ (τ * ρ))) *
        (eta diffusion T (detailIndices details) ^ ρ *
          ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) := by
      exact mul_le_mul hcard' heta hetaNonneg
        (by positivity)
    _ = _ := by ring

/-- Pointwise endpoint-only contribution, including the harmless empty/empty overbound. -/
theorem bridge_pair_summand_le_of_details_empty
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (endpoints : Finset (Fin noiseDim)) :
    (if (bridgeSubset endpoints (∅ : Finset (DetailIndex J noiseDim))).Nonempty then
      κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
        eta diffusion T (bridgeSubset (J := J) endpoints
          (∅ : Finset (DetailIndex J noiseDim))) ^ ρ
    else 0) ≤
      T ^ ρ *
        (κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
          ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) := by
  by_cases hendpoints : endpoints.Nonempty
  · have hbridge : (bridgeSubset endpoints
        (∅ : Finset (DetailIndex J noiseDim))).Nonempty := by
      rcases hendpoints with ⟨r, hr⟩
      exact ⟨Sum.inl r, by simp [bridgeSubset, hr]⟩
    rw [if_pos hbridge]
    have heta := eta_bridgeSubset_rpow_le diffusion hT hρ endpoints
      (∅ : Finset (DetailIndex J noiseDim))
    simp [detailIndices, eta_empty] at heta
    have hcommon : 0 ≤ κ ^ endpoints.card *
        (endpoints.card.factorial : ℝ) ^ (τ * ρ) := by
      exact mul_nonneg (pow_nonneg hκ _)
        (Real.rpow_nonneg (by positivity) _)
    calc
      κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
          eta diffusion T (bridgeSubset endpoints ∅) ^ ρ ≤
        κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
          (T ^ ρ * ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) :=
        mul_le_mul_of_nonneg_left heta hcommon
      _ = T ^ ρ *
          (κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
            ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ) := by ring
  · have hempty : endpoints = ∅ := Finset.not_nonempty_iff_eq_empty.mp hendpoints
    subst endpoints
    simp [bridgeSubset]
    exact Real.rpow_nonneg hT ρ

private theorem sum_finset_if_nonempty_else
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (c : ℝ) :
    (∑ s : Finset α, if s.Nonempty then f s else c) =
      (∑ s : Finset α, if s.Nonempty then f s else 0) + c := by
  classical
  calc
    (∑ s : Finset α, if s.Nonempty then f s else c) =
      ∑ s : Finset α,
        ((if s.Nonempty then f s else 0) + (if s = ∅ then c else 0)) := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases h : s.Nonempty
          · simp [h, Finset.nonempty_iff_ne_empty.mp h]
          · simp [h, Finset.not_nonempty_iff_eq_empty.mp h]
    _ = (∑ s : Finset α, if s.Nonempty then f s else 0) +
        ∑ s : Finset α, if s = ∅ then c else 0 := Finset.sum_add_distrib
    _ = (∑ s : Finset α, if s.Nonempty then f s else 0) + c := by
      rw [Finset.sum_ite_eq']
      simp

/-- The explicit uniform majorant used for Lemma 4.5. -/
def allSubsetSeriesConstant {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T κ ρ τ : ℝ) : ℝ :=
  let κ' := (2 : ℝ) ^ (τ * ρ) * κ
  endpointSeriesConstant diffusion T κ' ρ τ *
      detailSeriesConstant diffusion T κ' ρ τ +
    T ^ ρ * endpointSeriesConstant diffusion T κ' ρ τ

theorem endpointWeightedSum_nonneg
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (ρ τ : ℝ) :
    0 ≤ endpointWeightedSum diffusion T κ ρ τ := by
  unfold endpointWeightedSum
  apply Finset.sum_nonneg
  intro endpoints hendpoints
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hκ _)
      (Real.rpow_nonneg (by positivity) _))
    (Finset.prod_nonneg fun r hr =>
      Real.rpow_nonneg (endpointFactor_nonneg diffusion T r) ρ)

theorem detailWeightedSum_nonneg
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (ρ τ : ℝ) :
    0 ≤ detailWeightedSum (J := J) diffusion T κ ρ τ := by
  unfold detailWeightedSum
  apply Finset.sum_nonneg
  intro details hdetails
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hκ _)
      (Real.rpow_nonneg (by positivity) _))
    (Real.rpow_nonneg (eta_nonneg diffusion hT _) ρ)

theorem endpointSeriesConstant_nonneg
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (ρ τ : ℝ) :
    0 ≤ endpointSeriesConstant diffusion T κ ρ τ := by
  unfold endpointSeriesConstant factorialDecaySeries
  exact tsum_nonneg fun n => mul_nonneg
    (pow_nonneg (endpointSeriesBase_pos diffusion hT hκ ρ).le n)
    (Real.rpow_nonneg (by positivity) _)

theorem detailSeriesConstant_nonneg
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (τ : ℝ) :
    0 ≤ detailSeriesConstant diffusion T κ ρ τ := by
  unfold detailSeriesConstant factorialDecaySeries
  exact tsum_nonneg fun n => mul_nonneg
    (pow_nonneg (detailSeriesBase_pos diffusion hT hκ hρ).le n)
    (Real.rpow_nonneg (by positivity) _)

/-- Lemma 4.5: uniform summability over every nonempty endpoint/detail subset. -/
theorem allSubsetTimeFactorSum_le_seriesConstant
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (hτ : 0 ≤ τ) (hτρ : τ * ρ < 1) :
    allSubsetTimeFactorSum (J := J) diffusion T κ ρ τ ≤
      allSubsetSeriesConstant diffusion T κ ρ τ := by
  classical
  let κ' := (2 : ℝ) ^ (τ * ρ) * κ
  let endpointTerm : Finset (Fin noiseDim) → ℝ := fun endpoints =>
    κ' ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
      ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ
  let detailTerm : Finset (DetailIndex J noiseDim) → ℝ := fun details =>
    κ' ^ details.card * (details.card.factorial : ℝ) ^ (τ * ρ) *
      eta diffusion T (detailIndices details) ^ ρ
  have hρ0 : 0 ≤ ρ := by linarith
  have hτρ0 : 0 ≤ τ * ρ := mul_nonneg hτ hρ0
  have hκ' : 0 ≤ κ' := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hκ
  rw [allSubsetTimeFactorSum_eq_pairSum]
  calc
    (∑ endpoints : Finset (Fin noiseDim),
        ∑ details : Finset (DetailIndex J noiseDim),
          if (bridgeSubset endpoints details).Nonempty then
            κ ^ (endpoints.card + details.card) *
              ((endpoints.card + details.card).factorial : ℝ) ^ (τ * ρ) *
              eta diffusion T (bridgeSubset endpoints details) ^ ρ
          else 0) ≤
      ∑ endpoints : Finset (Fin noiseDim),
        ∑ details : Finset (DetailIndex J noiseDim),
          if details.Nonempty then endpointTerm endpoints * detailTerm details
          else T ^ ρ * endpointTerm endpoints := by
      apply Finset.sum_le_sum
      intro endpoints hendpoints
      apply Finset.sum_le_sum
      intro details hdetails
      by_cases hd : details.Nonempty
      · have hbridge : (bridgeSubset endpoints details).Nonempty := by
          rcases hd with ⟨j, hj⟩
          exact ⟨Sum.inr j, by simp [bridgeSubset, hj]⟩
        rw [if_pos hbridge, if_pos hd]
        simpa [endpointTerm, detailTerm, κ'] using
          bridge_pair_summand_le_of_details_nonempty diffusion hT.le hκ hρ0
            hτρ0 endpoints details hd
      · have hempty := Finset.not_nonempty_iff_eq_empty.mp hd
        subst details
        have hemptyBound := bridge_pair_summand_le_of_details_empty
          (J := J) (τ := τ) diffusion hT.le hκ hρ0 endpoints
        have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (τ * ρ) :=
          Real.one_le_rpow (by norm_num) hτρ0
        have hκle : κ ≤ κ' := by
          unfold κ'
          nlinarith [mul_le_mul_of_nonneg_right hone hκ]
        have hweight :
            κ ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
                ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ ≤
              κ' ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
                ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ := by
          have hpow := pow_le_pow_left₀ hκ hκle endpoints.card
          have hfactorial : 0 ≤ (endpoints.card.factorial : ℝ) ^ (τ * ρ) :=
            Real.rpow_nonneg (by positivity) _
          have hprod : 0 ≤ ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ :=
            Finset.prod_nonneg fun r hr =>
              Real.rpow_nonneg (endpointFactor_nonneg diffusion T r) ρ
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpow hfactorial) hprod
        exact hemptyBound.trans
          (mul_le_mul_of_nonneg_left hweight (Real.rpow_nonneg hT.le ρ))
    _ = endpointWeightedSum diffusion T κ' ρ τ *
          detailWeightedSum (J := J) diffusion T κ' ρ τ +
        T ^ ρ * endpointWeightedSum diffusion T κ' ρ τ := by
      have hinner (endpoints : Finset (Fin noiseDim)) :
          (∑ details : Finset (DetailIndex J noiseDim),
            if details.Nonempty then endpointTerm endpoints * detailTerm details else 0) =
          endpointTerm endpoints *
            detailWeightedSum (J := J) diffusion T κ' ρ τ := by
        rw [detailWeightedSum_eq_fintypeSum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro details hdetails
        by_cases hd : details.Nonempty
        · simp only [if_pos hd]
          rfl
        · simp only [if_neg hd, mul_zero]
      calc
        (∑ endpoints : Finset (Fin noiseDim),
            ∑ details : Finset (DetailIndex J noiseDim),
              if details.Nonempty then endpointTerm endpoints * detailTerm details
              else T ^ ρ * endpointTerm endpoints) =
          ∑ endpoints : Finset (Fin noiseDim),
            ((∑ details : Finset (DetailIndex J noiseDim),
              if details.Nonempty then endpointTerm endpoints * detailTerm details else 0) +
              T ^ ρ * endpointTerm endpoints) := by
            apply Finset.sum_congr rfl
            intro endpoints hendpoints
            exact sum_finset_if_nonempty_else
              (fun details => endpointTerm endpoints * detailTerm details)
              (T ^ ρ * endpointTerm endpoints)
        _ = ∑ endpoints : Finset (Fin noiseDim),
            (endpointTerm endpoints *
                detailWeightedSum (J := J) diffusion T κ' ρ τ +
              T ^ ρ * endpointTerm endpoints) := by
            apply Finset.sum_congr rfl
            intro endpoints hendpoints
            rw [hinner]
        _ = endpointWeightedSum diffusion T κ' ρ τ *
              detailWeightedSum (J := J) diffusion T κ' ρ τ +
            T ^ ρ * endpointWeightedSum diffusion T κ' ρ τ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
          rw [← endpointWeightedSum_eq_fintypeSum diffusion T κ' ρ τ]
    _ ≤ endpointSeriesConstant diffusion T κ' ρ τ *
          detailSeriesConstant diffusion T κ' ρ τ +
        T ^ ρ * endpointSeriesConstant diffusion T κ' ρ τ := by
      have hE := endpointWeightedSum_le_seriesConstant diffusion hT.le hκ' hτρ
      have hD := detailWeightedSum_le_seriesConstant
        (J := J) diffusion hT hκ' hρ hτρ
      have hEnonneg := endpointWeightedSum_nonneg diffusion hT.le hκ' ρ τ
      have hDnonneg := detailWeightedSum_nonneg (J := J) diffusion hT.le hκ' ρ τ
      have hECnonneg := endpointSeriesConstant_nonneg diffusion hT.le hκ' ρ τ
      exact add_le_add
        (mul_le_mul hE hD hDnonneg hECnonneg)
        (mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hT.le ρ))
    _ = allSubsetSeriesConstant diffusion T κ ρ τ := rfl

end

end TimeDependentLattice.Regularity
