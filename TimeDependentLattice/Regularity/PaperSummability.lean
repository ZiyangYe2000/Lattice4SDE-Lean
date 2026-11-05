/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Regularity.AllSubsetSummability

/-!
# The exact endpoint and detail series of the paper

The series and `C_H` in the proof of Lemma 4.5 are retained literally. The older,
larger series remain useful auxiliary majorants for establishing convergence.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open scoped BigOperators
open TimeDependentLattice TimeDependentLattice.BrownianBridge

/-- The square-root form of `A_{ρ,T}` is exactly the displayed power form in the paper. -/
theorem detailSummabilityA_eq_paper {T ρ : ℝ} (hT : 0 ≤ T) :
    detailSummabilityA T ρ =
      (2 : ℝ) ^ (-ρ) * T ^ (ρ / 2) / (1 - (2 : ℝ) ^ (-ρ / 2)) := by
  unfold detailSummabilityA
  rw [Real.div_rpow (Real.sqrt_nonneg T) (by norm_num : (0 : ℝ) ≤ 2) ρ,
    ← Real.rpow_div_two_eq_sqrt ρ hT, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ρ]
  ring

/-- The endpoint series `H_*^E(κ)` in the paper. -/
def paperEndpointSeries (T κ ρ τ Θ : ℝ) : ℝ :=
  ∑' n : ℕ, (κ * T ^ (ρ / 2) * Θ) ^ n * (n.factorial : ℝ) ^ (τ * ρ - 1)

/-- The detail series `H_*^J(κ)` in the paper; its zero term vanishes. -/
def paperDetailSeries (T κ ρ τ Θ : ℝ) : ℝ :=
  ∑' n : ℕ, (κ * detailSummabilityConstant T ρ * Θ) ^ n * n *
    (n.factorial : ℝ) ^ (τ * ρ - 1)

/-- The exact `C_H` chosen in the proof of Lemma 4.5 of the paper. -/
def paperTimeFactorConstant (T κ ρ τ Θ : ℝ) : ℝ :=
  let κ' := (2 : ℝ) ^ (τ * ρ) * κ
  paperEndpointSeries T κ ρ τ Θ +
    paperDetailSeries T κ' ρ τ Θ * paperEndpointSeries T κ' ρ τ Θ +
    T ^ ρ * (paperEndpointSeries T κ ρ τ Θ - 1)

private theorem summable_factorialDecay_nonneg {A q : ℝ} (hA : 0 ≤ A) (hq : q < 1) :
    Summable (fun n : ℕ ↦ A ^ n * (n.factorial : ℝ) ^ (q - 1)) := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (pow_nonneg hA n) (Real.rpow_nonneg (by positivity) _))
    (fun n ↦ mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hA (show A ≤ 1 + A by linarith) n)
      (Real.rpow_nonneg (by positivity) _))
    (summable_factorialDecaySeries (by linarith : 0 < 1 + A) hq)

private theorem summable_nat_mul_factorialDecay {A q : ℝ} (hA : 0 ≤ A) (hq : q < 1) :
    Summable (fun n : ℕ ↦ A ^ n * n * (n.factorial : ℝ) ^ (q - 1)) := by
  have hdom := summable_factorialDecay_nonneg
    (show (0 : ℝ) ≤ 2 * A by positivity) hq
  apply Summable.of_nonneg_of_le
    (fun n ↦ by positivity) (fun n ↦ ?_) hdom
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self.le : n ≤ 2 ^ n)
  have hpow : A ^ n * n ≤ (2 * A) ^ n := by
    rw [mul_pow]
    nlinarith [pow_nonneg hA n]
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)

theorem paperEndpointSeries_summable {T κ ρ τ Θ : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hΘ : 0 ≤ Θ) (hτρ : τ * ρ < 1) :
    Summable (fun n : ℕ ↦
      (κ * T ^ (ρ / 2) * Θ) ^ n * (n.factorial : ℝ) ^ (τ * ρ - 1)) :=
  summable_factorialDecay_nonneg (by positivity) hτρ

theorem paperDetailSeries_summable {T κ ρ τ Θ : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hΘ : 0 ≤ Θ) (hρ : 2 / 3 < ρ)
    (hτρ : τ * ρ < 1) :
    Summable (fun n : ℕ ↦ (κ * detailSummabilityConstant T ρ * Θ) ^ n * n *
      (n.factorial : ℝ) ^ (τ * ρ - 1)) := by
  apply summable_nat_mul_factorialDecay _ hτρ
  exact mul_nonneg (mul_nonneg hκ (detailSummabilityConstant_nonneg hT hρ)) hΘ

theorem paperEndpointSeries_nonneg {T κ ρ τ Θ : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hΘ : 0 ≤ Θ) :
    0 ≤ paperEndpointSeries T κ ρ τ Θ :=
  tsum_nonneg (fun n ↦ by positivity)

theorem paperDetailSeries_nonneg {T κ ρ τ Θ : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hΘ : 0 ≤ Θ) (hρ : 2 / 3 < ρ) :
    0 ≤ paperDetailSeries T κ ρ τ Θ := by
  unfold paperDetailSeries
  have hC := detailSummabilityConstant_nonneg hT hρ
  exact tsum_nonneg (fun n ↦ by positivity)

theorem one_le_paperEndpointSeries {T κ ρ τ Θ : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hΘ : 0 ≤ Θ) (hτρ : τ * ρ < 1) :
    1 ≤ paperEndpointSeries T κ ρ τ Θ := by
  have hs := paperEndpointSeries_summable hT hκ hΘ hτρ
  simpa [paperEndpointSeries] using
    hs.sum_le_tsum ({0} : Finset ℕ) (fun n _ ↦ by positivity)

theorem paperEndpointSeries_mono {T κ κ' ρ τ Θ Θ' : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hκκ : κ ≤ κ') (hΘ : 0 ≤ Θ) (hΘΘ : Θ ≤ Θ')
    (hτρ : τ * ρ < 1) :
    paperEndpointSeries T κ ρ τ Θ ≤ paperEndpointSeries T κ' ρ τ Θ' := by
  apply Summable.tsum_le_tsum _
    (paperEndpointSeries_summable hT hκ hΘ hτρ)
    (paperEndpointSeries_summable hT (hκ.trans hκκ) (hΘ.trans hΘΘ) hτρ)
  intro n
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hκκ (Real.rpow_nonneg hT _)) hΘΘ hΘ
    (mul_nonneg (hκ.trans hκκ) (Real.rpow_nonneg hT _))

theorem paperDetailSeries_mono {T κ κ' ρ τ Θ Θ' : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hκκ : κ ≤ κ') (hΘ : 0 ≤ Θ) (hΘΘ : Θ ≤ Θ')
    (hρ : 2 / 3 < ρ) (hτρ : τ * ρ < 1) :
    paperDetailSeries T κ ρ τ Θ ≤ paperDetailSeries T κ' ρ τ Θ' := by
  have hC := detailSummabilityConstant_nonneg hT hρ
  apply Summable.tsum_le_tsum _
    (paperDetailSeries_summable hT hκ hΘ hρ hτρ)
    (paperDetailSeries_summable hT (hκ.trans hκκ) (hΘ.trans hΘΘ) hρ hτρ)
  intro n
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hκκ hC) hΘΘ hΘ
    (mul_nonneg (hκ.trans hκκ) hC)

theorem one_le_paperTimeFactorConstant {T κ ρ τ Θ : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hΘ : 0 ≤ Θ) (hρ : 2 / 3 < ρ)
    (hτρ : τ * ρ < 1) :
    1 ≤ paperTimeFactorConstant T κ ρ τ Θ := by
  have hE := one_le_paperEndpointSeries hT hκ hΘ hτρ
  have hκ' : 0 ≤ (2 : ℝ) ^ (τ * ρ) * κ := by positivity
  have hE' := paperEndpointSeries_nonneg (τ := τ) (ρ := ρ) hT hκ' hΘ
  have hJ' := paperDetailSeries_nonneg (τ := τ) hT hκ' hΘ hρ
  unfold paperTimeFactorConstant
  nlinarith [mul_nonneg hJ' hE', mul_nonneg (Real.rpow_nonneg hT ρ) (sub_nonneg.mpr hE)]

theorem paperTimeFactorConstant_mono {T κ κ' ρ τ Θ Θ' : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hκκ : κ ≤ κ') (hΘ : 0 ≤ Θ) (hΘΘ : Θ ≤ Θ')
    (hρ : 2 / 3 < ρ) (hτρ : τ * ρ < 1) :
    paperTimeFactorConstant T κ ρ τ Θ ≤ paperTimeFactorConstant T κ' ρ τ Θ' := by
  have hE := paperEndpointSeries_mono hT hκ hκκ hΘ hΘΘ hτρ
  have hsκ : 0 ≤ (2 : ℝ) ^ (τ * ρ) * κ := by positivity
  have hsκκ := mul_le_mul_of_nonneg_left hκκ
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (τ * ρ))
  have hEs := paperEndpointSeries_mono hT hsκ hsκκ hΘ hΘΘ hτρ
  have hJs := paperDetailSeries_mono hT hsκ hsκκ hΘ hΘΘ hρ hτρ
  have hprod := mul_le_mul hJs hEs
    (paperEndpointSeries_nonneg (τ := τ) (ρ := ρ) hT hsκ hΘ)
    (paperDetailSeries_nonneg (τ := τ) hT (hsκ.trans hsκκ) (hΘ.trans hΘΘ) hρ)
  have hlast := mul_le_mul_of_nonneg_left (sub_le_sub_right hE 1)
    (Real.rpow_nonneg hT ρ)
  exact add_le_add (add_le_add hE hprod) hlast

@[simp] theorem paperEndpointSeries_zero_theta (T κ ρ τ : ℝ) :
    paperEndpointSeries T κ ρ τ 0 = 1 := by
  unfold paperEndpointSeries
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

@[simp] theorem paperDetailSeries_zero_theta (T κ ρ τ : ℝ) :
    paperDetailSeries T κ ρ τ 0 = 0 := by
  unfold paperDetailSeries
  have hz : (fun n : ℕ ↦ (κ * detailSummabilityConstant T ρ * 0) ^ n * n *
      (n.factorial : ℝ) ^ (τ * ρ - 1)) = 0 := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [zero_pow hn]
  rw [hz]
  exact tsum_zero

@[simp] theorem paperTimeFactorConstant_zero_theta (T κ ρ τ : ℝ) :
    paperTimeFactorConstant T κ ρ τ 0 = 1 := by
  simp [paperTimeFactorConstant]

private theorem weighted_factorial_div_eq
    (κ X q : ℝ) (n : ℕ) :
    κ ^ n * (n.factorial : ℝ) ^ q * (X ^ n / n.factorial) =
      (κ * X) ^ n * (n.factorial : ℝ) ^ (q - 1) := by
  rw [Real.rpow_sub_one (by positivity : (n.factorial : ℝ) ≠ 0)]
  rw [mul_pow]
  field_simp

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

theorem endpointWeightedSum_le_paperEndpointSeries
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hτρ : τ * ρ < 1) :
    endpointWeightedSum diffusion T κ ρ τ ≤
      paperEndpointSeries T κ ρ τ (columnRhoSum diffusion ρ) := by
  classical
  let X := (√T) ^ ρ * columnRhoSum diffusion ρ
  let A := κ * X
  have hX : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg T) ρ)
    (columnRhoSum_nonneg diffusion ρ)
  have hbase : κ * X ≤ A := le_rfl
  have hA : 0 ≤ A := mul_nonneg hκ hX
  have hsummable := summable_factorialDecay_nonneg hA hτρ
  unfold endpointWeightedSum paperEndpointSeries
  rw [Real.rpow_div_two_eq_sqrt ρ hT]
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
    _ = _ := by simp [A, X, mul_assoc]

theorem detailWeightedSum_le_paperDetailSeries
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (hτρ : τ * ρ < 1) :
    detailWeightedSum (J := J) diffusion T κ ρ τ ≤
      paperDetailSeries T κ ρ τ (columnRhoSum diffusion ρ) := by
  classical
  let CΘ := detailSummabilityConstant T ρ * columnRhoSum diffusion ρ
  let A := κ * CΘ
  have hCΘ : 0 ≤ CΘ := mul_nonneg
    (detailSummabilityConstant_nonneg hT.le hρ)
    (columnRhoSum_nonneg diffusion ρ)
  have hA : 0 ≤ A := mul_nonneg hκ hCΘ
  have hsummable := summable_nat_mul_factorialDecay hA hτρ
  unfold detailWeightedSum paperDetailSeries
  rw [show κ * detailSummabilityConstant T ρ * columnRhoSum diffusion ρ = A by
    dsimp [A, CΘ]; ring]
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
        A ^ n * n * (n.factorial : ℝ) ^ (τ * ρ - 1) := by
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
              rw [ite_eq_left hnonempty, hcard]
          _ ≤ κ ^ n * (n.factorial : ℝ) ^ (τ * ρ) *
              (CΘ ^ n / (n - 1).factorial) :=
            mul_le_mul_of_nonneg_left hfixed hcommon
          _ = (κ * CΘ) ^ n * n *
              (n.factorial : ℝ) ^ (τ * ρ - 1) :=
            weighted_factorial_pred_div_eq κ CΘ (τ * ρ) n hn
          _ = A ^ n * n * (n.factorial : ℝ) ^ (τ * ρ - 1) := rfl
    _ ≤ ∑' n : ℕ, A ^ n * n * (n.factorial : ℝ) ^ (τ * ρ - 1) := by
      exact hsummable.sum_le_tsum _ (fun n hn =>
        by positivity)


private theorem sum_nonempty_add_empty
    {α : Type*} [Fintype α] (f : Finset α → ℝ) :
    (∑ s : Finset α, if s.Nonempty then f s else 0) + f ∅ = ∑ s : Finset α, f s := by
  classical
  calc
    (∑ s : Finset α, if s.Nonempty then f s else 0) + f ∅ =
        (∑ s : Finset α, if s.Nonempty then f s else 0) +
          ∑ s : Finset α, if s = ∅ then f ∅ else 0 := by simp
    _ = ∑ s : Finset α,
        ((if s.Nonempty then f s else 0) + (if s = ∅ then f ∅ else 0)) :=
      Finset.sum_add_distrib.symm
    _ = ∑ s : Finset α, f s := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hn : s.Nonempty
      · simp [hn, Finset.nonempty_iff_ne_empty.mp hn]
      · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

/-- The exact endpoint/detail separation before passing from finite sums to series.
The empty endpoint set is excluded from the detail-free contribution. -/
theorem allSubsetTimeFactorSum_le_finite_paper_bound
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) :
    allSubsetTimeFactorSum (J := J) diffusion T κ ρ τ ≤
      let κ' := (2 : ℝ) ^ (τ * ρ) * κ
      endpointWeightedSum diffusion T κ' ρ τ *
          detailWeightedSum (J := J) diffusion T κ' ρ τ +
        T ^ ρ * (endpointWeightedSum diffusion T κ ρ τ - 1) := by
  classical
  let κ' := (2 : ℝ) ^ (τ * ρ) * κ
  let e : Finset (Fin noiseDim) → ℝ := fun E ↦
    κ ^ E.card * (E.card.factorial : ℝ) ^ (τ * ρ) *
      ∏ r ∈ E, endpointFactor diffusion T r ^ ρ
  let e' : Finset (Fin noiseDim) → ℝ := fun E ↦
    κ' ^ E.card * (E.card.factorial : ℝ) ^ (τ * ρ) *
      ∏ r ∈ E, endpointFactor diffusion T r ^ ρ
  let d' : Finset (DetailIndex J noiseDim) → ℝ := fun D ↦
    κ' ^ D.card * (D.card.factorial : ℝ) ^ (τ * ρ) *
      eta diffusion T (detailIndices D) ^ ρ
  have hse : (∑ E : Finset (Fin noiseDim), e E) =
      endpointWeightedSum diffusion T κ ρ τ :=
    (endpointWeightedSum_eq_fintypeSum diffusion T κ ρ τ).symm
  have hse' : (∑ E : Finset (Fin noiseDim), e' E) =
      endpointWeightedSum diffusion T κ' ρ τ :=
    (endpointWeightedSum_eq_fintypeSum diffusion T κ' ρ τ).symm
  have hsd' : (∑ D : Finset (DetailIndex J noiseDim), if D.Nonempty then d' D else 0) =
      detailWeightedSum (J := J) diffusion T κ' ρ τ :=
    (detailWeightedSum_eq_fintypeSum diffusion T κ' ρ τ).symm
  have hse_nonempty : (∑ E : Finset (Fin noiseDim), if E.Nonempty then e E else 0) =
      endpointWeightedSum diffusion T κ ρ τ - 1 := by
    have hs := sum_nonempty_add_empty e
    have he : e ∅ = 1 := by simp [e]
    rw [he, hse] at hs
    linarith
  rw [allSubsetTimeFactorSum_eq_pairSum]
  calc
    (∑ E : Finset (Fin noiseDim), ∑ D : Finset (DetailIndex J noiseDim),
      if (bridgeSubset E D).Nonempty then
        κ ^ (E.card + D.card) * ((E.card + D.card).factorial : ℝ) ^ (τ * ρ) *
          eta diffusion T (bridgeSubset E D) ^ ρ else 0) ≤
      ∑ E : Finset (Fin noiseDim), ∑ D : Finset (DetailIndex J noiseDim),
        ((if D.Nonempty then e' E * d' D else 0) +
          (if D = ∅ then (if E.Nonempty then T ^ ρ * e E else 0) else 0)) := by
      apply Finset.sum_le_sum
      intro E hE
      apply Finset.sum_le_sum
      intro D hD
      by_cases hd : D.Nonempty
      · have hb : (bridgeSubset E D).Nonempty := by
          obtain ⟨j, hj⟩ := hd
          exact ⟨Sum.inr j, by simp [bridgeSubset, hj]⟩
        simp only [hb, hd, Finset.nonempty_iff_ne_empty.mp hd, ite_true, ite_false, add_zero]
        exact bridge_pair_summand_le_of_details_nonempty diffusion hT hκ hρ
          (mul_nonneg hτ hρ) E D hd
      · have hd0 := Finset.not_nonempty_iff_eq_empty.mp hd
        subst D
        by_cases he : E.Nonempty
        · simpa [e, he] using bridge_pair_summand_le_of_details_empty
            (J := J) (τ := τ) diffusion hT hκ hρ E
        · have he0 := Finset.not_nonempty_iff_eq_empty.mp he
          subst E
          simp [bridgeSubset]
    _ = endpointWeightedSum diffusion T κ' ρ τ *
          detailWeightedSum (J := J) diffusion T κ' ρ τ +
        T ^ ρ * (endpointWeightedSum diffusion T κ ρ τ - 1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have hinner (E : Finset (Fin noiseDim)) :
          (∑ D : Finset (DetailIndex J noiseDim), if D.Nonempty then e' E * d' D else 0) =
            e' E * detailWeightedSum (J := J) diffusion T κ' ρ τ := by
        rw [← hsd', Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D hD
        split_ifs <;> simp
      simp_rw [hinner]
      rw [← Finset.sum_mul, hse']
      congr 1
      rw [← hse_nonempty, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      split_ifs <;> simp

theorem allSubsetTimeFactorSum_le_paper_series
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (hτ : 0 ≤ τ) (hτρ : τ * ρ < 1) :
    allSubsetTimeFactorSum (J := J) diffusion T κ ρ τ ≤
      let κ' := (2 : ℝ) ^ (τ * ρ) * κ
      paperDetailSeries T κ' ρ τ (columnRhoSum diffusion ρ) *
          paperEndpointSeries T κ' ρ τ (columnRhoSum diffusion ρ) +
        T ^ ρ * (paperEndpointSeries T κ ρ τ (columnRhoSum diffusion ρ) - 1) := by
  let κ' := (2 : ℝ) ^ (τ * ρ) * κ
  have hκ' : 0 ≤ κ' := by dsimp [κ']; positivity
  have hE := endpointWeightedSum_le_paperEndpointSeries diffusion hT.le hκ' hτρ
  have hD := detailWeightedSum_le_paperDetailSeries (J := J) diffusion hT hκ' hρ hτρ
  have hE0 := endpointWeightedSum_le_paperEndpointSeries diffusion hT.le hκ hτρ
  have hm := mul_le_mul hE hD
    (detailWeightedSum_nonneg (J := J) diffusion hT.le hκ' ρ τ)
    (paperEndpointSeries_nonneg (τ := τ) (ρ := ρ) hT.le hκ'
      (columnRhoSum_nonneg diffusion ρ))
  have ht := mul_le_mul_of_nonneg_left (sub_le_sub_right hE0 1)
    (Real.rpow_nonneg hT.le ρ)
  have hb := allSubsetTimeFactorSum_le_finite_paper_bound (J := J) diffusion hT.le hκ
    (by linarith : 0 ≤ ρ) hτ
  exact hb.trans (by simpa [κ', mul_comm] using add_le_add hm ht)

theorem endpointWeightedSum_le_paperTimeFactorConstant
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (_hτ : 0 ≤ τ) (hτρ : τ * ρ < 1) :
    endpointWeightedSum diffusion T κ ρ τ ≤
      paperTimeFactorConstant T κ ρ τ (columnRhoSum diffusion ρ) := by
  have hE := endpointWeightedSum_le_paperEndpointSeries diffusion hT.le hκ hτρ
  have hΘ := columnRhoSum_nonneg diffusion ρ
  have hE1 := one_le_paperEndpointSeries hT.le hκ hΘ hτρ
  have hκ' : 0 ≤ (2 : ℝ) ^ (τ * ρ) * κ := by positivity
  have hEs := paperEndpointSeries_nonneg (τ := τ) (ρ := ρ) hT.le hκ' hΘ
  have hJs := paperDetailSeries_nonneg (τ := τ) hT.le hκ' hΘ hρ
  unfold paperTimeFactorConstant
  nlinarith [mul_nonneg hJs hEs,
    mul_nonneg (Real.rpow_nonneg hT.le ρ) (sub_nonneg.mpr hE1)]

theorem allSubsetTimeFactorSum_le_paperTimeFactorConstant
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T κ ρ τ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hρ : 2 / 3 < ρ)
    (hτ : 0 ≤ τ) (hτρ : τ * ρ < 1) :
    allSubsetTimeFactorSum (J := J) diffusion T κ ρ τ ≤
      paperTimeFactorConstant T κ ρ τ (columnRhoSum diffusion ρ) := by
  have hb := allSubsetTimeFactorSum_le_paper_series (J := J) diffusion hT hκ hρ hτ hτρ
  have hE := paperEndpointSeries_nonneg (τ := τ) (ρ := ρ) hT.le hκ
    (columnRhoSum_nonneg diffusion ρ)
  unfold paperTimeFactorConstant
  linarith

end

end TimeDependentLattice.Regularity
