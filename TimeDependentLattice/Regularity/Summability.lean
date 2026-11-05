/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform summability of normalized mixed derivatives

This file contains the final exponent-lifting step in paper Theorem 4.1.  The difficult tree
and Brownian-bridge estimates provide a uniform `ρ`-sum with `2 / 3 < ρ < p`; the argument here
turns that estimate into the asserted `p`-sum without a dimension-dependent factor.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open scoped BigOperators

/-- For `q ≥ 1`, the `q`-power sum of finitely many nonnegative numbers is bounded by the
`q`-power of their sum. -/
theorem sum_rpow_le_rpow_sum {α : Type*} (entries : Finset α) (value : α → ℝ)
    {q : ℝ} (hq : 1 ≤ q) (hvalue : ∀ entry ∈ entries, 0 ≤ value entry) :
    ∑ entry ∈ entries, value entry ^ q ≤ (∑ entry ∈ entries, value entry) ^ q := by
  let total := ∑ entry ∈ entries, value entry
  have htotal : 0 ≤ total := Finset.sum_nonneg hvalue
  have hpoint : ∀ entry ∈ entries,
      value entry ^ q ≤ value entry * total ^ (q - 1) := by
    intro entry hentry
    have hentryNonneg := hvalue entry hentry
    have hentryLe : value entry ≤ total :=
      Finset.single_le_sum (fun other hother => hvalue other hother) hentry
    have hexponent : 0 ≤ q - 1 := sub_nonneg.mpr hq
    calc
      value entry ^ q = value entry * value entry ^ (q - 1) := by
        calc
          value entry ^ q = value entry ^ ((q - 1) + 1) := by congr 1 <;> linarith
          _ = value entry ^ (q - 1) * value entry ^ (1 : ℝ) :=
            Real.rpow_add_of_nonneg hentryNonneg hexponent zero_le_one
          _ = value entry * value entry ^ (q - 1) := by
            rw [Real.rpow_one, mul_comm]
      _ ≤ value entry * total ^ (q - 1) := by
        gcongr
  calc
    ∑ entry ∈ entries, value entry ^ q ≤
        ∑ entry ∈ entries, value entry * total ^ (q - 1) :=
      Finset.sum_le_sum fun entry hentry => hpoint entry hentry
    _ = total * total ^ (q - 1) := by
      rw [← Finset.sum_mul]
    _ = total ^ q := by
      calc
        total * total ^ (q - 1) = total ^ (q - 1) * total ^ (1 : ℝ) := by
          rw [Real.rpow_one, mul_comm]
        _ = total ^ ((q - 1) + 1) :=
          (Real.rpow_add_of_nonneg htotal (sub_nonneg.mpr hq) zero_le_one).symm
        _ = total ^ q := by congr 1 <;> linarith

/-- The finite-dimensional `ℓ^ρ` to `ℓ^p` estimate used in the last paragraph of the proof of
Theorem 4.1. -/
theorem sum_rpow_lift {α : Type*} (entries : Finset α) (value : α → ℝ)
    {ρ p bound : ℝ} (hρ : 0 < ρ) (hρp : ρ < p)
    (hvalue : ∀ entry ∈ entries, 0 ≤ value entry)
    (hsum : ∑ entry ∈ entries, value entry ^ ρ ≤ bound) :
    ∑ entry ∈ entries, value entry ^ p ≤ bound ^ (p / ρ) := by
  have hq : 1 ≤ p / ρ := by
    rw [le_div_iff₀ hρ]
    simpa using le_of_lt hρp
  have hpowered : ∀ entry ∈ entries, 0 ≤ value entry ^ ρ := by
    intro entry hentry
    exact Real.rpow_nonneg (hvalue entry hentry) ρ
  calc
    ∑ entry ∈ entries, value entry ^ p =
        ∑ entry ∈ entries, (value entry ^ ρ) ^ (p / ρ) := by
      apply Finset.sum_congr rfl
      intro entry hentry
      rw [← Real.rpow_mul (hvalue entry hentry)]
      congr 2
      field_simp
    _ ≤ (∑ entry ∈ entries, value entry ^ ρ) ^ (p / ρ) :=
      sum_rpow_le_rpow_sum entries (fun entry => value entry ^ ρ) hq hpowered
    _ ≤ bound ^ (p / ρ) := by
      exact Real.rpow_le_rpow (Finset.sum_nonneg hpowered) hsum (by positivity)

/-- The weighted mixed-derivative sum over all nonempty coordinate subsets. -/
def weightedDerivativeSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ p : ℝ) (derivativeEnvelope : Finset ι → ℝ) : ℝ :=
  ∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι => u.Nonempty),
    κ ^ u.card * derivativeEnvelope u ^ p

/-- The intermediate exponent selected in the proof of Theorem 4.1. -/
def intermediateExponent (τ p : ℝ) : ℝ :=
  ((2 : ℝ) / 3 + min p (1 / τ)) / 2

/-- The paper's choice of intermediate exponent lies strictly between the critical exponent
`2 / 3` and both upper constraints `p` and `1 / τ`. -/
theorem intermediateExponent_spec {τ p : ℝ}
    (hτone : 1 ≤ τ) (hτ : τ < 3 / 2) (hp : 2 / 3 < p) :
    2 / 3 < intermediateExponent τ p ∧
      intermediateExponent τ p < p ∧
      intermediateExponent τ p < 1 / τ ∧
      0 < intermediateExponent τ p := by
  have hτpos : 0 < τ := zero_lt_one.trans_le hτone
  have hcriticalInv : (2 : ℝ) / 3 < 1 / τ := by
    rw [lt_div_iff₀ hτpos]
    nlinarith
  have hcriticalMin : (2 : ℝ) / 3 < min p (1 / τ) :=
    lt_min hp hcriticalInv
  have havgLower : (2 : ℝ) / 3 < intermediateExponent τ p := by
    unfold intermediateExponent
    linarith
  have havgUpper : intermediateExponent τ p < min p (1 / τ) := by
    unfold intermediateExponent
    linarith
  exact ⟨havgLower, havgUpper.trans_le (min_le_left _ _),
    havgUpper.trans_le (min_le_right _ _), (by linarith)⟩

/-- The factorial-decay series appearing in Equation (4.17). -/
def factorialDecaySeries (A q : ℝ) : ℝ :=
  ∑' k : ℕ, A ^ k * (k.factorial : ℝ) ^ (q - 1)

/-- The factorial-decay series converges for every positive geometric factor as soon as
`q < 1`.  This is the ratio-test argument written below Equation (4.17). -/
theorem summable_factorialDecaySeries {A q : ℝ} (hA : 0 < A) (hq : q < 1) :
    Summable (fun k : ℕ => A ^ k * (k.factorial : ℝ) ^ (q - 1)) := by
  let term : ℕ → ℝ := fun k => A ^ k * (k.factorial : ℝ) ^ (q - 1)
  have hterm : ∀ k, term k ≠ 0 := by
    intro k
    exact mul_ne_zero (pow_ne_zero _ hA.ne')
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hratio (k : ℕ) : ‖term (k + 1)‖ / ‖term k‖ =
      A * ((k + 1 : ℕ) : ℝ) ^ (q - 1) := by
    dsimp [term]
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ k + 1)
        (by positivity : (0 : ℝ) ≤ k.factorial)]
    field_simp
  have hbase : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hpower : Filter.Tendsto
      (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (q - 1))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hq)).comp hbase
    convert h using 1
    · funext k
      congr 1
      ring
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
  · exact Filter.Eventually.of_forall hterm
  · convert hpower.const_mul A using 1
    · funext k
      exact hratio k
    · simp

/-- The explicit constant in the `ρ`-summability stage of Theorem 4.1. -/
def derivativeRhoConstant (H Cmaj τ ρ : ℝ) : ℝ :=
  H * factorialDecaySeries (Cmaj ^ ρ * H) (τ * ρ)

/-- The series defining `derivativeRhoConstant` is summable under the paper's restriction
`τ ρ < 1`. -/
theorem derivativeRhoConstant_series_summable
    {H Cmaj τ ρ : ℝ} (hH : 0 < H) (hCmaj : 0 < Cmaj) (hτρ : τ * ρ < 1) :
    Summable (fun k : ℕ =>
      (Cmaj ^ ρ * H) ^ k * (k.factorial : ℝ) ^ (τ * ρ - 1)) := by
  apply summable_factorialDecaySeries
  · exact mul_pos (Real.rpow_pos_of_pos hCmaj ρ) hH
  · exact hτρ

/-- Paper Theorem 4.1, in the interface exposed by its preceding `ρ`-summability estimate.

`rhoBound` is exactly Equation (4.17) of the paper after setting
`x_u = κ^(|u|/p) 𝒟_{m,u}`.  The theorem proves the final passage from that estimate to every
`p > 2/3`, uniformly in the Euler level `m`. -/
theorem summable_normalized_mixedDeriv_fixed
    {ι Step : Type*} [Fintype ι] [DecidableEq ι]
    (derivativeEnvelope : Step → Finset ι → ℝ)
    (κ p ρ rhoBound : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ) (hρp : ρ < p)
    (henvelope : ∀ m u, 0 ≤ derivativeEnvelope m u)
    (hRhoBound : ∀ m,
      ∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι => u.Nonempty),
        (κ ^ ((u.card : ℝ) / p) * derivativeEnvelope m u) ^ ρ ≤ rhoBound) :
    ∀ m, weightedDerivativeSum κ p (derivativeEnvelope m) ≤
      rhoBound ^ (p / ρ) := by
  intro m
  let subsets := Finset.univ.powerset.filter (fun u : Finset ι => u.Nonempty)
  let scaled : Finset ι → ℝ := fun u =>
    κ ^ ((u.card : ℝ) / p) * derivativeEnvelope m u
  have hp : 0 < p := hρ.trans hρp
  have hscaled : ∀ u ∈ subsets, 0 ≤ scaled u := by
    intro u hu
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hκ) _) (henvelope m u)
  have hlift := sum_rpow_lift subsets scaled hρ hρp hscaled (hRhoBound m)
  change (∑ u ∈ subsets, κ ^ u.card * derivativeEnvelope m u ^ p) ≤ _
  calc
    (∑ u ∈ subsets, κ ^ u.card * derivativeEnvelope m u ^ p) =
        ∑ u ∈ subsets, scaled u ^ p := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hκ) _) (henvelope m u),
        ← Real.rpow_mul (le_of_lt hκ)]
      have hnat : κ ^ u.card = κ ^ (u.card : ℝ) :=
        (Real.rpow_natCast κ u.card).symm
      rw [hnat]
      congr 2
      field_simp
    _ ≤ rhoBound ^ (p / ρ) := hlift

/-- Dimension-varying form of the final exponent lift.  The coordinate type may depend on the
Euler level, as it does for the Brownian-bridge index type `Index J d_w`. -/
theorem summable_normalized_mixedDeriv
    {Step : Type*} (ι : Step → Type*)
    [∀ m, Fintype (ι m)] [∀ m, DecidableEq (ι m)]
    (derivativeEnvelope : ∀ m, Finset (ι m) → ℝ)
    (κ p ρ rhoBound : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ) (hρp : ρ < p)
    (henvelope : ∀ m u, 0 ≤ derivativeEnvelope m u)
    (hRhoBound : ∀ m,
      ∑ u ∈ Finset.univ.powerset.filter
          (fun u : Finset (ι m) => u.Nonempty),
        (κ ^ ((u.card : ℝ) / p) * derivativeEnvelope m u) ^ ρ ≤ rhoBound) :
    ∀ m, weightedDerivativeSum κ p (derivativeEnvelope m) ≤
      rhoBound ^ (p / ρ) := by
  intro m
  exact summable_normalized_mixedDeriv_fixed
    (fun _ : Unit => derivativeEnvelope m) κ p ρ rhoBound
    hκ hρ hρp (fun _ u => henvelope m u) (fun _ => hRhoBound m) ()

/-- Assembly form of paper Theorem 4.1 using the particular intermediate exponent selected in
the paper.  The remaining hypothesis is precisely the uniform `ρ`-estimate obtained by combining
Proposition 4.3 with Lemmas 4.4 and 4.5. -/
theorem theorem4_1_from_rho_estimate
    {Step : Type*} (ι : Step → Type*)
    [∀ m, Fintype (ι m)] [∀ m, DecidableEq (ι m)]
    (derivativeEnvelope : ∀ m, Finset (ι m) → ℝ)
    (κ p τ rhoBound : ℝ) (hκ : 0 < κ) (hτone : 1 ≤ τ) (hτ : τ < 3 / 2)
    (hp : 2 / 3 < p) (henvelope : ∀ m u, 0 ≤ derivativeEnvelope m u)
    (hRhoBound : ∀ m,
      ∑ u ∈ Finset.univ.powerset.filter (fun u : Finset (ι m) => u.Nonempty),
        (κ ^ ((u.card : ℝ) / p) * derivativeEnvelope m u) ^
          intermediateExponent τ p ≤ rhoBound) :
    ∀ m, weightedDerivativeSum κ p (derivativeEnvelope m) ≤
      rhoBound ^ (p / intermediateExponent τ p) := by
  have hspec := intermediateExponent_spec hτone hτ hp
  exact summable_normalized_mixedDeriv ι derivativeEnvelope κ p
    (intermediateExponent τ p) rhoBound hκ hspec.2.2.2 hspec.2.1
    henvelope hRhoBound

end

end TimeDependentLattice.Regularity
