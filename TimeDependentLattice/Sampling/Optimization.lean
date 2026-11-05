/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.Transfer

/-!
# Optimization of the subset weights

This file verifies the auxiliary-weight calculation in paper Proposition 5.3, including the
zero-weight convention.  Both finite sums produced by the random worst-case-error argument become
the same fractional subset sum.
-/

namespace TimeDependentLattice.Sampling

open scoped BigOperators

noncomputable section

/-- Division with the paper's convention `0 / 0 = 0`. -/
def zeroDiv (a b : ℝ) : ℝ :=
  if b = 0 then 0 else a / b

/-- The auxiliary subset weight from Equation (5.6). -/
def auxiliarySubsetWeight {ι : Type*}
    (ρ lam : ℝ) (B : Finset ι → ℝ) (u : Finset ι) : ℝ :=
  (B u ^ 2 / ρ ^ u.card) ^ (1 / (1 + lam))

/-- The common balanced summand in Proposition 5.3. -/
def balancedSubsetTerm {ι : Type*}
    (ρ lam : ℝ) (B : Finset ι → ℝ) (u : Finset ι) : ℝ :=
  ρ ^ ((u.card : ℝ) / (1 + lam)) *
    B u ^ latticeDerivativeExponent lam

private theorem balance_left_positive
    {b r lam : ℝ} (hb : 0 < b) (hr : 0 < r) (hlam : 0 < lam) :
    b ^ 2 / ((b ^ 2 / r) ^ (1 / (1 + lam))) =
      r ^ (1 / (1 + lam)) * b ^ (2 * lam / (1 + lam)) := by
  have hden : 0 < 1 + lam := by linarith
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hratio : 0 < b ^ 2 / r := div_pos hb2 hr
  have hgamma : 0 < (b ^ 2 / r) ^ (1 / (1 + lam)) :=
    Real.rpow_pos_of_pos hratio _
  have hleft : 0 < b ^ 2 / ((b ^ 2 / r) ^ (1 / (1 + lam))) :=
    div_pos hb2 hgamma
  have hright : 0 < r ^ (1 / (1 + lam)) * b ^ (2 * lam / (1 + lam)) :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hb _)
  apply Real.log_injOn_pos hleft hright
  rw [Real.log_div hb2.ne' hgamma.ne', Real.log_rpow hratio,
    Real.log_div hb2.ne' hr.ne', Real.log_pow,
    Real.log_mul (Real.rpow_pos_of_pos hr _).ne'
      (Real.rpow_pos_of_pos hb _).ne',
    Real.log_rpow hr, Real.log_rpow hb]
  field_simp
  ring

private theorem balance_right_positive
    {b r lam : ℝ} (hb : 0 < b) (hr : 0 < r) (hlam : 0 < lam) :
    ((b ^ 2 / r) ^ (1 / (1 + lam))) ^ lam * r =
      r ^ (1 / (1 + lam)) * b ^ (2 * lam / (1 + lam)) := by
  have hden : 0 < 1 + lam := by linarith
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hratio : 0 < b ^ 2 / r := div_pos hb2 hr
  have hgamma : 0 < (b ^ 2 / r) ^ (1 / (1 + lam)) :=
    Real.rpow_pos_of_pos hratio _
  have hleft : 0 < ((b ^ 2 / r) ^ (1 / (1 + lam))) ^ lam * r :=
    mul_pos (Real.rpow_pos_of_pos hgamma _) hr
  have hright : 0 < r ^ (1 / (1 + lam)) * b ^ (2 * lam / (1 + lam)) :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hb _)
  apply Real.log_injOn_pos hleft hright
  rw [Real.log_mul (Real.rpow_pos_of_pos hgamma _).ne' hr.ne',
    Real.log_rpow hgamma, Real.log_rpow hratio,
    Real.log_div hb2.ne' hr.ne', Real.log_pow,
    Real.log_mul (Real.rpow_pos_of_pos hr _).ne'
      (Real.rpow_pos_of_pos hb _).ne',
    Real.log_rpow hr, Real.log_rpow hb]
  field_simp
  ring

private theorem rpow_nat_then_fraction
    {ρ lam : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    (ρ ^ n : ℝ) ^ (1 / (1 + lam)) =
      ρ ^ ((n : ℝ) / (1 + lam)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  congr 1
  ring

theorem zeroDiv_auxiliarySubsetWeight_eq_balancedSubsetTerm
    {ι : Type*} {ρ lam : ℝ} {B : Finset ι → ℝ}
    (hρ : 0 < ρ) (hlam : 0 < lam) (hB : ∀ u, 0 ≤ B u) (u : Finset ι) :
    zeroDiv (B u ^ 2) (auxiliarySubsetWeight ρ lam B u) =
      balancedSubsetTerm ρ lam B u := by
  have hp : 0 < latticeDerivativeExponent lam := by
    unfold latticeDerivativeExponent
    positivity
  by_cases hzero : B u = 0
  · have hauxExp : 0 < 1 / (1 + lam) := by positivity
    simp [zeroDiv, auxiliarySubsetWeight, balancedSubsetTerm, hzero,
      Real.zero_rpow hp.ne']
  · have hb : 0 < B u := lt_of_le_of_ne (hB u) (Ne.symm hzero)
    have hr : 0 < ρ ^ u.card := pow_pos hρ _
    have hgamma : auxiliarySubsetWeight ρ lam B u ≠ 0 := by
      unfold auxiliarySubsetWeight
      exact (Real.rpow_pos_of_pos (div_pos (sq_pos_of_pos hb) hr) _).ne'
    unfold zeroDiv
    rw [if_neg hgamma]
    unfold auxiliarySubsetWeight balancedSubsetTerm latticeDerivativeExponent
    rw [balance_left_positive hb hr hlam,
      rpow_nat_then_fraction hρ]

theorem auxiliarySubsetWeight_rpow_eq_balancedSubsetTerm
    {ι : Type*} {ρ lam : ℝ} {B : Finset ι → ℝ}
    (hρ : 0 < ρ) (hlam : 0 < lam) (hB : ∀ u, 0 ≤ B u) (u : Finset ι) :
    auxiliarySubsetWeight ρ lam B u ^ lam * ρ ^ u.card =
      balancedSubsetTerm ρ lam B u := by
  have hp : 0 < latticeDerivativeExponent lam := by
    unfold latticeDerivativeExponent
    positivity
  by_cases hzero : B u = 0
  · have hauxExp : 0 < 1 / (1 + lam) := by positivity
    simp only [auxiliarySubsetWeight, balancedSubsetTerm, hzero,
      zero_pow (by norm_num : 2 ≠ 0), zero_div]
    rw [Real.zero_rpow hauxExp.ne', Real.zero_rpow hlam.ne',
      Real.zero_rpow hp.ne']
    simp
  · have hb : 0 < B u := lt_of_le_of_ne (hB u) (Ne.symm hzero)
    have hr : 0 < ρ ^ u.card := pow_pos hρ _
    unfold auxiliarySubsetWeight balancedSubsetTerm latticeDerivativeExponent
    rw [balance_right_positive hb hr hlam,
      rpow_nat_then_fraction hρ]

/-- The Sobolev-norm sum for the optimized weights equals the fractional subset sum. -/
theorem sum_zeroDiv_auxiliarySubsetWeight_eq_latticeFractionalSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ lam : ℝ} {B : Finset ι → ℝ}
    (hρ : 0 < ρ) (hlam : 0 < lam) (hB : ∀ u, 0 ≤ B u) :
    (∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
      zeroDiv (B u ^ 2) (auxiliarySubsetWeight ρ lam B u)) =
      latticeFractionalSum ρ lam B := by
  unfold latticeFractionalSum
  apply Finset.sum_congr rfl
  intro u hu
  exact zeroDiv_auxiliarySubsetWeight_eq_balancedSubsetTerm hρ hlam hB u

/-- The random-wce weight sum for the optimized weights is the same fractional subset sum. -/
theorem sum_auxiliarySubsetWeight_rpow_eq_latticeFractionalSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ lam : ℝ} {B : Finset ι → ℝ}
    (hρ : 0 < ρ) (hlam : 0 < lam) (hB : ∀ u, 0 ≤ B u) :
    (∑ u ∈ Finset.univ.powerset.filter (fun u : Finset ι ↦ u.Nonempty),
      auxiliarySubsetWeight ρ lam B u ^ lam * ρ ^ u.card) =
      latticeFractionalSum ρ lam B := by
  unfold latticeFractionalSum
  apply Finset.sum_congr rfl
  intro u hu
  exact auxiliarySubsetWeight_rpow_eq_balancedSubsetTerm hρ hlam hB u

end

end TimeDependentLattice.Sampling
