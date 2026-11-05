/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.Constants
import TimeDependentLattice.Euler.Growth

/-!
# Euler bias from the stochastic remainder interfaces

The recurrence hypotheses below are the interface to the standard stochastic-analysis steps in
Appendix E.  This file proves the remaining discrete Gronwall and payoff-transfer deductions.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators

private theorem mul_natCast_div_self
    {a : ℝ} {m : ℕ} (hm : 0 < m) :
    (a / (m : ℝ)) * (m : ℝ) = a := by
  field_simp

/-- Theorem 3.7: the half-order strong estimate from its scalar error recurrence. -/
theorem euler_strong_half_of_recurrence
    {m : ℕ} (hm : 0 < m)
    {T K0 L Ht initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (error : ℕ → ℝ) (herror : ∀ j, 0 ≤ error j)
    (hrec : ∀ j ≤ m,
      error j ≤
        (2 / 3 : ℝ) * T * Real.sqrt T *
            (L * incrementConstant T K0 L initialNorm sigmaHS +
              Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) *
            (m : ℝ) ^ (-(1 / 2 : ℝ)) +
          (L * T / (m : ℝ)) * ∑ i ∈ Finset.range j, error i) :
    error m ≤
      strongHalfConstant T K0 L Ht initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let A :=
    (2 / 3 : ℝ) * T * Real.sqrt T *
      (L * incrementConstant T K0 L initialNorm sigmaHS +
        Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) *
      (m : ℝ) ^ (-(1 / 2 : ℝ))
  let c := L * T / (m : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [stateMomentConstant_nonneg (L := L) hT hK0 hinitial hsigma,
      incrementConstant_nonneg hT hK0 hL hinitial hsigma]
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hgronwall := TimeDependentLattice.Euler.discrete_sum_gronwall
    hA hc herror (n := m) (by simpa [A, c] using hrec)
  calc
    error m ≤ A * Real.exp (c * m) := hgronwall
    _ = strongHalfConstant T K0 L Ht initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hcMul : c * (m : ℝ) = L * T := by
        dsimp [c]
        exact mul_natCast_div_self hm
      rw [hcMul]
      unfold A strongHalfConstant
      ring

/-- Theorem 3.7: the half-order payoff bias. -/
theorem euler_bias_half_of_recurrence
    {m : ℕ} (hm : 0 < m)
    {G0 G1 beta T K0 L Ht initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (error : ℕ → ℝ) (herror : ∀ j, 0 ≤ error j)
    (hrec : ∀ j ≤ m,
      error j ≤
        (2 / 3 : ℝ) * T * Real.sqrt T *
            (L * incrementConstant T K0 L initialNorm sigmaHS +
              Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) *
            (m : ℝ) ^ (-(1 / 2 : ℝ)) +
          (L * T / (m : ℝ)) * ∑ i ∈ Finset.range j, error i)
    (approximateIntegral exactIntegral : ℝ)
    (hpayoff : |approximateIntegral - exactIntegral| ≤
      payoffDifferenceConstant G0 G1 beta T K0 L initialNorm sigmaHS * error m) :
    |approximateIntegral - exactIntegral| ≤
      biasHalfConstant G0 G1 beta T K0 L Ht initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  refine hpayoff.trans ?_
  have hstrong := euler_strong_half_of_recurrence hm hT hK0 hL hHt
    hinitial hsigma error herror hrec
  unfold biasHalfConstant
  have h := mul_le_mul_of_nonneg_left hstrong
    (payoffDifferenceConstant_nonneg (beta := beta) (T := T) (K0 := K0)
      (L := L) (initialNorm := initialNorm) (sigmaHS := sigmaHS) hG0 hG1)
  simpa [mul_assoc] using h

/-- Theorem 3.8: the first-order strong estimate from the drift and martingale remainder
interface. -/
theorem euler_strong_one_of_recurrence
    {m : ℕ} (hm : 0 < m)
    {T K0 L B2 Lt initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hLt : 0 ≤ Lt) (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (error : ℕ → ℝ) (herror : ∀ j, 0 ≤ error j)
    (hrec : ∀ j ≤ m,
      error j ≤
        (T * driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS +
            2 * L * sigmaHS * Real.sqrt (T / 3)) *
            (T / (m : ℝ)) +
          (L * T / (m : ℝ)) * ∑ i ∈ Finset.range j, error i) :
    error m ≤
      T * strongOneConstant T K0 L B2 Lt initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 : ℝ)) := by
  let A :=
    (T * driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS +
      2 * L * sigmaHS * Real.sqrt (T / 3)) * (T / (m : ℝ))
  let c := L * T / (m : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [driftRemainderConstant_nonneg hT hK0 hL hB2 hLt hinitial hsigma]
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hgronwall := TimeDependentLattice.Euler.discrete_sum_gronwall
    hA hc herror (n := m) (by simpa [A, c] using hrec)
  calc
    error m ≤ A * Real.exp (c * m) := hgronwall
    _ = T * strongOneConstant T K0 L B2 Lt initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 : ℝ)) := by
      have hcMul : c * (m : ℝ) = L * T := by
        dsimp [c]
        exact mul_natCast_div_self hm
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      rw [hcMul, Real.rpow_neg_one]
      unfold A strongOneConstant
      field_simp

/-- Theorem 3.8: the first-order payoff bias. -/
theorem euler_bias_order_one_of_recurrence
    {m : ℕ} (hm : 0 < m)
    {G0 G1 beta T K0 L B2 Lt initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hLt : 0 ≤ Lt) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (error : ℕ → ℝ) (herror : ∀ j, 0 ≤ error j)
    (hrec : ∀ j ≤ m,
      error j ≤
        (T * driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS +
            2 * L * sigmaHS * Real.sqrt (T / 3)) *
            (T / (m : ℝ)) +
          (L * T / (m : ℝ)) * ∑ i ∈ Finset.range j, error i)
    (approximateIntegral exactIntegral : ℝ)
    (hpayoff : |approximateIntegral - exactIntegral| ≤
      payoffDifferenceConstant G0 G1 beta T K0 L initialNorm sigmaHS * error m) :
    |approximateIntegral - exactIntegral| ≤
      biasOneConstant G0 G1 beta T K0 L B2 Lt initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 : ℝ)) := by
  refine hpayoff.trans ?_
  have hstrong := euler_strong_one_of_recurrence hm hT hK0 hL hB2 hLt
    hinitial hsigma error herror hrec
  unfold biasOneConstant
  have h := mul_le_mul_of_nonneg_left hstrong
    (payoffDifferenceConstant_nonneg (beta := beta) (T := T) (K0 := K0)
      (L := L) (initialNorm := initialNorm) (sigmaHS := sigmaHS) hG0 hG1)
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

end

end TimeDependentLattice.Bias
