/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import TimeDependentLattice.Trees.CoefficientBound
import TimeDependentLattice.Trees.Value

/-!
# Analytic bounds for timed tree values

This file formalizes the analytic half of paper Lemma B.8.  It starts with the exact product
of direction norms at one vertex, the bridge needed to apply the operator-norm assumptions in
Assumption 2.1 to the recursive tree values.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open scoped BigOperators ContDiff
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Euler

/-- The direction family at one vertex splits into its direct bridge inputs and its child-tree
values. -/
theorem prod_norm_vertexDirections
    {J stateDim noiseDim : ℕ}
    (direct : Finset (Index J noiseDim))
    (directValue : Index J noiseDim → State stateDim)
    (childValues : List (State stateDim)) :
    (∏ i, ‖vertexDirections direct directValue childValues i‖) =
      (∏ j ∈ direct, ‖directValue j‖) *
        (childValues.map norm).prod := by
  rw [Fin.prod_univ_add]
  congr 1
  · calc
      (∏ i : Fin direct.card,
          ‖vertexDirections direct directValue childValues (Fin.castAdd _ i)‖) =
          ∏ i : Fin direct.card, ‖directValue (direct.equivFin.symm i).1‖ := by
            apply Finset.prod_congr rfl
            intro i _
            simp [vertexDirections]
      _ = ∏ j : ↥direct, ‖directValue j.1‖ := by
        exact Fintype.prod_equiv direct.equivFin.symm
          (fun i : Fin direct.card => ‖directValue (direct.equivFin.symm i).1‖)
          (fun j : ↥direct => ‖directValue j.1‖) (fun _ => rfl)
      _ = ∏ j ∈ direct, ‖directValue j‖ := by
        exact Finset.prod_attach direct (fun j => ‖directValue j‖)
  · calc
      (∏ i : Fin childValues.length,
          ‖vertexDirections direct directValue childValues (Fin.natAdd _ i)‖) =
          ∏ i : Fin childValues.length, ‖childValues.get i‖ := by
            apply Finset.prod_congr rfl
            intro i _
            simp [vertexDirections]
      _ = (childValues.map norm).prod := by
        simpa [List.get_eq_getElem] using
          (Fin.prod_univ_fun_getElem childValues norm)

/-- A uniform one-step operator bound gives a power bound for the discrete propagator. -/
theorem norm_propagator_le_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (jacobian : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 1 ≤ C)
    (hjacobian : ∀ i, ‖jacobian i‖ ≤ C) :
    ∀ i r, ‖propagator jacobian i r‖ ≤ C ^ i := by
  intro i
  induction i with
  | zero =>
      intro r
      have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ (1 : ℝ) :=
        ContinuousLinearMap.norm_id_le
      simpa using hid
  | succ i ih =>
      intro r
      by_cases hr : r < i
      · rw [propagator_succ_of_lt jacobian hr]
        calc
          ‖(jacobian i).comp (propagator jacobian i r)‖ ≤
              ‖jacobian i‖ * ‖propagator jacobian i r‖ :=
            (jacobian i).opNorm_comp_le _
          _ ≤ C * C ^ i := mul_le_mul (hjacobian i) (ih r)
            (norm_nonneg _) (zero_le_one.trans hC)
          _ = C ^ (i + 1) := by rw [pow_succ]; ring
      · rw [propagator]
        simp only [hr, if_false]
        have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ (1 : ℝ) :=
          ContinuousLinearMap.norm_id_le
        exact hid.trans (one_le_pow₀ hC)

/-- Prefix-local version of `norm_propagator_le_pow`.  This is the form needed on the finite
Euler grid, where the Jacobian estimate is assumed only before the terminal time. -/
theorem norm_propagator_le_pow_of_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (jacobian : ℕ → E →L[ℝ] E) (C : ℝ) (hC : 1 ≤ C) :
    ∀ i, (∀ k, k < i → ‖jacobian k‖ ≤ C) →
      ∀ r, ‖propagator jacobian i r‖ ≤ C ^ i := by
  intro i
  induction i with
  | zero =>
      intro _ r
      have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ (1 : ℝ) :=
        ContinuousLinearMap.norm_id_le
      simpa using hid
  | succ i ih =>
      intro hjacobian r
      by_cases hr : r < i
      · rw [propagator_succ_of_lt jacobian hr]
        have hprefix : ∀ k, k < i → ‖jacobian k‖ ≤ C := by
          intro k hk
          exact hjacobian k (hk.trans_le i.le_succ)
        calc
          ‖(jacobian i).comp (propagator jacobian i r)‖ ≤
              ‖jacobian i‖ * ‖propagator jacobian i r‖ :=
            (jacobian i).opNorm_comp_le _
          _ ≤ C * C ^ i := mul_le_mul (hjacobian i (Nat.lt_succ_self i))
            (ih hprefix r) (norm_nonneg _) (zero_le_one.trans hC)
          _ = C ^ (i + 1) := by rw [pow_succ]; ring
      · rw [propagator]
        simp only [hr, if_false]
        have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ (1 : ℝ) :=
          ContinuousLinearMap.norm_id_le
        exact hid.trans (one_le_pow₀ hC)

/-- The part of paper Assumption 2.1 used by the tree majorant.  The bounds are stated in the
same operator norm and with the same Gevrey factorial growth as in the paper. -/
structure GevreyBounds {stateDim : ℕ}
    (drift : Drift stateDim) (payoff : Payoff stateDim) (T : ℝ) where
  B₀ : ℝ
  B₁ : ℝ
  G₀ : ℝ
  G₁ : ℝ
  β : ℝ
  τ : ℝ
  B₀_pos : 0 < B₀
  B₁_pos : 0 < B₁
  G₀_pos : 0 < G₀
  G₁_pos : 0 < G₁
  β_pos : 0 < β
  τ_mem : τ ∈ Set.Ico (1 : ℝ) (3 / 2 : ℝ)
  drift_smooth : ∀ t, ContDiff ℝ ∞ (drift t)
  payoff_smooth : ContDiff ℝ ∞ payoff
  drift_derivative_norm : ∀ n, 1 ≤ n → ∀ t, 0 ≤ t → t ≤ T → ∀ x,
    ‖iteratedFDeriv ℝ n (drift t) x‖ ≤
      B₀ * B₁ ^ n * (n.factorial : ℝ) ^ τ
  payoff_derivative_norm : ∀ n, 1 ≤ n → ∀ x,
    ‖iteratedFDeriv ℝ n payoff x‖ ≤
      G₀ * G₁ ^ n * (n.factorial : ℝ) ^ τ * Real.exp (β * ‖x‖)

namespace GevreyBounds

/-- The first drift-derivative constant `\mathsf B_1` from Assumption 2.1. -/
def driftLipschitzConstant
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) : ℝ :=
  bounds.B₀ * bounds.B₁

theorem driftLipschitzConstant_pos
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    0 < bounds.driftLipschitzConstant := by
  exact mul_pos bounds.B₀_pos bounds.B₁_pos

/-- Assumption 2.1 implies the linear-growth estimate used in the Euler moment bounds.
The only additional datum is the stated bound of the drift at the origin. -/
theorem drift_norm_le_origin_add_lipschitz
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T)
    (horigin : ∀ t, 0 ≤ t → t ≤ T → ‖drift t 0‖ ≤ K₀)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (x : State stateDim) :
    ‖drift t x‖ ≤ K₀ + bounds.driftLipschitzConstant * ‖x‖ := by
  have hderiv : ∀ y : State stateDim,
      ‖fderiv ℝ (drift t) y‖ ≤ bounds.driftLipschitzConstant := by
    intro y
    rw [← norm_iteratedFDeriv_one]
    simpa [driftLipschitzConstant] using
      bounds.drift_derivative_norm 1 (by omega) t ht0 htT y
  have hlip : ‖drift t x - drift t 0‖ ≤
      bounds.driftLipschitzConstant * ‖x - 0‖ := by
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := Set.univ) (x := (0 : State stateDim)) (y := x)
      (fun y _ ↦ (bounds.drift_smooth t).differentiable (by simp) y)
      (fun y _ ↦ hderiv y) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  calc
    ‖drift t x‖ ≤ ‖drift t x - drift t 0‖ + ‖drift t 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (drift t x - drift t 0) (drift t 0)
    _ ≤ bounds.driftLipschitzConstant * ‖x - 0‖ + K₀ :=
      add_le_add hlip (horigin t ht0 htT)
    _ = K₀ + bounds.driftLipschitzConstant * ‖x‖ := by
      simp [add_comm]

/-- A single base dominating every model constant that occurs in the tree coefficient
estimate.  It is the paper's `K`, written with nested maxima. -/
def coefficientBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) : ℝ :=
  max 1 (max bounds.G₀ (max bounds.G₁
    (max (Real.exp (bounds.driftLipschitzConstant * T) * bounds.B₀)
      (max bounds.B₁ ((2 : ℝ) ^ bounds.τ)))))

theorem one_le_coefficientBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    1 ≤ bounds.coefficientBase :=
  le_max_left _ _

theorem G₀_le_coefficientBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    bounds.G₀ ≤ bounds.coefficientBase := by
  exact le_max_of_le_right (le_max_left _ _)

theorem G₁_le_coefficientBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    bounds.G₁ ≤ bounds.coefficientBase := by
  exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

theorem exp_mul_B₀_le_coefficientBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    Real.exp (bounds.driftLipschitzConstant * T) * bounds.B₀ ≤
      bounds.coefficientBase := by
  exact le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))

theorem B₁_le_coefficientBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    bounds.B₁ ≤ bounds.coefficientBase := by
  exact le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))

theorem two_rpow_τ_le_coefficientBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    (2 : ℝ) ^ bounds.τ ≤ bounds.coefficientBase := by
  exact le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))

private theorem drift_local_coefficient_le
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (n c : ℕ) :
    Real.exp (bounds.driftLipschitzConstant * T) *
        (bounds.B₀ * bounds.B₁ ^ (n + c) *
          ((n + c).factorial : ℝ) ^ bounds.τ) ≤
      bounds.coefficientBase ^ (1 + 2 * (n + c)) *
        (n.factorial : ℝ) ^ bounds.τ * (c.factorial : ℝ) ^ bounds.τ := by
  have hK : 0 ≤ bounds.coefficientBase :=
    (zero_le_one.trans bounds.one_le_coefficientBase)
  have hfactorial := factorial_add_rpow_le_split n c bounds.τ
    (zero_le_one.trans bounds.τ_mem.1)
  have hAB :
      (Real.exp (bounds.driftLipschitzConstant * T) * bounds.B₀) *
          bounds.B₁ ^ (n + c) ≤
        bounds.coefficientBase * bounds.coefficientBase ^ (n + c) :=
    mul_le_mul bounds.exp_mul_B₀_le_coefficientBase
      (pow_le_pow_left₀ bounds.B₁_pos.le bounds.B₁_le_coefficientBase _)
      (pow_nonneg bounds.B₁_pos.le _) hK
  have htwoPow :
      ((2 : ℝ) ^ bounds.τ) ^ (n + c) ≤
        bounds.coefficientBase ^ (n + c) :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
      bounds.two_rpow_τ_le_coefficientBase _
  calc
    Real.exp (bounds.driftLipschitzConstant * T) *
        (bounds.B₀ * bounds.B₁ ^ (n + c) *
          ((n + c).factorial : ℝ) ^ bounds.τ) =
      (Real.exp (bounds.driftLipschitzConstant * T) * bounds.B₀) *
        bounds.B₁ ^ (n + c) * ((n + c).factorial : ℝ) ^ bounds.τ := by ring
    _ ≤ bounds.coefficientBase * bounds.coefficientBase ^ (n + c) *
        (((2 : ℝ) ^ bounds.τ) ^ (n + c) *
          (n.factorial : ℝ) ^ bounds.τ * (c.factorial : ℝ) ^ bounds.τ) := by
      exact (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (by positivity) _)).trans
        (mul_le_mul_of_nonneg_left hfactorial
          (mul_nonneg hK (pow_nonneg hK _)))
    _ ≤ bounds.coefficientBase * bounds.coefficientBase ^ (n + c) *
        (bounds.coefficientBase ^ (n + c) *
          (n.factorial : ℝ) ^ bounds.τ * (c.factorial : ℝ) ^ bounds.τ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htwoPow
            (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg hK (pow_nonneg hK _))
    _ = _ := by
      rw [show 1 + 2 * (n + c) = 1 + (n + c) + (n + c) by omega,
        pow_add, pow_add]
      ring

private theorem payoff_local_coefficient_le
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (n c : ℕ) :
    bounds.G₀ * bounds.G₁ ^ (n + c) *
        ((n + c).factorial : ℝ) ^ bounds.τ ≤
      bounds.coefficientBase ^ (1 + 2 * (n + c)) *
        (n.factorial : ℝ) ^ bounds.τ * (c.factorial : ℝ) ^ bounds.τ := by
  have hK : 0 ≤ bounds.coefficientBase :=
    (zero_le_one.trans bounds.one_le_coefficientBase)
  have hfactorial := factorial_add_rpow_le_split n c bounds.τ
    (zero_le_one.trans bounds.τ_mem.1)
  have hAB : bounds.G₀ * bounds.G₁ ^ (n + c) ≤
      bounds.coefficientBase * bounds.coefficientBase ^ (n + c) :=
    mul_le_mul bounds.G₀_le_coefficientBase
      (pow_le_pow_left₀ bounds.G₁_pos.le bounds.G₁_le_coefficientBase _)
      (pow_nonneg bounds.G₁_pos.le _) hK
  have htwoPow :
      ((2 : ℝ) ^ bounds.τ) ^ (n + c) ≤
        bounds.coefficientBase ^ (n + c) :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
      bounds.two_rpow_τ_le_coefficientBase _
  calc
    bounds.G₀ * bounds.G₁ ^ (n + c) *
        ((n + c).factorial : ℝ) ^ bounds.τ ≤
      bounds.coefficientBase * bounds.coefficientBase ^ (n + c) *
        (((2 : ℝ) ^ bounds.τ) ^ (n + c) *
          (n.factorial : ℝ) ^ bounds.τ * (c.factorial : ℝ) ^ bounds.τ) := by
      exact (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (by positivity) _)).trans
        (mul_le_mul_of_nonneg_left hfactorial
          (mul_nonneg hK (pow_nonneg hK _)))
    _ ≤ bounds.coefficientBase * bounds.coefficientBase ^ (n + c) *
        (bounds.coefficientBase ^ (n + c) *
          (n.factorial : ℝ) ^ bounds.τ * (c.factorial : ℝ) ^ bounds.τ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htwoPow
            (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg hK (pow_nonneg hK _))
    _ = _ := by
      rw [show 1 + 2 * (n + c) = 1 + (n + c) + (n + c) by omega,
        pow_add, pow_add]
      ring

/-- The Euler Jacobian satisfies `\|J_i\| ≤ 1 + h \mathsf B_1` at every grid time. -/
theorem norm_stepJacobian_le
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) {i : ℕ} (hi : i ≤ numSteps J) :
    ‖stepJacobian drift diffusion T x₀ z i‖ ≤
      1 + stepSize T J * bounds.driftLipschitzConstant := by
  have hderiv :
      ‖fderiv ℝ (drift (gridTime T J i))
          (eulerDriftInput drift diffusion T x₀ i z)‖ ≤
        bounds.driftLipschitzConstant := by
    rw [← norm_iteratedFDeriv_one]
    simpa [driftLipschitzConstant] using
      bounds.drift_derivative_norm 1 (by omega) (gridTime T J i)
        (gridTime_nonneg hT J i) (gridTime_le_terminal hT J hi)
        (eulerDriftInput drift diffusion T x₀ i z)
  have hh : 0 ≤ stepSize T J := stepSize_nonneg hT J
  unfold stepJacobian
  calc
    ‖ContinuousLinearMap.id ℝ (State stateDim) +
        stepSize T J • fderiv ℝ (drift (gridTime T J i))
          (eulerDriftInput drift diffusion T x₀ i z)‖ ≤
      ‖ContinuousLinearMap.id ℝ (State stateDim)‖ +
        ‖stepSize T J • fderiv ℝ (drift (gridTime T J i))
          (eulerDriftInput drift diffusion T x₀ i z)‖ := norm_add_le _ _
    _ ≤ 1 + stepSize T J * bounds.driftLipschitzConstant := by
      gcongr
      · exact ContinuousLinearMap.norm_id_le
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left hderiv hh

/-- Equation (4.8): every Euler propagator before the terminal grid time is bounded by
`exp (\mathsf B_1 T)`. -/
theorem norm_stepPropagator_le_exp
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) {i : ℕ} (hi : i ≤ numSteps J) (r : ℕ) :
    ‖propagator (stepJacobian drift diffusion T x₀ z) i r‖ ≤
      Real.exp (bounds.driftLipschitzConstant * T) := by
  let L := bounds.driftLipschitzConstant
  let h := stepSize T J
  let C := 1 + h * L
  have hL : 0 ≤ L := bounds.driftLipschitzConstant_pos.le
  have hh : 0 ≤ h := stepSize_nonneg hT J
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hh hL]
  have hjacobian : ∀ k, k < i →
      ‖stepJacobian drift diffusion T x₀ z k‖ ≤ C := by
    intro k hk
    dsimp [C, h, L]
    exact bounds.norm_stepJacobian_le hT diffusion x₀ z (hk.le.trans hi)
  have hprop :
      ‖propagator (stepJacobian drift diffusion T x₀ z) i r‖ ≤ C ^ i :=
    norm_propagator_le_pow_of_prefix _ C hC i hjacobian r
  have hbase : C ≤ Real.exp (h * L) := by
    dsimp [C]
    simpa [add_comm] using Real.add_one_le_exp (h * L)
  have hterminal : (numSteps J : ℝ) * h = T := by
    simpa [gridTime, h] using gridTime_terminal T J
  calc
    ‖propagator (stepJacobian drift diffusion T x₀ z) i r‖ ≤ C ^ i := hprop
    _ ≤ C ^ numSteps J := pow_le_pow_right₀ hC hi
    _ ≤ (Real.exp (h * L)) ^ numSteps J :=
      pow_le_pow_left₀ (zero_le_one.trans hC) hbase _
    _ = Real.exp ((numSteps J : ℝ) * (h * L)) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (L * T) := by
      congr 1
      rw [← hterminal]
      ring
    _ = Real.exp (bounds.driftLipschitzConstant * T) := by rfl

/-- One drift vertex satisfies exactly the local recursive estimate used in (B.5).  The direct
bridge directions and recursively computed child values remain factored, so this lemma can be
iterated along a timed tree without losing the paper's coefficient structure. -/
theorem norm_driftVertex_le
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) (parentTime time : ℕ)
    (hparent : parentTime ≤ numSteps J) (htime : time < parentTime)
    (direct : Finset (Index J noiseDim)) (childValues : List (State stateDim))
    (hn : 1 ≤ direct.card + childValues.length) :
    ‖propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J •
          iteratedFDeriv ℝ (direct.card + childValues.length)
            (drift (gridTime T J time))
            (stateNat drift diffusion T x₀ z time)
            (vertexDirections direct
              (fun j ↦ diffusionCoefficient diffusion T j (gridTime T J time))
              childValues))‖ ≤
      stepSize T J * Real.exp (bounds.driftLipschitzConstant * T) *
        (bounds.B₀ * bounds.B₁ ^ (direct.card + childValues.length) *
          ((direct.card + childValues.length).factorial : ℝ) ^ bounds.τ) *
        (∏ j ∈ direct,
          ‖diffusionCoefficient diffusion T j (gridTime T J time)‖) *
        (childValues.map norm).prod := by
  let n := direct.card + childValues.length
  let directions := vertexDirections direct
    (fun j ↦ diffusionCoefficient diffusion T j (gridTime T J time)) childValues
  let derivativeValue := iteratedFDeriv ℝ n
    (drift (gridTime T J time)) (stateNat drift diffusion T x₀ z time) directions
  have htimeGrid : time ≤ numSteps J := htime.le.trans hparent
  have hprop := bounds.norm_stepPropagator_le_exp hT diffusion x₀ z hparent time
  have hderiv : ‖derivativeValue‖ ≤
      (bounds.B₀ * bounds.B₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        ∏ i, ‖directions i‖ := by
    exact ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
      (bounds.drift_derivative_norm n hn (gridTime T J time)
        (gridTime_nonneg hT J time) (gridTime_le_terminal hT J htimeGrid)
        (stateNat drift diffusion T x₀ z time)) (fun _ ↦ le_rfl)
  have hh : 0 ≤ stepSize T J := stepSize_nonneg hT J
  have hexp : 0 ≤ Real.exp (bounds.driftLipschitzConstant * T) :=
    (Real.exp_pos _).le
  have hcoefficient : 0 ≤
      bounds.B₀ * bounds.B₁ ^ n * (n.factorial : ℝ) ^ bounds.τ := by
    exact mul_nonneg
      (mul_nonneg bounds.B₀_pos.le (pow_nonneg bounds.B₁_pos.le _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  change ‖propagator (stepJacobian drift diffusion T x₀ z) parentTime time
      (stepSize T J • derivativeValue)‖ ≤ _
  calc
    ‖propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J • derivativeValue)‖ ≤
      ‖propagator (stepJacobian drift diffusion T x₀ z) parentTime time‖ *
        ‖stepSize T J • derivativeValue‖ :=
      (propagator (stepJacobian drift diffusion T x₀ z) parentTime time).le_opNorm _
    _ ≤ Real.exp (bounds.driftLipschitzConstant * T) *
        ‖stepSize T J • derivativeValue‖ := by
      gcongr
    _ = Real.exp (bounds.driftLipschitzConstant * T) *
        (stepSize T J * ‖derivativeValue‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ Real.exp (bounds.driftLipschitzConstant * T) *
        (stepSize T J *
          ((bounds.B₀ * bounds.B₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
            ∏ i, ‖directions i‖)) := by
      gcongr
    _ = stepSize T J * Real.exp (bounds.driftLipschitzConstant * T) *
        (bounds.B₀ * bounds.B₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        (∏ j ∈ direct,
          ‖diffusionCoefficient diffusion T j (gridTime T J time)‖) *
        (childValues.map norm).prod := by
      rw [prod_norm_vertexDirections]
      ring

mutual
  /-- The recursive right-hand side obtained by applying the local drift-vertex estimate at
  every vertex of a timed drift tree. -/
  def driftTreeMajorant
      {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
      {T : ℝ} (bounds : GevreyBounds drift payoff T)
      (diffusion : Diffusion stateDim noiseDim) :
      DriftTreeData J noiseDim → DriftTimeData → ℝ
    | .node direct children, .node time assignments =>
        let n := direct.card + children.length
        stepSize T J * Real.exp (bounds.driftLipschitzConstant * T) *
          (bounds.B₀ * bounds.B₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
          (∏ j ∈ direct,
            ‖diffusionCoefficient diffusion T j (gridTime T J time)‖) *
          (driftTreeMajorants bounds diffusion children assignments).prod

  /-- Majorants for an aligned forest and its list of time assignments. -/
  def driftTreeMajorants
      {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
      {T : ℝ} (bounds : GevreyBounds drift payoff T)
      (diffusion : Diffusion stateDim noiseDim) :
      List (DriftTreeData J noiseDim) → List DriftTimeData → List ℝ
    | tree :: trees, assignment :: assignments =>
        driftTreeMajorant bounds diffusion tree assignment ::
          driftTreeMajorants bounds diffusion trees assignments
    | _, _ => []
end

/-- Recursively substituting the local estimate proves the drift-subtree part of the
single-coefficient bound (B.5). -/
theorem norm_driftTreeValue_le_majorant
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) (tree : DriftTreeData J noiseDim)
    (assignment : DriftTimeData) (parentTime : ℕ)
    (htree : tree.Valid) (hassignment : assignment.Valid parentTime tree)
    (hparent : parentTime ≤ numSteps J) :
    ‖driftTreeValue drift diffusion T x₀ z parentTime tree assignment‖ ≤
      driftTreeMajorant bounds diffusion tree assignment := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ ∀ assignment parentTime,
      tree.Valid → assignment.Valid parentTime tree → parentTime ≤ numSteps J →
        ‖driftTreeValue drift diffusion T x₀ z parentTime tree assignment‖ ≤
          driftTreeMajorant bounds diffusion tree assignment)
    (motive_2 := fun trees ↦ ∀ assignments parentTime,
      (∀ child ∈ trees, child.Valid) →
      DriftTimeData.ValidChildren parentTime trees assignments →
      parentTime ≤ numSteps J →
        ((driftTreeValues drift diffusion T x₀ z parentTime trees assignments).map norm).prod ≤
          (driftTreeMajorants bounds diffusion trees assignments).prod)
    (fun direct children hchildren assignment parentTime htree hassignment hparent ↦ by
      cases assignment with
      | node time assignments =>
          simp only [DriftTimeData.Valid] at hassignment
          simp only [DriftTreeData.Valid] at htree
          let childValues :=
            driftTreeValues drift diffusion T x₀ z time children assignments
          have hlength : childValues.length = children.length :=
            driftTreeValues_length_eq_of_validChildren drift diffusion T x₀ z time
              children assignments hassignment.2
          have hn : 1 ≤ direct.card + childValues.length := by
            rw [hlength]
            rcases htree.1 with hsingleton | hhigher
            · omega
            · omega
          have hlocal := bounds.norm_driftVertex_le hT diffusion x₀ z parentTime time
            hparent hassignment.1 direct childValues hn
          have hforest := hchildren assignments time
            htree.2.2.2.2 hassignment.2 (hassignment.1.le.trans hparent)
          have hprefactor : 0 ≤
              stepSize T J * Real.exp (bounds.driftLipschitzConstant * T) *
                (bounds.B₀ * bounds.B₁ ^ (direct.card + childValues.length) *
                  ((direct.card + childValues.length).factorial : ℝ) ^ bounds.τ) *
                (∏ j ∈ direct,
                  ‖diffusionCoefficient diffusion T j (gridTime T J time)‖) := by
            apply mul_nonneg
            · apply mul_nonneg
              · exact mul_nonneg (stepSize_nonneg hT J) (Real.exp_pos _).le
              · exact mul_nonneg
                  (mul_nonneg bounds.B₀_pos.le (pow_nonneg bounds.B₁_pos.le _))
                  (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            · exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
          calc
            ‖driftTreeValue drift diffusion T x₀ z parentTime
                (.node direct children) (.node time assignments)‖ ≤
              stepSize T J * Real.exp (bounds.driftLipschitzConstant * T) *
                (bounds.B₀ * bounds.B₁ ^ (direct.card + childValues.length) *
                  ((direct.card + childValues.length).factorial : ℝ) ^ bounds.τ) *
                (∏ j ∈ direct,
                  ‖diffusionCoefficient diffusion T j (gridTime T J time)‖) *
                (childValues.map norm).prod := by
                  simpa [driftTreeValue, childValues] using hlocal
            _ ≤ stepSize T J * Real.exp (bounds.driftLipschitzConstant * T) *
                (bounds.B₀ * bounds.B₁ ^ (direct.card + childValues.length) *
                  ((direct.card + childValues.length).factorial : ℝ) ^ bounds.τ) *
                (∏ j ∈ direct,
                  ‖diffusionCoefficient diffusion T j (gridTime T J time)‖) *
                (driftTreeMajorants bounds diffusion children assignments).prod := by
                  exact mul_le_mul_of_nonneg_left hforest hprefactor
            _ = driftTreeMajorant bounds diffusion
                (.node direct children) (.node time assignments) := by
                  simp only [driftTreeMajorant]
                  rw [← hlength])
    (fun assignments parentTime _ hvalid _ ↦ by
      cases assignments <;>
        simp [DriftTimeData.ValidChildren, driftTreeValues, driftTreeMajorants] at hvalid ⊢)
    (fun head tail hhead htail assignments parentTime htrees hvalid hparent ↦ by
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          have hheadBound := hhead assignment parentTime (htrees head (by simp))
            hvalid.1 hparent
          have htailBound := htail assignments parentTime
            (fun child hchild ↦ htrees child (by simp [hchild])) hvalid.2 hparent
          have hheadNonneg : 0 ≤ driftTreeMajorant bounds diffusion head assignment :=
            (norm_nonneg _).trans hheadBound
          have htailNormNonneg : 0 ≤
              ((driftTreeValues drift diffusion T x₀ z parentTime tail assignments).map norm).prod := by
            apply List.prod_nonneg
            intro value hvalue
            rcases List.mem_map.mp hvalue with ⟨state, _, rfl⟩
            exact norm_nonneg state
          simpa only [driftTreeValues, driftTreeMajorants, List.map_cons, List.prod_cons] using
            mul_le_mul hheadBound htailBound htailNormNonneg hheadNonneg)
    tree assignment parentTime htree hassignment hparent

/-- Forest form of `norm_driftTreeValue_le_majorant`, used at the payoff root. -/
theorem prod_norm_driftTreeValues_le_majorants
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) (trees : List (DriftTreeData J noiseDim))
    (assignments : List DriftTimeData) (parentTime : ℕ)
    (htrees : ∀ tree ∈ trees, tree.Valid)
    (hassignments : DriftTimeData.ValidChildren parentTime trees assignments)
    (hparent : parentTime ≤ numSteps J) :
    ((driftTreeValues drift diffusion T x₀ z parentTime trees assignments).map norm).prod ≤
      (driftTreeMajorants bounds diffusion trees assignments).prod := by
  induction trees generalizing assignments with
  | nil =>
      cases assignments <;>
        simp [DriftTimeData.ValidChildren, driftTreeValues, driftTreeMajorants] at hassignments ⊢
  | cons head tail ih =>
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hassignments
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hassignments
          have hhead := bounds.norm_driftTreeValue_le_majorant hT diffusion x₀ z
            head assignment parentTime (htrees head (by simp)) hassignments.1 hparent
          have htail := ih assignments
            (fun tree htree ↦ htrees tree (by simp [htree])) hassignments.2
          have hmajorantNonneg : 0 ≤ driftTreeMajorant bounds diffusion head assignment :=
            (norm_nonneg _).trans hhead
          have hnormProdNonneg : 0 ≤
              ((driftTreeValues drift diffusion T x₀ z parentTime tail assignments).map norm).prod := by
            apply List.prod_nonneg
            intro value hvalue
            rcases List.mem_map.mp hvalue with ⟨state, _, rfl⟩
            exact norm_nonneg state
          simpa only [driftTreeValues, driftTreeMajorants, List.map_cons, List.prod_cons] using
            mul_le_mul hhead htail hnormProdNonneg hmajorantNonneg

/-- The coefficient majorant at the payoff root, prior to separating the common powers of `h`
and the bridge factors by vertex. -/
def payoffTreeMajorant
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim)
    (tree : PayoffTreeData J noiseDim) (assignment : TimeAssignment) : ℝ :=
  let n := tree.direct.card + tree.children.length
  (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
    (∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖) *
    (driftTreeMajorants bounds diffusion tree.children assignment.children).prod

/-- First assertion of Lemma B.8 in recursive form: the normalized value of every valid timed
payoff tree is bounded by its explicit vertexwise majorant. -/
theorem TimedPayoffTree.normalized_norm_value_le_majorant
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) {u : Finset (Index J noiseDim)} (hu : u.Nonempty)
    {m : ℕ} (hm : m ≤ numSteps J) (timedTree : TimedPayoffTree J noiseDim u m) :
    Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
        ‖timedTree.value drift payoff diffusion T x₀ z‖ ≤
      payoffTreeMajorant bounds diffusion timedTree.tree.data timedTree.assignment := by
  let data := timedTree.tree.data
  let childValues := driftTreeValues drift diffusion T x₀ z m
    data.children timedTree.assignment.children
  let n := data.direct.card + childValues.length
  let directions := vertexDirections data.direct
    (fun j ↦ diffusionCoefficient diffusion T j T) childValues
  have hlength : childValues.length = data.children.length :=
    driftTreeValues_length_eq_of_validChildren drift diffusion T x₀ z m
      data.children timedTree.assignment.children timedTree.assignmentValid.2
  have hn : 1 ≤ n := by
    dsimp [n]
    by_cases hdirect : data.direct.Nonempty
    · have hcard : 0 < data.direct.card := Finset.card_pos.mpr hdirect
      omega
    · by_cases hchildren : data.children = []
      · have hdirectEmpty : data.direct = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hdirect
        have huEmpty : u = ∅ := by
          calc
            u = data.support := by
              simpa [data] using timedTree.tree.valid.1.symm
            _ = ∅ := by
              simp [PayoffTreeData.support, childrenSupport, hdirectEmpty, hchildren]
        exact (hu.ne_empty huEmpty).elim
      · have hchildrenPos : 0 < data.children.length :=
          List.length_pos_of_ne_nil hchildren
        rw [hlength]
        omega
  have hpayoff :
      Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
          ‖iteratedFDeriv ℝ n payoff (stateNat drift diffusion T x₀ z m) directions‖ ≤
        (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
          ∏ i, ‖directions i‖ := by
    have happly :
        ‖iteratedFDeriv ℝ n payoff (stateNat drift diffusion T x₀ z m) directions‖ ≤
          (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ *
            Real.exp (bounds.β * ‖stateNat drift diffusion T x₀ z m‖)) *
            ∏ i, ‖directions i‖ :=
      ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
        (bounds.payoff_derivative_norm n hn (stateNat drift diffusion T x₀ z m))
        (fun _ ↦ le_rfl)
    have hexpNonneg :
        0 ≤ Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) :=
      (Real.exp_pos _).le
    calc
      Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
          ‖iteratedFDeriv ℝ n payoff (stateNat drift diffusion T x₀ z m) directions‖ ≤
        Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
          (((bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
            Real.exp (bounds.β * ‖stateNat drift diffusion T x₀ z m‖)) *
            ∏ i, ‖directions i‖) :=
        mul_le_mul_of_nonneg_left happly hexpNonneg
      _ = (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
          ∏ i, ‖directions i‖ := by
        have hexpCancel :
            Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
              Real.exp (bounds.β * ‖stateNat drift diffusion T x₀ z m‖) = 1 := by
          rw [← Real.exp_add]
          have hzero : -bounds.β * ‖stateNat drift diffusion T x₀ z m‖ +
              bounds.β * ‖stateNat drift diffusion T x₀ z m‖ = 0 := by ring
          rw [hzero, Real.exp_zero]
        calc
          _ = (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
              (Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
                Real.exp (bounds.β * ‖stateNat drift diffusion T x₀ z m‖)) *
              ∏ i, ‖directions i‖ := by ring
          _ = _ := by rw [hexpCancel, mul_one]
  have hforest := bounds.prod_norm_driftTreeValues_le_majorants hT diffusion x₀ z
    data.children timedTree.assignment.children m timedTree.tree.valid.2.2.2.2.2
    timedTree.assignmentValid.2 hm
  have hcoefficient : 0 ≤
      bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ := by
    exact mul_nonneg
      (mul_nonneg bounds.G₀_pos.le (pow_nonneg bounds.G₁_pos.le _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hdirectProduct : 0 ≤
      ∏ j ∈ data.direct, ‖diffusionCoefficient diffusion T j T‖ :=
    Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  change Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
      ‖iteratedFDeriv ℝ n payoff (stateNat drift diffusion T x₀ z m) directions‖ ≤ _
  calc
    Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
        ‖iteratedFDeriv ℝ n payoff (stateNat drift diffusion T x₀ z m) directions‖ ≤
      (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        ∏ i, ‖directions i‖ := hpayoff
    _ = (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        (∏ j ∈ data.direct, ‖diffusionCoefficient diffusion T j T‖) *
        (childValues.map norm).prod := by
          rw [prod_norm_vertexDirections]
          ring
    _ ≤ (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        (∏ j ∈ data.direct, ‖diffusionCoefficient diffusion T j T‖) *
        (driftTreeMajorants bounds diffusion data.children
          timedTree.assignment.children).prod := by
            exact mul_le_mul_of_nonneg_left hforest
              (mul_nonneg hcoefficient hdirectProduct)
    _ = payoffTreeMajorant bounds diffusion data timedTree.assignment := by
      simp only [payoffTreeMajorant]
      rw [← hlength]

/-- Product of the propagator and drift-derivative constants over a drift subtree. -/
def DriftTreeData.analyticCoefficient
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) :
    DriftTreeData J noiseDim → ℝ
  | .node direct children =>
      let n := direct.card + children.length
      Real.exp (bounds.driftLipschitzConstant * T) *
        (bounds.B₀ * bounds.B₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        (children.map (analyticCoefficient bounds)).prod
termination_by tree => sizeOf tree

/-- Exponent of `coefficientBase` produced by the vertexwise factorial split. -/
def DriftTreeData.coefficientComplexity {J noiseDim : ℕ} :
    DriftTreeData J noiseDim → ℕ
  | .node direct children =>
      1 + 2 * (direct.card + children.length) +
        (children.map coefficientComplexity).sum
termination_by tree => sizeOf tree

theorem DriftTreeData.analyticCoefficient_nonneg
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (tree : DriftTreeData J noiseDim) :
    0 ≤ DriftTreeData.analyticCoefficient bounds tree := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ 0 ≤ DriftTreeData.analyticCoefficient bounds tree)
    (motive_2 := fun children ↦
      0 ≤ (children.map (DriftTreeData.analyticCoefficient bounds)).prod)
    (fun direct children hchildren ↦ by
      simp only [DriftTreeData.analyticCoefficient]
      exact mul_nonneg
        (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg
            (mul_nonneg bounds.B₀_pos.le (pow_nonneg bounds.B₁_pos.le _))
            (Real.rpow_nonneg (by positivity) _)))
        hchildren)
    (by simp)
    (fun head tail hhead htail ↦ by
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg hhead htail)
    tree

/-- Recursive coefficient estimate after splitting the factorial at every drift vertex. -/
theorem DriftTreeData.analyticCoefficient_le_split
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (tree : DriftTreeData J noiseDim) :
    DriftTreeData.analyticCoefficient bounds tree ≤
      bounds.coefficientBase ^ DriftTreeData.coefficientComplexity tree *
        (tree.directFactorialProduct : ℝ) ^ bounds.τ *
        (tree.childFactorialProduct : ℝ) ^ bounds.τ := by
  have hK : 0 ≤ bounds.coefficientBase :=
    zero_le_one.trans bounds.one_le_coefficientBase
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦
      DriftTreeData.analyticCoefficient bounds tree ≤
        bounds.coefficientBase ^ DriftTreeData.coefficientComplexity tree *
          (tree.directFactorialProduct : ℝ) ^ bounds.τ *
          (tree.childFactorialProduct : ℝ) ^ bounds.τ)
    (motive_2 := fun children ↦
      (children.map (DriftTreeData.analyticCoefficient bounds)).prod ≤
        bounds.coefficientBase ^
            (children.map DriftTreeData.coefficientComplexity).sum *
          ((children.map DriftTreeData.directFactorialProduct).prod : ℝ) ^ bounds.τ *
          ((children.map DriftTreeData.childFactorialProduct).prod : ℝ) ^ bounds.τ)
    (fun direct children hchildren ↦ by
      have hlocal := drift_local_coefficient_le bounds direct.card children.length
      have hforestNonneg :
          0 ≤ (children.map (DriftTreeData.analyticCoefficient bounds)).prod := by
        apply List.prod_nonneg
        intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨child, _, rfl⟩
        exact DriftTreeData.analyticCoefficient_nonneg bounds child
      have hlocalUpperNonneg : 0 ≤
          bounds.coefficientBase ^ (1 + 2 * (direct.card + children.length)) *
            (direct.card.factorial : ℝ) ^ bounds.τ *
            (children.length.factorial : ℝ) ^ bounds.τ := by positivity
      simp only [DriftTreeData.analyticCoefficient,
        DriftTreeData.coefficientComplexity, DriftTreeData.directFactorialProduct,
        DriftTreeData.childFactorialProduct]
      calc
        Real.exp (bounds.driftLipschitzConstant * T) *
              (bounds.B₀ * bounds.B₁ ^ (direct.card + children.length) *
                (direct.card + children.length).factorial ^ bounds.τ) *
              (children.map (DriftTreeData.analyticCoefficient bounds)).prod ≤
            (bounds.coefficientBase ^ (1 + 2 * (direct.card + children.length)) *
                (direct.card.factorial : ℝ) ^ bounds.τ *
                (children.length.factorial : ℝ) ^ bounds.τ) *
              (bounds.coefficientBase ^
                    (children.map DriftTreeData.coefficientComplexity).sum *
                ((children.map DriftTreeData.directFactorialProduct).prod : ℝ) ^
                    bounds.τ *
                ((children.map DriftTreeData.childFactorialProduct).prod : ℝ) ^
                    bounds.τ) :=
          mul_le_mul hlocal hchildren hforestNonneg hlocalUpperNonneg
        _ = _ := by
          rw [Nat.cast_mul, Nat.cast_mul]
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
          simp only [Nat.cast_list_prod]
          rw [pow_add]
          ring)
    (by simp)
    (fun head tail hhead htail ↦ by
      have htailNonneg :
          0 ≤ (tail.map (DriftTreeData.analyticCoefficient bounds)).prod := by
        apply List.prod_nonneg
        intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨child, _, rfl⟩
        exact DriftTreeData.analyticCoefficient_nonneg bounds child
      have hheadUpperNonneg : 0 ≤
          bounds.coefficientBase ^ DriftTreeData.coefficientComplexity head *
            (head.directFactorialProduct : ℝ) ^ bounds.τ *
            (head.childFactorialProduct : ℝ) ^ bounds.τ := by
        exact mul_nonneg
          (mul_nonneg
            (pow_nonneg (zero_le_one.trans bounds.one_le_coefficientBase) _)
            (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (by positivity) _)
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      calc
        DriftTreeData.analyticCoefficient bounds head *
              (tail.map (DriftTreeData.analyticCoefficient bounds)).prod ≤
            (bounds.coefficientBase ^ DriftTreeData.coefficientComplexity head *
                (head.directFactorialProduct : ℝ) ^ bounds.τ *
                (head.childFactorialProduct : ℝ) ^ bounds.τ) *
              (bounds.coefficientBase ^
                    (tail.map DriftTreeData.coefficientComplexity).sum *
                ((tail.map DriftTreeData.directFactorialProduct).prod : ℝ) ^ bounds.τ *
                ((tail.map DriftTreeData.childFactorialProduct).prod : ℝ) ^ bounds.τ) :=
          mul_le_mul hhead htail htailNonneg hheadUpperNonneg
        _ = _ := by
          rw [Nat.cast_mul, Nat.cast_mul]
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
          simp only [Nat.cast_list_prod]
          rw [pow_add]
          ring)
    tree

/-- Forest form of `DriftTreeData.analyticCoefficient_le_split`. -/
theorem driftForest_analyticCoefficient_le_split
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (children : List (DriftTreeData J noiseDim)) :
    (children.map (DriftTreeData.analyticCoefficient bounds)).prod ≤
      bounds.coefficientBase ^
          (children.map DriftTreeData.coefficientComplexity).sum *
        ((children.map DriftTreeData.directFactorialProduct).prod : ℝ) ^ bounds.τ *
        ((children.map DriftTreeData.childFactorialProduct).prod : ℝ) ^ bounds.τ := by
  induction children with
  | nil => simp
  | cons head tail ih =>
      have hhead := DriftTreeData.analyticCoefficient_le_split bounds head
      have htailNonneg :
          0 ≤ (tail.map (DriftTreeData.analyticCoefficient bounds)).prod := by
        apply List.prod_nonneg
        intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨child, _, rfl⟩
        exact DriftTreeData.analyticCoefficient_nonneg bounds child
      have hheadUpperNonneg : 0 ≤
          bounds.coefficientBase ^ DriftTreeData.coefficientComplexity head *
            (head.directFactorialProduct : ℝ) ^ bounds.τ *
            (head.childFactorialProduct : ℝ) ^ bounds.τ := by
        exact mul_nonneg
          (mul_nonneg
            (pow_nonneg (zero_le_one.trans bounds.one_le_coefficientBase) _)
            (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (by positivity) _)
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      calc
        DriftTreeData.analyticCoefficient bounds head *
              (tail.map (DriftTreeData.analyticCoefficient bounds)).prod ≤
            (bounds.coefficientBase ^ DriftTreeData.coefficientComplexity head *
                (head.directFactorialProduct : ℝ) ^ bounds.τ *
                (head.childFactorialProduct : ℝ) ^ bounds.τ) *
              (bounds.coefficientBase ^
                    (tail.map DriftTreeData.coefficientComplexity).sum *
                ((tail.map DriftTreeData.directFactorialProduct).prod : ℝ) ^ bounds.τ *
                ((tail.map DriftTreeData.childFactorialProduct).prod : ℝ) ^ bounds.τ) :=
          mul_le_mul hhead ih htailNonneg hheadUpperNonneg
        _ = _ := by
          rw [Nat.cast_mul, Nat.cast_mul]
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
          simp only [Nat.cast_list_prod]
          rw [pow_add]
          ring

mutual
  /-- Product of the nonroot Brownian-bridge factors attached to one timed drift subtree. -/
  def driftTreeDirectionProduct
      {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ) :
      DriftTreeData J noiseDim → DriftTimeData → ℝ
    | .node direct children, .node time assignments =>
        (∏ j ∈ direct,
          ‖diffusionCoefficient diffusion T j (gridTime T J time)‖) *
          (driftTreeDirectionProducts diffusion T children assignments).prod

  /-- Direction products for an aligned timed forest. -/
  def driftTreeDirectionProducts
      {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ) :
      List (DriftTreeData J noiseDim) → List DriftTimeData → List ℝ
    | tree :: trees, assignment :: assignments =>
        driftTreeDirectionProduct diffusion T tree assignment ::
          driftTreeDirectionProducts diffusion T trees assignments
    | _, _ => []
end

/-- The paper's coefficient `B_ᵀ`: payoff-root constant and terminal bridge factors, followed
by all drift-vertex analytic constants. -/
def PayoffTreeData.analyticCoefficient
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (tree : PayoffTreeData J noiseDim) : ℝ :=
  let n := tree.direct.card + tree.children.length
  (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
    (∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖) *
    (tree.children.map (DriftTreeData.analyticCoefficient bounds)).prod

theorem PayoffTreeData.analyticCoefficient_nonneg
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (tree : PayoffTreeData J noiseDim) :
    0 ≤ PayoffTreeData.analyticCoefficient bounds diffusion tree := by
  unfold PayoffTreeData.analyticCoefficient
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact mul_nonneg
      (mul_nonneg bounds.G₀_pos.le (pow_nonneg bounds.G₁_pos.le _))
      (Real.rpow_nonneg (by positivity) _)
  · exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  · exact List.prod_nonneg fun value hvalue ↦ by
      rcases List.mem_map.mp hvalue with ⟨child, _, rfl⟩
      exact DriftTreeData.analyticCoefficient_nonneg bounds child

/-- Total exponent of `coefficientBase` after the vertexwise factorial split, including the
payoff root. -/
def PayoffTreeData.coefficientComplexity
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) : ℕ :=
  1 + 2 * (tree.direct.card + tree.children.length) +
    (tree.children.map DriftTreeData.coefficientComplexity).sum

/-- Paper Lemma B.8 before the final count over tree shapes: the payoff coefficient is bounded
by a root factor, the products of direct and child factorials, and one common model base. -/
theorem PayoffTreeData.analyticCoefficient_le_split
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (tree : PayoffTreeData J noiseDim) :
    PayoffTreeData.analyticCoefficient bounds diffusion tree ≤
      bounds.coefficientBase ^ PayoffTreeData.coefficientComplexity tree *
        ((tree.direct.card.factorial : ℝ) ^ bounds.τ *
          ∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖) *
        (tree.nonrootDirectFactorialProduct : ℝ) ^ bounds.τ *
        (tree.childFactorialProduct : ℝ) ^ bounds.τ := by
  have hlocal := payoff_local_coefficient_le bounds tree.direct.card tree.children.length
  have hrootDirections : 0 ≤
      ∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖ :=
    Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hroot := mul_le_mul_of_nonneg_right hlocal hrootDirections
  have hforest := driftForest_analyticCoefficient_le_split bounds tree.children
  have hforestNonneg :
      0 ≤ (tree.children.map (DriftTreeData.analyticCoefficient bounds)).prod := by
    apply List.prod_nonneg
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨child, _, rfl⟩
    exact DriftTreeData.analyticCoefficient_nonneg bounds child
  have hrootUpperNonneg : 0 ≤
      (bounds.coefficientBase ^ (1 + 2 * (tree.direct.card + tree.children.length)) *
          (tree.direct.card.factorial : ℝ) ^ bounds.τ *
          (tree.children.length.factorial : ℝ) ^ bounds.τ) *
        (∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (pow_nonneg (zero_le_one.trans bounds.one_le_coefficientBase) _)
          (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _))
      hrootDirections
  simp only [PayoffTreeData.analyticCoefficient,
    PayoffTreeData.coefficientComplexity,
    PayoffTreeData.nonrootDirectFactorialProduct,
    PayoffTreeData.childFactorialProduct]
  calc
    (bounds.G₀ * bounds.G₁ ^ (tree.direct.card + tree.children.length) *
          ((tree.direct.card + tree.children.length).factorial : ℝ) ^ bounds.τ) *
          (∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖) *
          (tree.children.map (DriftTreeData.analyticCoefficient bounds)).prod ≤
        ((bounds.coefficientBase ^
              (1 + 2 * (tree.direct.card + tree.children.length)) *
            (tree.direct.card.factorial : ℝ) ^ bounds.τ *
            (tree.children.length.factorial : ℝ) ^ bounds.τ) *
          (∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖)) *
        (bounds.coefficientBase ^
              (tree.children.map DriftTreeData.coefficientComplexity).sum *
            ((tree.children.map DriftTreeData.directFactorialProduct).prod : ℝ) ^
              bounds.τ *
            ((tree.children.map DriftTreeData.childFactorialProduct).prod : ℝ) ^
              bounds.τ) :=
      mul_le_mul hroot hforest hforestNonneg hrootUpperNonneg
    _ = _ := by
      rw [Nat.cast_mul]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      simp only [Nat.cast_list_prod]
      rw [pow_add]
      ring

theorem DriftTreeData.coefficientComplexity_eq
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    DriftTreeData.coefficientComplexity tree =
      tree.vertexCount + 2 * (tree.directCardSum + tree.childCountSum) := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ DriftTreeData.coefficientComplexity tree =
      tree.vertexCount + 2 * (tree.directCardSum + tree.childCountSum))
    (motive_2 := fun children ↦
      (children.map DriftTreeData.coefficientComplexity).sum =
        (children.map DriftTreeData.vertexCount).sum +
          2 * ((children.map DriftTreeData.directCardSum).sum +
            (children.map DriftTreeData.childCountSum).sum))
    (fun direct children hchildren ↦ by
      simp only [DriftTreeData.coefficientComplexity, DriftTreeData.vertexCount,
        DriftTreeData.directCardSum, DriftTreeData.childCountSum]
      rw [hchildren]
      omega)
    (by simp)
    (fun head tail hhead htail ↦ by
      simp only [List.map_cons, List.sum_cons]
      rw [hhead, htail]
      omega)
    tree

theorem PayoffTreeData.coefficientComplexity_eq
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    PayoffTreeData.coefficientComplexity tree =
      tree.vertexCount + 2 * (tree.directCardSum + tree.childCountSum) := by
  have hforest :
      (tree.children.map DriftTreeData.coefficientComplexity).sum =
        (tree.children.map DriftTreeData.vertexCount).sum +
          2 * ((tree.children.map DriftTreeData.directCardSum).sum +
            (tree.children.map DriftTreeData.childCountSum).sum) := by
    induction tree.children with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [DriftTreeData.coefficientComplexity_eq head, ih]
        omega
  simp only [PayoffTreeData.coefficientComplexity, PayoffTreeData.vertexCount,
    PayoffTreeData.directCardSum, PayoffTreeData.childCountSum]
  rw [hforest]
  omega

/-- The complexity exponent is bounded by the paper's `2|u| + 6k`. -/
theorem PayoffTreeData.coefficientComplexity_le
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    {u : Finset (Index J noiseDim)} (hvalid : tree.Valid u)
    (hchildren : tree.children ≠ []) :
    PayoffTreeData.coefficientComplexity tree ≤
      2 * u.card + 6 * tree.nonemptyDriftCount := by
  have hcomplexity := PayoffTreeData.coefficientComplexity_eq tree
  have hdirect := tree.valid_directCardSum_eq_support_card hvalid
  have hchildCount := tree.childCountSum_add_one_eq_vertexCount
  have hvertices := tree.vertexCount_le_two_mul_nonemptyDriftCount hvalid hchildren
  omega

/-- The paper's `C₀ = K^6`. -/
def coefficientCountBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) : ℝ :=
  bounds.coefficientBase ^ 6

/-- Per-tree coefficient estimate used in the proof of paper Lemma B.8, in the exact form
consumed by the weighted Catalan count. -/
theorem PayoffTreeData.analyticCoefficient_le_countingForm
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (tree : PayoffTreeData J noiseDim)
    (blocks : Finset (Finset (Index J noiseDim)))
    {u : Finset (Index J noiseDim)} (hvalid : tree.Valid u)
    (hblocksNonempty : blocks.Nonempty)
    (hblocks : tree.nonemptyDirectLabels.Perm blocks.toList) :
    PayoffTreeData.analyticCoefficient bounds diffusion tree ≤
      bounds.coefficientCountBase ^ (u.card + blocks.card) *
        ((tree.direct.card.factorial : ℝ) ^ bounds.τ *
          ∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖) *
        (∏ block ∈ blocks, (block.card.factorial : ℝ) ^ bounds.τ) *
        (blocks.card.factorial : ℝ) ^ (bounds.τ - 1) *
        (tree.childFactorialProduct : ℝ) := by
  have hcount : tree.nonemptyDriftCount = blocks.card := by
    have hlength := hblocks.length_eq
    rw [tree.length_nonemptyDirectLabels_eq_nonemptyDriftCount] at hlength
    simpa using hlength
  have hchildren : tree.children ≠ [] := by
    intro hempty
    have hzero : tree.nonemptyDriftCount = 0 := by
      simp [PayoffTreeData.nonemptyDriftCount, hempty]
    have hblocksZero : blocks.card = 0 := by omega
    exact hblocksNonempty.ne_empty (Finset.card_eq_zero.mp hblocksZero)
  have hcomplexity := PayoffTreeData.coefficientComplexity_le tree hvalid hchildren
  rw [hcount] at hcomplexity
  have hexponent :
      PayoffTreeData.coefficientComplexity tree ≤ 6 * (u.card + blocks.card) := by
    omega
  have hKpow :
      bounds.coefficientBase ^ PayoffTreeData.coefficientComplexity tree ≤
        bounds.coefficientCountBase ^ (u.card + blocks.card) := by
    calc
      bounds.coefficientBase ^ PayoffTreeData.coefficientComplexity tree ≤
          bounds.coefficientBase ^ (6 * (u.card + blocks.card)) :=
        pow_le_pow_right₀ bounds.one_le_coefficientBase hexponent
      _ = bounds.coefficientCountBase ^ (u.card + blocks.card) := by
        simp only [coefficientCountBase, pow_mul]
  have hdirectPow :
      (tree.nonrootDirectFactorialProduct : ℝ) ^ bounds.τ =
        ∏ block ∈ blocks, (block.card.factorial : ℝ) ^ bounds.τ := by
    rw [tree.nonrootDirectFactorialProduct_eq_blocks blocks hblocks]
    rw [Nat.cast_prod]
    exact finset_prod_rpow blocks (fun block ↦ (block.card.factorial : ℝ))
      bounds.τ (fun _ _ ↦ by positivity)
  have hQnat : tree.childFactorialProduct ≤ blocks.card.factorial := by
    rw [← hcount]
    exact tree.childFactorialProduct_le_nonemptyDriftCount_factorial hvalid hchildren
  have hQpos : (0 : ℝ) < tree.childFactorialProduct := by
    exact_mod_cast tree.childFactorialProduct_pos
  have hQ :
      (tree.childFactorialProduct : ℝ) ^ bounds.τ ≤
        (blocks.card.factorial : ℝ) ^ (bounds.τ - 1) *
          (tree.childFactorialProduct : ℝ) := by
    apply rpow_le_rpow_sub_one_mul hQpos _ bounds.τ_mem.1
    exact_mod_cast hQnat
  have hsplit := PayoffTreeData.analyticCoefficient_le_split bounds diffusion tree
  let rootFactor : ℝ :=
    (tree.direct.card.factorial : ℝ) ^ bounds.τ *
      ∏ j ∈ tree.direct, ‖diffusionCoefficient diffusion T j T‖
  let blockFactor : ℝ :=
    ∏ block ∈ blocks, (block.card.factorial : ℝ) ^ bounds.τ
  have hrootFactor : 0 ≤ rootFactor := by
    dsimp [rootFactor]
    positivity
  have hblockFactor : 0 ≤ blockFactor := by
    dsimp [blockFactor]
    positivity
  have hC₀ : 0 ≤ bounds.coefficientCountBase := by
    exact pow_nonneg (zero_le_one.trans bounds.one_le_coefficientBase) _
  calc
    PayoffTreeData.analyticCoefficient bounds diffusion tree ≤
        bounds.coefficientBase ^ PayoffTreeData.coefficientComplexity tree *
          rootFactor * (tree.nonrootDirectFactorialProduct : ℝ) ^ bounds.τ *
          (tree.childFactorialProduct : ℝ) ^ bounds.τ := by
      simpa [rootFactor] using hsplit
    _ ≤ bounds.coefficientCountBase ^ (u.card + blocks.card) *
          rootFactor * (tree.nonrootDirectFactorialProduct : ℝ) ^ bounds.τ *
          (tree.childFactorialProduct : ℝ) ^ bounds.τ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKpow hrootFactor)
          (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (by positivity) _)
    _ = bounds.coefficientCountBase ^ (u.card + blocks.card) *
          rootFactor * blockFactor *
          (tree.childFactorialProduct : ℝ) ^ bounds.τ := by
      rw [hdirectPow]
    _ ≤ bounds.coefficientCountBase ^ (u.card + blocks.card) *
          rootFactor * blockFactor *
          ((blocks.card.factorial : ℝ) ^ (bounds.τ - 1) *
            (tree.childFactorialProduct : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hQ
        (mul_nonneg
          (mul_nonneg (pow_nonneg hC₀ _) hrootFactor)
          hblockFactor)
    _ = _ := by
      dsimp [rootFactor, blockFactor]
      ring

/-- Coefficient-sum conclusion of paper Lemma B.8 for any finite family satisfying the
defining properties of `Γ(E, π)`. -/
theorem analyticCoefficient_sum_le
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim)
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (support root : Finset (Index J noiseDim))
    (hblocksNonempty : blocks.Nonempty)
    (hvalid : ∀ tree ∈ family, tree.Valid support)
    (hroot : ∀ tree ∈ family, tree.direct = root)
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList) :
    ∑ tree ∈ family, PayoffTreeData.analyticCoefficient bounds diffusion tree ≤
      bounds.coefficientCountBase ^ (support.card + blocks.card) *
        ((root.card.factorial : ℝ) ^ bounds.τ *
          ∏ j ∈ root, ‖diffusionCoefficient diffusion T j T‖) *
        (∏ block ∈ blocks, (block.card.factorial : ℝ) ^ bounds.τ) *
        (64 : ℝ) ^ blocks.card * (blocks.card.factorial : ℝ) ^ bounds.τ := by
  let rootFactor : ℝ :=
    (root.card.factorial : ℝ) ^ bounds.τ *
      ∏ j ∈ root, ‖diffusionCoefficient diffusion T j T‖
  let blockFactor : ℝ :=
    ∏ block ∈ blocks, (block.card.factorial : ℝ) ^ bounds.τ
  have hvertices : ∀ tree ∈ family, tree.vertexCount ≤ 2 * blocks.card := by
    intro tree htree
    have hcount : tree.nonemptyDriftCount = blocks.card := by
      have hlength := (hblocks tree htree).length_eq
      rw [tree.length_nonemptyDirectLabels_eq_nonemptyDriftCount] at hlength
      simpa using hlength
    have hchildren : tree.children ≠ [] := by
      intro hempty
      have hzero : tree.nonemptyDriftCount = 0 := by
        simp [PayoffTreeData.nonemptyDriftCount, hempty]
      have hblocksZero : blocks.card = 0 := by omega
      exact hblocksNonempty.ne_empty (Finset.card_eq_zero.mp hblocksZero)
    rw [← hcount]
    exact tree.vertexCount_le_two_mul_nonemptyDriftCount (hvalid tree htree) hchildren
  apply coefficient_sum_le_of_tree_bound family blocks support root
    hvalid hroot hblocks hvertices
    (PayoffTreeData.analyticCoefficient bounds diffusion)
    bounds.coefficientCountBase rootFactor blockFactor bounds.τ support.card
  · exact pow_nonneg (zero_le_one.trans bounds.one_le_coefficientBase) _
  · dsimp [rootFactor]
    positivity
  · dsimp [blockFactor]
    positivity
  · intro tree htree
    have htreeBound := PayoffTreeData.analyticCoefficient_le_countingForm
      bounds diffusion tree blocks (hvalid tree htree) hblocksNonempty (hblocks tree htree)
    rw [hroot tree htree] at htreeBound
    simpa [rootFactor, blockFactor, mul_assoc] using htreeBound

/-- Product of all Brownian-bridge factors below the payoff root. -/
def payoffTreeNonrootDirectionProduct
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (tree : PayoffTreeData J noiseDim) (assignment : TimeAssignment) : ℝ :=
  (driftTreeDirectionProducts diffusion T tree.children assignment.children).prod

/-- The recursive majorant factors into one power of `h` per drift vertex, the time-independent
analytic coefficient, and the product of all nonroot bridge directions. -/
theorem driftTreeMajorant_eq_factorized
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (tree : DriftTreeData J noiseDim)
    (assignment : DriftTimeData) (parentTime : ℕ)
    (hassignment : assignment.Valid parentTime tree) :
    driftTreeMajorant bounds diffusion tree assignment =
      stepSize T J ^ tree.vertexCount * DriftTreeData.analyticCoefficient bounds tree *
        driftTreeDirectionProduct diffusion T tree assignment := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ ∀ assignment parentTime,
      assignment.Valid parentTime tree →
        driftTreeMajorant bounds diffusion tree assignment =
          stepSize T J ^ tree.vertexCount * DriftTreeData.analyticCoefficient bounds tree *
            driftTreeDirectionProduct diffusion T tree assignment)
    (motive_2 := fun trees ↦ ∀ assignments parentTime,
      DriftTimeData.ValidChildren parentTime trees assignments →
        (driftTreeMajorants bounds diffusion trees assignments).prod =
          stepSize T J ^ (trees.map DriftTreeData.vertexCount).sum *
            (trees.map (DriftTreeData.analyticCoefficient bounds)).prod *
            (driftTreeDirectionProducts diffusion T trees assignments).prod)
    (fun direct children hchildren assignment parentTime hvalid ↦ by
      cases assignment with
      | node time assignments =>
          simp only [DriftTimeData.Valid] at hvalid
          have hforest := hchildren assignments time hvalid.2
          simp only [driftTreeMajorant, DriftTreeData.analyticCoefficient,
            driftTreeDirectionProduct, DriftTreeData.vertexCount]
          rw [hforest]
          rw [show 1 + (children.map DriftTreeData.vertexCount).sum =
              (children.map DriftTreeData.vertexCount).sum + 1 by omega, pow_succ]
          ring)
    (fun assignments _ hvalid ↦ by
      cases assignments <;>
        simp [DriftTimeData.ValidChildren, driftTreeMajorants,
          driftTreeDirectionProducts] at hvalid ⊢)
    (fun head tail hhead htail assignments parentTime hvalid ↦ by
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          have hheadFactor := hhead assignment parentTime hvalid.1
          have htailFactor := htail assignments parentTime hvalid.2
          simp only [driftTreeMajorants, driftTreeDirectionProducts, List.map_cons,
            List.sum_cons, List.prod_cons]
          rw [hheadFactor, htailFactor, pow_add]
          ring)
    tree assignment parentTime hassignment

/-- Forest form of `driftTreeMajorant_eq_factorized`. -/
theorem driftTreeMajorants_eq_factorized
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (trees : List (DriftTreeData J noiseDim))
    (assignments : List DriftTimeData) (parentTime : ℕ)
    (hassignments : DriftTimeData.ValidChildren parentTime trees assignments) :
    (driftTreeMajorants bounds diffusion trees assignments).prod =
      stepSize T J ^ (trees.map DriftTreeData.vertexCount).sum *
        (trees.map (DriftTreeData.analyticCoefficient bounds)).prod *
        (driftTreeDirectionProducts diffusion T trees assignments).prod := by
  induction trees generalizing assignments with
  | nil =>
      cases assignments <;>
        simp [DriftTimeData.ValidChildren, driftTreeMajorants,
          driftTreeDirectionProducts] at hassignments ⊢
  | cons head tail ih =>
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hassignments
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hassignments
          have hhead := driftTreeMajorant_eq_factorized bounds diffusion head
            assignment parentTime hassignments.1
          have htail := ih assignments hassignments.2
          simp only [driftTreeMajorants, driftTreeDirectionProducts, List.map_cons,
            List.sum_cons, List.prod_cons]
          rw [hhead, htail, pow_add]
          ring

/-- Factored form of the payoff-tree majorant used in the proof of paper Lemma B.8. -/
theorem payoffTreeMajorant_eq_factorized
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (tree : PayoffTreeData J noiseDim)
    (assignment : TimeAssignment) (m : ℕ)
    (hassignment : assignment.Valid m tree) :
    payoffTreeMajorant bounds diffusion tree assignment =
      stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion tree *
        payoffTreeNonrootDirectionProduct diffusion T tree assignment := by
  have hforest :
      (driftTreeMajorants bounds diffusion tree.children assignment.children).prod =
        stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
          (tree.children.map (DriftTreeData.analyticCoefficient bounds)).prod *
          (driftTreeDirectionProducts diffusion T tree.children
            assignment.children).prod := by
    exact driftTreeMajorants_eq_factorized bounds diffusion tree.children
      assignment.children m hassignment.2
  simp only [payoffTreeMajorant, PayoffTreeData.analyticCoefficient,
    payoffTreeNonrootDirectionProduct]
  rw [hforest]
  ring

/-- The per-tree factorization underlying Equation (B.17). -/
theorem TimedPayoffTree.normalized_norm_value_le_factorized
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) {u : Finset (Index J noiseDim)} (hu : u.Nonempty)
    {m : ℕ} (hm : m ≤ numSteps J) (timedTree : TimedPayoffTree J noiseDim u m) :
    Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
        ‖timedTree.value drift payoff diffusion T x₀ z‖ ≤
      stepSize T J ^
          (timedTree.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timedTree.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timedTree.tree.data
          timedTree.assignment := by
  calc
    Real.exp (-bounds.β * ‖stateNat drift diffusion T x₀ z m‖) *
        ‖timedTree.value drift payoff diffusion T x₀ z‖ ≤
      payoffTreeMajorant bounds diffusion timedTree.tree.data timedTree.assignment :=
        TimedPayoffTree.normalized_norm_value_le_majorant
          bounds hT diffusion x₀ z hu hm timedTree
    _ = _ := payoffTreeMajorant_eq_factorized bounds diffusion timedTree.tree.data
      timedTree.assignment m timedTree.assignmentValid

theorem drift_apply_le
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht₀ : 0 ≤ t) (htT : t ≤ T)
    (x : State stateDim) (directions : Fin n → State stateDim) :
    ‖iteratedFDeriv ℝ n (drift t) x directions‖ ≤
      (bounds.B₀ * bounds.B₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        ∏ i, ‖directions i‖ := by
  exact ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
    (bounds.drift_derivative_norm n hn t ht₀ htT x) (fun _ => le_rfl)

theorem payoff_apply_normalized_le
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T)
    (n : ℕ) (hn : 1 ≤ n) (x : State stateDim)
    (directions : Fin n → State stateDim) :
    Real.exp (-bounds.β * ‖x‖) *
        ‖iteratedFDeriv ℝ n payoff x directions‖ ≤
      (bounds.G₀ * bounds.G₁ ^ n * (n.factorial : ℝ) ^ bounds.τ) *
        ∏ i, ‖directions i‖ := by
  have happly :
      ‖iteratedFDeriv ℝ n payoff x directions‖ ≤
        (bounds.G₀ * bounds.G₁ ^ n *
            (n.factorial : ℝ) ^ bounds.τ * Real.exp (bounds.β * ‖x‖)) *
          ∏ i, ‖directions i‖ :=
    ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
      (bounds.payoff_derivative_norm n hn x) (fun _ => le_rfl)
  have hexpNonneg : 0 ≤ Real.exp (-bounds.β * ‖x‖) := (Real.exp_pos _).le
  calc
    Real.exp (-bounds.β * ‖x‖) *
        ‖iteratedFDeriv ℝ n payoff x directions‖ ≤
      Real.exp (-bounds.β * ‖x‖) *
        ((bounds.G₀ * bounds.G₁ ^ n *
            (n.factorial : ℝ) ^ bounds.τ * Real.exp (bounds.β * ‖x‖)) *
          ∏ i, ‖directions i‖) :=
      mul_le_mul_of_nonneg_left happly hexpNonneg
    _ = (bounds.G₀ * bounds.G₁ ^ n *
          (n.factorial : ℝ) ^ bounds.τ) *
        ∏ i, ‖directions i‖ := by
      have hexpCancel :
          Real.exp (-bounds.β * ‖x‖) * Real.exp (bounds.β * ‖x‖) = 1 := by
        rw [← Real.exp_add]
        have : -bounds.β * ‖x‖ + bounds.β * ‖x‖ = 0 := by ring
        rw [this, Real.exp_zero]
      calc
        _ = (bounds.G₀ * bounds.G₁ ^ n *
              (n.factorial : ℝ) ^ bounds.τ) *
            (Real.exp (-bounds.β * ‖x‖) * Real.exp (bounds.β * ‖x‖)) *
              ∏ i, ‖directions i‖ := by ring
        _ = _ := by rw [hexpCancel, mul_one]

end GevreyBounds

end

end TimeDependentLattice.Trees
