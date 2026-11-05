/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.ODE.DiscreteGronwall
import TimeDependentLattice.Euler.State

/-!
# Deterministic growth bounds for the Euler recursion

This file isolates the deterministic part of the proof of paper Lemma 5.1.  The Euler
recursion is first written as a drift sum plus the Brownian-bridge path.  A discrete
Gronwall estimate then bounds the state by the size of that path.
-/

namespace TimeDependentLattice.Euler

noncomputable section

open scoped BigOperators
open TimeDependentLattice.BrownianBridge

/-- A constant-coefficient version of discrete Gronwall for inequalities containing the
sum over all preceding indices.  This is an auxiliary formalization lemma. -/
theorem discrete_sum_gronwall
    {u : ℕ → ℝ} {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (huNonneg : ∀ m, 0 ≤ u m) {n : ℕ}
    (hu : ∀ m ≤ n, u m ≤ A + c * ∑ k ∈ Finset.range m, u k) :
    u n ≤ A * Real.exp (c * n) := by
  let w : ℕ → ℝ := fun m => if m ≤ n then u m else 0
  let v : ℕ → ℝ := fun m => A + c * ∑ k ∈ Finset.range m, w k
  have hv0 : v 0 = A := by simp [v]
  have hvnonneg0 : 0 ≤ v 0 := by simpa [hv0] using hA
  have hw_le_v : ∀ m, w m ≤ v m := by
    intro m
    by_cases hm : m ≤ n
    · have hsum : (∑ k ∈ Finset.range m, w k) = ∑ k ∈ Finset.range m, u k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hm]
      simpa [w, hm, v, hsum] using hu m hm
    · have hw : w m = 0 := by simp [w, hm]
      rw [hw]
      exact add_nonneg hA (mul_nonneg hc (Finset.sum_nonneg (fun k _ => by
        simp only [w]
        split
        · exact huNonneg k
        · exact le_rfl)))
  have hvstep : ∀ m, v (m + 1) ≤ (1 + c) * v m + 0 := by
    intro m
    have hwm : w m ≤ v m := hw_le_v m
    dsimp [v]
    rw [Finset.sum_range_succ]
    calc
      A + c * (∑ k ∈ Finset.range m, w k + w m) =
          (A + c * ∑ k ∈ Finset.range m, w k) + c * w m := by ring
      _ ≤ (A + c * ∑ k ∈ Finset.range m, w k) +
          c * (A + c * ∑ k ∈ Finset.range m, w k) := by gcongr
      _ = (1 + c) * (A + c * ∑ k ∈ Finset.range m, w k) + 0 := by ring
  have hvbound : v n ≤ v 0 * Real.exp (∑ _i ∈ Finset.Ico 0 n, c) := by
    simpa using
      (discrete_gronwall hvnonneg0 (fun m _ => hvstep m)
        (fun _ _ => hc) (fun _ _ => le_rfl) (Nat.zero_le n))
  calc
    u n = w n := by simp [w]
    _ ≤ v n := hw_le_v n
    _ ≤ v 0 * Real.exp (∑ _i ∈ Finset.Ico 0 n, c) := hvbound
    _ = A * Real.exp (c * n) := by
      rw [hv0]
      simp [mul_comm]

/-- The Euler recursion telescopes into the initial value, the drift sum, and the
diffused Brownian-bridge path at the current grid time. -/
theorem stateNat_eq_initial_add_driftSum_add_diffusedPath
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (i : ℕ) :
    stateNat drift diffusion T x₀ z i =
      x₀ + ∑ k ∈ Finset.range i,
        stepSize T J • drift (gridTime T J k)
          (stateNat drift diffusion T x₀ z k) +
        diffusedPath diffusion T z (gridTime T J i) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [stateNat_succ]
      nth_rewrite 1 [ih]
      rw [Finset.sum_range_succ]
      abel

/-- Deterministic Euler growth estimate used in Lemma 5.1.

The hypotheses are precisely the linear-growth estimate for the drift and a bound on the
diffused path at each grid point.  The conclusion is uniform over the grid index and keeps
the paper's constants `K₀`, `L`, and `P` explicit. -/
theorem stateNat_norm_le_exp_of_linearGrowth
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) {T K₀ L P : ℝ}
    (x₀ : State stateDim) (z : Input J noiseDim)
    (hT : 0 ≤ T) (hK₀ : 0 ≤ K₀) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (hdrift : ∀ i < numSteps J,
      ‖drift (gridTime T J i) (stateNat drift diffusion T x₀ z i)‖ ≤
        K₀ + L * ‖stateNat drift diffusion T x₀ z i‖)
    (hpath : ∀ i ≤ numSteps J,
      ‖diffusedPath diffusion T z (gridTime T J i)‖ ≤ P)
    {i : ℕ} (hi : i ≤ numSteps J) :
    ‖stateNat drift diffusion T x₀ z i‖ ≤
      (‖x₀‖ + K₀ * T + P) * Real.exp (L * T) := by
  let A : ℝ := ‖x₀‖ + K₀ * T + P
  let c : ℝ := stepSize T J * L
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hc : 0 ≤ c := mul_nonneg (stepSize_nonneg hT J) hL
  have hrec : ∀ n, n ≤ numSteps J →
      ‖stateNat drift diffusion T x₀ z n‖ ≤
        A + c * ∑ k ∈ Finset.range n,
          ‖stateNat drift diffusion T x₀ z k‖ := by
    intro n hn
    rw [stateNat_eq_initial_add_driftSum_add_diffusedPath]
    calc
      ‖x₀ + ∑ k ∈ Finset.range n,
          stepSize T J • drift (gridTime T J k)
            (stateNat drift diffusion T x₀ z k) +
          diffusedPath diffusion T z (gridTime T J n)‖
          ≤ ‖x₀‖ +
              ‖∑ k ∈ Finset.range n,
                stepSize T J • drift (gridTime T J k)
                  (stateNat drift diffusion T x₀ z k)‖ +
              ‖diffusedPath diffusion T z (gridTime T J n)‖ := by
            calc
              _ ≤ ‖x₀ + ∑ k ∈ Finset.range n,
                  stepSize T J • drift (gridTime T J k)
                    (stateNat drift diffusion T x₀ z k)‖ +
                    ‖diffusedPath diffusion T z (gridTime T J n)‖ := norm_add_le _ _
              _ ≤ (‖x₀‖ + ‖∑ k ∈ Finset.range n,
                    stepSize T J • drift (gridTime T J k)
                      (stateNat drift diffusion T x₀ z k)‖) +
                    ‖diffusedPath diffusion T z (gridTime T J n)‖ := by
                  gcongr
                  exact norm_add_le _ _
      _ ≤ ‖x₀‖ +
              ∑ k ∈ Finset.range n,
                stepSize T J *
                  (K₀ + L * ‖stateNat drift diffusion T x₀ z k‖) + P := by
            gcongr
            · calc
                ‖∑ k ∈ Finset.range n,
                    stepSize T J • drift (gridTime T J k)
                      (stateNat drift diffusion T x₀ z k)‖
                    ≤ ∑ k ∈ Finset.range n,
                        ‖stepSize T J • drift (gridTime T J k)
                          (stateNat drift diffusion T x₀ z k)‖ := norm_sum_le _ _
                _ = ∑ k ∈ Finset.range n,
                      stepSize T J *
                        ‖drift (gridTime T J k)
                          (stateNat drift diffusion T x₀ z k)‖ := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (stepSize_nonneg hT J)]
                _ ≤ ∑ k ∈ Finset.range n,
                      stepSize T J *
                        (K₀ + L * ‖stateNat drift diffusion T x₀ z k‖) := by
                      apply Finset.sum_le_sum
                      intro k hk
                      exact mul_le_mul_of_nonneg_left
                        (hdrift k (lt_of_lt_of_le (Finset.mem_range.mp hk) hn))
                        (stepSize_nonneg hT J)
            · exact hpath n hn
      _ ≤ A + c * ∑ k ∈ Finset.range n,
              ‖stateNat drift diffusion T x₀ z k‖ := by
            have hgrid : (n : ℝ) * stepSize T J ≤ T := by
              simpa [gridTime] using gridTime_le_terminal hT J hn
            have hconstant :
                (∑ _k ∈ Finset.range n, stepSize T J * K₀) ≤ T * K₀ := by
              calc
                (∑ _k ∈ Finset.range n, stepSize T J * K₀) =
                    ((n : ℝ) * stepSize T J) * K₀ := by simp; ring
                _ ≤ T * K₀ := mul_le_mul_of_nonneg_right hgrid hK₀
            have hsplit :
                (∑ k ∈ Finset.range n,
                    stepSize T J * (K₀ + L * ‖stateNat drift diffusion T x₀ z k‖)) =
                  (∑ _k ∈ Finset.range n, stepSize T J * K₀) +
                    ∑ k ∈ Finset.range n,
                      stepSize T J * (L * ‖stateNat drift diffusion T x₀ z k‖) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              ring
            dsimp [A, c]
            rw [hsplit]
            calc
              ‖x₀‖ +
                    ((∑ _k ∈ Finset.range n, stepSize T J * K₀) +
                      ∑ k ∈ Finset.range n,
                        stepSize T J * (L * ‖stateNat drift diffusion T x₀ z k‖)) + P
                  ≤ ‖x₀‖ +
                    (T * K₀ + ∑ k ∈ Finset.range n,
                      stepSize T J * (L * ‖stateNat drift diffusion T x₀ z k‖)) + P := by
                    gcongr
              _ = ‖x₀‖ + K₀ * T + P +
                    stepSize T J * L *
                      ∑ k ∈ Finset.range n,
                        ‖stateNat drift diffusion T x₀ z k‖ := by
                    rw [Finset.mul_sum]
                    ring_nf
  have hgronwall := discrete_sum_gronwall hA hc
    (fun n => norm_nonneg (stateNat drift diffusion T x₀ z n))
    (fun n hn => hrec n (le_trans hn hi))
  calc
    ‖stateNat drift diffusion T x₀ z i‖ ≤ A * Real.exp (c * i) := hgronwall
    _ ≤ A * Real.exp (L * T) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.exp_le_exp.mpr
      have hgrid : (i : ℝ) * stepSize T J ≤ T := by
        simpa [gridTime] using gridTime_le_terminal hT J hi
      dsimp [c]
      nlinarith

end

end TimeDependentLattice.Euler
