/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.Constants
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Coupled Euler paths and the exact error identity

The stochastic input is the integral equation for the exact solution driven by the same
additive noise as the Euler chain. Subtracting the two equations and telescoping are proved
here; neither the scalar error recurrence nor an Euler convergence bound is assumed.

Unlike `Euler.stateNat`, which takes finite Brownian-bridge coordinates, `coupledEulerChain`
takes an arbitrary additive noise path. This is the coupled continuous-time representation
used in Appendix E. The Brownian law is needed only by the stochastic input estimates.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators
open MeasureTheory TimeDependentLattice.Euler

/-- Euler--Maruyama driven by an additive path, at a prescribed uniform grid. -/
def coupledEulerChain {Ω : Type*} {stateDim : ℕ}
    (drift : Drift stateDim) (grid : ℕ → ℝ) (h : ℝ) (x₀ : State stateDim)
    (noise : ℝ → Ω → State stateDim) : ℕ → Ω → State stateDim
  | 0, _ => x₀
  | i + 1, ω =>
      coupledEulerChain drift grid h x₀ noise i ω +
        h • drift (grid i) (coupledEulerChain drift grid h x₀ noise i ω) +
          (noise (grid (i + 1)) ω - noise (grid i) ω)

/-- The actual one-step time integral of the drift increment along the exact solution. -/
def localDriftRemainder {Ω : Type*} {stateDim : ℕ}
    (drift : Drift stateDim) (X : ℝ → Ω → State stateDim)
    (grid : ℕ → ℝ) (i : ℕ) (ω : Ω) : State stateDim :=
  ∫ s in grid i..grid (i + 1), drift s (X s ω) - drift (grid i) (X (grid i) ω)

/-- The space Lipschitz estimate follows from the first derivative bound in Assumption 2.1. -/
theorem drift_lipschitz_of_gevrey
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : Trees.GevreyBounds drift payoff T)
    {t : ℝ} (ht₀ : 0 ≤ t) (htT : t ≤ T) (x y : State stateDim) :
    ‖drift t x - drift t y‖ ≤ bounds.driftLipschitzConstant * ‖x - y‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (x := y) (y := x)
    (fun z _ ↦ (bounds.drift_smooth t).differentiable (by simp) z)
    (fun z _ ↦ ?_) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  rw [← norm_iteratedFDeriv_one]
  simpa [Trees.GevreyBounds.driftLipschitzConstant] using
    bounds.drift_derivative_norm 1 (by omega) t ht₀ htT z

/-- The SDE integral equation and the defining Euler recursion imply the actual vector
error recurrence. The common additive noise cancels algebraically. -/
theorem coupledEuler_error_step
    {Ω : Type*} {stateDim : ℕ}
    (drift : Drift stateDim) (grid : ℕ → ℝ) (h : ℝ) (x₀ : State stateDim)
    (noise X : ℝ → Ω → State stateDim) (i : ℕ) (ω : Ω)
    (hgrid : grid (i + 1) - grid i = h)
    (hint : IntervalIntegrable (fun s ↦ drift s (X s ω)) volume (grid i) (grid (i + 1)))
    (hsolution : X (grid (i + 1)) ω = X (grid i) ω +
      (∫ s in grid i..grid (i + 1), drift s (X s ω)) +
        (noise (grid (i + 1)) ω - noise (grid i) ω)) :
    X (grid (i + 1)) ω - coupledEulerChain drift grid h x₀ noise (i + 1) ω =
      (X (grid i) ω - coupledEulerChain drift grid h x₀ noise i ω) +
        h • (drift (grid i) (X (grid i) ω) -
          drift (grid i) (coupledEulerChain drift grid h x₀ noise i ω)) +
            localDriftRemainder drift X grid i ω := by
  have hrem : localDriftRemainder drift X grid i ω =
      (∫ s in grid i..grid (i + 1), drift s (X s ω)) -
        h • drift (grid i) (X (grid i) ω) := by
    unfold localDriftRemainder
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, hgrid]
  rw [hsolution, coupledEulerChain, hrem, smul_sub]
  abel

/-- Telescoping the vector recurrence gives the unnumbered error identity preceding (E.9).
The same identity is the sum of (E.10) in the order-one proof. -/
theorem coupledEuler_error_eq_sum
    {Ω : Type*} {stateDim : ℕ} {m : ℕ}
    (drift : Drift stateDim) (grid : ℕ → ℝ) (h : ℝ) (x₀ : State stateDim)
    (noise X : ℝ → Ω → State stateDim) (ω : Ω)
    (hgrid : ∀ i < m, grid (i + 1) - grid i = h)
    (hint : ∀ i < m,
      IntervalIntegrable (fun s ↦ drift s (X s ω)) volume (grid i) (grid (i + 1)))
    (hzero : X (grid 0) ω = x₀)
    (hsolution : ∀ i < m, X (grid (i + 1)) ω = X (grid i) ω +
      (∫ s in grid i..grid (i + 1), drift s (X s ω)) +
        (noise (grid (i + 1)) ω - noise (grid i) ω))
    {j : ℕ} (hj : j ≤ m) :
    X (grid j) ω - coupledEulerChain drift grid h x₀ noise j ω =
      h • (∑ i ∈ Finset.range j,
        (drift (grid i) (X (grid i) ω) -
          drift (grid i) (coupledEulerChain drift grid h x₀ noise i ω))) +
        ∑ i ∈ Finset.range j, localDriftRemainder drift X grid i ω := by
  induction j with
  | zero => simp [coupledEulerChain, hzero]
  | succ j ih =>
      have hjm : j < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      rw [coupledEuler_error_step drift grid h x₀ noise X j ω
        (hgrid j hjm) (hint j hjm) (hsolution j hjm)]
      rw [ih (Nat.le_of_succ_le hj), Finset.sum_range_succ, Finset.sum_range_succ,
        smul_add]
      abel

/-- Almost-everywhere form of the error identity, matching the SDE integral equation. -/
theorem coupledEuler_error_eq_sum_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {stateDim m : ℕ}
    (drift : Drift stateDim) (grid : ℕ → ℝ) (h : ℝ) (x₀ : State stateDim)
    (noise X : ℝ → Ω → State stateDim)
    (hgrid : ∀ i < m, grid (i + 1) - grid i = h)
    (hint : ∀ᵐ ω ∂μ, ∀ i < m,
      IntervalIntegrable (fun s ↦ drift s (X s ω)) volume (grid i) (grid (i + 1)))
    (hzero : ∀ᵐ ω ∂μ, X (grid 0) ω = x₀)
    (hsolution : ∀ᵐ ω ∂μ, ∀ i < m, X (grid (i + 1)) ω = X (grid i) ω +
      (∫ s in grid i..grid (i + 1), drift s (X s ω)) +
        (noise (grid (i + 1)) ω - noise (grid i) ω)) :
    ∀ᵐ ω ∂μ, ∀ j ≤ m,
      X (grid j) ω - coupledEulerChain drift grid h x₀ noise j ω =
        h • (∑ i ∈ Finset.range j,
          (drift (grid i) (X (grid i) ω) -
            drift (grid i) (coupledEulerChain drift grid h x₀ noise i ω))) +
          ∑ i ∈ Finset.range j, localDriftRemainder drift X grid i ω := by
  filter_upwards [hint, hzero, hsolution] with ω hintω hzeroω hsolutionω
  intro j hj
  exact coupledEuler_error_eq_sum drift grid h x₀ noise X ω hgrid hintω hzeroω
    hsolutionω hj

/-- The coupled Euler chain specializes to the existing Brownian-bridge Euler recursion.
This is a deterministic identity and requires no new distributional assumption. -/
theorem coupledEulerChain_eq_stateNat
    {Ω : Type*} {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Ω → BrownianBridge.Input J noiseDim) (i : ℕ) (ω : Ω) :
    coupledEulerChain drift (BrownianBridge.gridTime T J) (BrownianBridge.stepSize T J)
        x₀ (fun t ω ↦ BrownianBridge.diffusedPath diffusion T (z ω) t) i ω =
      stateNat drift diffusion T x₀ (z ω) i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [coupledEulerChain, stateNat_succ, ih]

/-- Only the noise values at the Euler grid affect the chain. The exact SDE may therefore
retain its Brownian path between grid points when the Euler chain is identified with a
Brownian-bridge representation on the grid. -/
theorem coupledEulerChain_eq_of_noise_eq_on_grid
    {Ω : Type*} {stateDim m : ℕ}
    (drift : Drift stateDim) (grid : ℕ → ℝ) (h : ℝ) (x₀ : State stateDim)
    (noise noise' : ℝ → Ω → State stateDim) (ω : Ω)
    (hnoise : ∀ i ≤ m, noise (grid i) ω = noise' (grid i) ω)
    {j : ℕ} (hj : j ≤ m) :
    coupledEulerChain drift grid h x₀ noise j ω =
      coupledEulerChain drift grid h x₀ noise' j ω := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [coupledEulerChain, ih (Nat.le_of_succ_le hj),
        hnoise (j + 1) hj, hnoise j (Nat.le_of_succ_le hj)]

end

end TimeDependentLattice.Bias
