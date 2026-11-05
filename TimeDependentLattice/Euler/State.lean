/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.BrownianBridge.Path

/-!
# The deterministic Euler integrand

For a fixed Brownian-bridge input `z`, this file defines the Euler recursion from
Equation `eq:bb-em`, its terminal value, and the integrand `F_m`.  It also defines the compensated
state `Y_i = X_i - Σ W_{t_i}` and proves Equation `eq:Y`, which is the starting point for the
mixed-derivative and tree expansions.
-/

namespace TimeDependentLattice.Euler

noncomputable section

open TimeDependentLattice.BrownianBridge

/-- A time-dependent drift on the finite-dimensional state space. -/
abbrev Drift (stateDim : ℕ) := ℝ → State stateDim → State stateDim

/-- A real-valued payoff on the state space. -/
abbrev Payoff (stateDim : ℕ) := State stateDim → ℝ

/-- The Euler state after `i` steps, extended recursively to every natural number.

The paper only uses indices `i ≤ numSteps J`; defining the recursion on all natural numbers keeps
the computational equation simple and lets bounded grid indices be added at the API boundary. -/
def stateNat {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) : ℕ → State stateDim
  | 0 => x₀
  | i + 1 =>
      let previous := stateNat drift diffusion T x₀ z i
      previous + stepSize T J • drift (gridTime T J i) previous +
        (diffusedPath diffusion T z (gridTime T J (i + 1)) -
          diffusedPath diffusion T z (gridTime T J i))

@[simp]
theorem stateNat_zero {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) : stateNat drift diffusion T x₀ z 0 = x₀ := rfl

/-- The defining one-step Euler recursion. -/
theorem stateNat_succ {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (i : ℕ) :
    stateNat drift diffusion T x₀ z (i + 1) =
      stateNat drift diffusion T x₀ z i +
        stepSize T J • drift (gridTime T J i) (stateNat drift diffusion T x₀ z i) +
        (diffusedPath diffusion T z (gridTime T J (i + 1)) -
          diffusedPath diffusion T z (gridTime T J i)) := rfl

/-- The Euler state at a valid grid index `0 ≤ i ≤ 2^J`. -/
def state {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (i : Fin (numSteps J + 1)) : State stateDim :=
  stateNat drift diffusion T x₀ z i.val

/-- The Euler terminal state `X^h_T(z)`. -/
def terminalState {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) : State stateDim :=
  stateNat drift diffusion T x₀ z (numSteps J)

/-- The deterministic Euler integrand `F_m(z) = g(X^h_T(z))`. -/
def integrand {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (payoff : Payoff stateDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) : ℝ :=
  payoff (terminalState drift diffusion T x₀ z)

/-- The compensated state `Y_i = X_i - Σ W_{t_i}` used in the derivative recursion. -/
def compensatedStateNat {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (i : ℕ) : State stateDim :=
  stateNat drift diffusion T x₀ z i - diffusedPath diffusion T z (gridTime T J i)

@[simp]
theorem compensatedStateNat_zero {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) : compensatedStateNat drift diffusion T x₀ z 0 = x₀ := by
  simp [compensatedStateNat, diffusedPath, path]

/-- Equation `eq:Y`: compensation removes the additive bridge increment from the recursion. -/
theorem compensatedStateNat_succ {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (i : ℕ) :
    compensatedStateNat drift diffusion T x₀ z (i + 1) =
      compensatedStateNat drift diffusion T x₀ z i +
        stepSize T J •
          drift (gridTime T J i)
            (compensatedStateNat drift diffusion T x₀ z i +
              diffusedPath diffusion T z (gridTime T J i)) := by
  rw [compensatedStateNat, stateNat_succ]
  have hdecompose :
      stateNat drift diffusion T x₀ z i =
        compensatedStateNat drift diffusion T x₀ z i +
          diffusedPath diffusion T z (gridTime T J i) := by
    simp [compensatedStateNat]
  rw [hdecompose]
  abel

end

end TimeDependentLattice.Euler
