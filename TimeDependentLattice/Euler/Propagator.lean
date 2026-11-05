/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import TimeDependentLattice.Euler.Derivatives

/-!
# Discrete propagators and the first state-derivative expansion

This file defines the Jacobians `J_i` and propagators `P_{i,r}` from Lemma
`lem:state-expansion`.  A general discrete Duhamel identity is proved first and then applied to
the singleton-coordinate derivative recurrence.
-/

namespace TimeDependentLattice.Euler

noncomputable section

open scoped BigOperators ContDiff
open TimeDependentLattice.Analysis
open TimeDependentLattice.BrownianBridge

/-- For a sequence of endomorphisms, `propagator jacobian i r` is the ordered product from just
after `r` through just before `i`.  In particular, `P_{r+1,r}` is the identity. -/
def propagator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (jacobian : ℕ → E →L[ℝ] E) : ℕ → ℕ → E →L[ℝ] E
  | 0, _ => ContinuousLinearMap.id ℝ E
  | i + 1, r => if r < i then (jacobian i).comp (propagator jacobian i r)
      else ContinuousLinearMap.id ℝ E

@[simp]
theorem propagator_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (jacobian : ℕ → E →L[ℝ] E) (r : ℕ) :
    propagator jacobian 0 r = ContinuousLinearMap.id ℝ E := by
  rfl

@[simp]
theorem propagator_succ_of_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (jacobian : ℕ → E →L[ℝ] E) {i r : ℕ} (hr : r < i) :
    propagator jacobian (i + 1) r =
      (jacobian i).comp (propagator jacobian i r) := by
  simp [propagator, hr]

@[simp]
theorem propagator_succ_self {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (jacobian : ℕ → E →L[ℝ] E) (i : ℕ) :
    propagator jacobian (i + 1) i = ContinuousLinearMap.id ℝ E := by
  simp [propagator]

/-- Discrete variation of constants for an inhomogeneous linear recurrence. -/
theorem discrete_duhamel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (jacobian : ℕ → E →L[ℝ] E) (forcing state : ℕ → E)
    (hzero : state 0 = 0)
    (hrec : ∀ i, state (i + 1) = jacobian i (state i) + forcing i) :
    ∀ i, state i = ∑ r ∈ Finset.range i, propagator jacobian i r (forcing r) := by
  intro i
  induction i with
  | zero => simpa using hzero
  | succ i ih =>
      rw [hrec, ih, Finset.sum_range_succ]
      rw [map_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro r hr
        rw [propagator_succ_of_lt jacobian (Finset.mem_range.mp hr)]
        rfl
      · simp

/-- The Euler Jacobian `J_i = Id + h D b(t_i, X_i)`. -/
def stepJacobian {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (i : ℕ) : State stateDim →L[ℝ] State stateDim :=
  ContinuousLinearMap.id ℝ (State stateDim) +
    stepSize T J • fderiv ℝ (drift (gridTime T J i))
      (eulerDriftInput drift diffusion T x₀ i z)

/-- The inhomogeneous forcing in the singleton-coordinate derivative recurrence. -/
def coordinateForcing {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (i : ℕ) (j : Index J noiseDim) : State stateDim :=
  stepSize T J •
    (fderiv ℝ (drift (gridTime T J i))
      (eulerDriftInput drift diffusion T x₀ i z))
      (diffusionCoefficient diffusion T j (gridTime T J i))

/-- Every compensated coordinate derivative starts at zero. -/
theorem compensatedStateCoordinateDerivative_zero {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (j : Index J noiseDim) :
    compensatedStateCoordinateDerivative drift diffusion T x₀ 0 j z = 0 := by
  unfold compensatedStateCoordinateDerivative coordinateDerivative
  have hfun : (fun y : Input J noiseDim ↦ compensatedStateNat drift diffusion T x₀ y 0) =
      fun _ ↦ x₀ := by
    funext y
    simp
  rw [hfun]
  simp

/-- The first derivative recurrence in `J_i Y_i + q_i` form. -/
theorem compensatedStateCoordinateDerivative_succ_eq_jacobian
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (i : ℕ) (j : Index J noiseDim) :
    compensatedStateCoordinateDerivative drift diffusion T x₀ (i + 1) j z =
      stepJacobian drift diffusion T x₀ z i
        (compensatedStateCoordinateDerivative drift diffusion T x₀ i j z) +
      coordinateForcing drift diffusion T x₀ z i j := by
  rw [compensatedStateCoordinateDerivative_succ_of_contDiff
    drift diffusion T x₀ hDrift z i j]
  simp [stepJacobian, coordinateForcing, eulerDriftInput, map_add, smul_add]
  abel

/-- Equation `eq:partition-first`: the singleton-coordinate state derivative is the propagated
sum of all earlier bridge forcings. -/
theorem compensatedStateCoordinateDerivative_eq_sum_propagator
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (i : ℕ) (j : Index J noiseDim) :
    compensatedStateCoordinateDerivative drift diffusion T x₀ i j z =
      ∑ r ∈ Finset.range i,
        propagator (stepJacobian drift diffusion T x₀ z) i r
          (coordinateForcing drift diffusion T x₀ z r j) := by
  exact discrete_duhamel
    (stepJacobian drift diffusion T x₀ z)
    (fun r ↦ coordinateForcing drift diffusion T x₀ z r j)
    (fun n ↦ compensatedStateCoordinateDerivative drift diffusion T x₀ n j z)
    (compensatedStateCoordinateDerivative_zero drift diffusion T x₀ z j)
    (fun n ↦ compensatedStateCoordinateDerivative_succ_eq_jacobian
      drift diffusion T x₀ hDrift z n j) i

/-- The nonlinear part of the one-step recurrence for a mixed state derivative.  The
subtracted first-derivative term is the contribution absorbed into `stepJacobian`. -/
def nonlinearStateForcing {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    (i : ℕ) (u : Finset (Index J noiseDim)) : State stateDim :=
  stepSize T J •
      ∑ c : OrderedFinpartition u.card,
        partitionChainTerm (drift (gridTime T J i))
          (eulerDriftInput drift diffusion T x₀ i) u c z -
    stepSize T J •
      (fderiv ℝ (drift (gridTime T J i))
        (eulerDriftInput drift diffusion T x₀ i z))
        (compensatedStateDerivative drift diffusion T x₀ i u z)

/-- Every nonempty compensated mixed state derivative starts at zero. -/
theorem compensatedStateDerivative_zero {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    (u : Finset (Index J noiseDim)) (hu : u.Nonempty) :
    compensatedStateDerivative drift diffusion T x₀ 0 u z = 0 := by
  unfold compensatedStateDerivative mixedDerivative
  have hcard : u.card ≠ 0 := Finset.card_ne_zero.mpr hu
  have hfun :
      (fun y : Input J noiseDim ↦ compensatedStateNat drift diffusion T x₀ y 0) =
        fun _ ↦ x₀ := by
    funext y
    simp
  rw [hfun]
  rw [iteratedFDeriv_const_of_ne hcard]
  rfl

/-- The general mixed-derivative recurrence in `J_i Y_i + q_i` form. -/
theorem compensatedStateDerivative_succ_eq_jacobian
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (i : ℕ) (u : Finset (Index J noiseDim)) :
    compensatedStateDerivative drift diffusion T x₀ (i + 1) u z =
      stepJacobian drift diffusion T x₀ z i
          (compensatedStateDerivative drift diffusion T x₀ i u z) +
        nonlinearStateForcing drift diffusion T x₀ z i u := by
  rw [compensatedStateDerivative_succ_of_contDiff
    drift diffusion T x₀ hDrift z i u]
  simp only [stepJacobian, nonlinearStateForcing, add_apply,
    ContinuousLinearMap.id_apply, smul_apply]
  abel

/-- Discrete Duhamel formula for every nonempty mixed state derivative. The direct-set and
partition reindexing is developed in `Trees/LocalExpansion.lean` and used in the final
tree expansion of `Trees/DerivativeExpansion.lean`. -/
theorem compensatedStateDerivative_eq_sum_nonlinearForcing
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (parentTime : ℕ)
    (u : Finset (Index J noiseDim)) (hu : u.Nonempty) :
    compensatedStateDerivative drift diffusion T x₀ parentTime u z =
      ∑ r ∈ Finset.range parentTime,
        propagator (stepJacobian drift diffusion T x₀ z) parentTime r
          (nonlinearStateForcing drift diffusion T x₀ z r u) := by
  exact discrete_duhamel
    (stepJacobian drift diffusion T x₀ z)
    (fun r ↦ nonlinearStateForcing drift diffusion T x₀ z r u)
    (fun n ↦ compensatedStateDerivative drift diffusion T x₀ n u z)
    (compensatedStateDerivative_zero drift diffusion T x₀ z u hu)
    (fun n ↦ compensatedStateDerivative_succ_eq_jacobian
      drift diffusion T x₀ hDrift z n u) parentTime

end

end TimeDependentLattice.Euler
