/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TimeDependentLattice.Analysis.MixedDerivative
import TimeDependentLattice.Euler.State

/-!
# Coordinate derivatives of the Euler state

This file introduces the derivative objects used in Lemma `lem:state-expansion`.  The first
verified facts identify the derivative of the linear Brownian-bridge forcing with the vector
coefficient `ξ_j(t)`.
-/

namespace TimeDependentLattice.Euler

noncomputable section

open scoped ContDiff
open TimeDependentLattice.Analysis
open TimeDependentLattice.BrownianBridge

/-- The mixed coordinate derivative `∂_u X_i(z)` of the Euler state. -/
def stateDerivative {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (i : ℕ) (u : Finset (Index J noiseDim)) (z : Input J noiseDim) : State stateDim :=
  mixedDerivative (fun z ↦ stateNat drift diffusion T x₀ z i) u z

/-- The mixed coordinate derivative `Y_{i,u} = ∂_u Y_i(z)` of the compensated state. -/
def compensatedStateDerivative {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (i : ℕ) (u : Finset (Index J noiseDim)) (z : Input J noiseDim) : State stateDim :=
  mixedDerivative (fun z ↦ compensatedStateNat drift diffusion T x₀ z i) u z

/-- The state seen by the drift at step `i`, written as compensated state plus bridge forcing. -/
def eulerDriftInput {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (i : ℕ) (z : Input J noiseDim) : State stateDim :=
  compensatedStateNat drift diffusion T x₀ z i +
    diffusedPath diffusion T z (gridTime T J i)

/-- The compensated representation of the drift input is exactly the Euler state. -/
theorem eulerDriftInput_eq_stateNat {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (i : ℕ) (z : Input J noiseDim) :
    eulerDriftInput drift diffusion T x₀ i z =
      stateNat drift diffusion T x₀ z i := by
  simp [eulerDriftInput, compensatedStateNat]

/-- The Euler state is the compensated state plus the linear bridge forcing. -/
theorem stateNat_eq_compensatedStateNat_add {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (i : ℕ) (z : Input J noiseDim) :
    stateNat drift diffusion T x₀ z i =
      compensatedStateNat drift diffusion T x₀ z i +
        diffusedPath diffusion T z (gridTime T J i) := by
  simp [compensatedStateNat]

/-- The first coordinate derivative `∂_j X_i(z)`. -/
def stateCoordinateDerivative {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (i : ℕ) (j : Index J noiseDim) (z : Input J noiseDim) : State stateDim :=
  coordinateDerivative (fun z ↦ stateNat drift diffusion T x₀ z i) j z

/-- The first coordinate derivative `Y_{i,{j}} = ∂_j Y_i(z)`. -/
def compensatedStateCoordinateDerivative {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (i : ℕ) (j : Index J noiseDim) (z : Input J noiseDim) : State stateDim :=
  coordinateDerivative (fun z ↦ compensatedStateNat drift diffusion T x₀ z i) j z

/-- The Fréchet derivative of the diffused bridge path is its defining continuous linear map. -/
theorem fderiv_diffusedPath {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T t : ℝ) (z : Input J noiseDim) :
    fderiv ℝ (fun z ↦ diffusedPath diffusion T z t) z = diffusedPathLinear diffusion T t := by
  have hfun : (fun y : Input J noiseDim ↦ diffusedPath diffusion T y t) =
      (diffusedPathLinear (J := J) diffusion T t : Input J noiseDim → State stateDim) := by
    funext y
    exact (diffusedPathLinear_apply diffusion T t y).symm
  rw [hfun, ContinuousLinearMap.fderiv]

/-- Differentiating the bridge forcing in coordinate `j` produces `ξ_j(t)`. -/
theorem fderiv_diffusedPath_inputBasis {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T t : ℝ) (z : Input J noiseDim)
    (j : Index J noiseDim) :
    (fderiv ℝ (fun z ↦ diffusedPath diffusion T z t) z) (inputBasis j) =
      diffusionCoefficient diffusion T j t := by
  rw [fderiv_diffusedPath]
  cases j with
  | inl r =>
      simp [diffusedPathLinear, pathLinear, inputBasis, diffusionCoefficient, smul_smul]
  | inr j =>
      simp [diffusedPathLinear, pathLinear, inputBasis, diffusionCoefficient, smul_smul]

/-- The coordinate derivative of the bridge forcing is `ξ_j(t)`. -/
theorem coordinateDerivative_diffusedPath {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T t : ℝ) (z : Input J noiseDim)
    (j : Index J noiseDim) :
    coordinateDerivative (fun z ↦ diffusedPath diffusion T z t) j z =
      diffusionCoefficient diffusion T j t := by
  exact fderiv_diffusedPath_inputBasis diffusion T t z j

/-- The Brownian-bridge forcing is linear in the input, so every mixed derivative involving at
least two distinct input coordinates vanishes. -/
theorem mixedDerivative_diffusedPath_eq_zero {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T t : ℝ)
    (u : Finset (Index J noiseDim)) (hu : 2 ≤ u.card) (z : Input J noiseDim) :
    mixedDerivative (fun y ↦ diffusedPath diffusion T y t) u z = 0 := by
  have hfun : (fun y : Input J noiseDim ↦ diffusedPath diffusion T y t) =
      (diffusedPathLinear (J := J) diffusion T t : Input J noiseDim → State stateDim) := by
    funext y
    exact (diffusedPathLinear_apply diffusion T t y).symm
  rw [hfun]
  exact mixedDerivative_clm_eq_zero (diffusedPathLinear diffusion T t) u hu z

/-- The bridge contribution to a partition block of size at least two is zero. -/
theorem partitionDerivative_diffusedPath_eq_zero {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T t : ℝ)
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) (hi : 2 ≤ c.partSize i) (z : Input J noiseDim) :
    partitionDerivative (fun y ↦ diffusedPath diffusion T y t) u c i z = 0 := by
  have hfun : (fun y : Input J noiseDim ↦ diffusedPath diffusion T y t) =
      (diffusedPathLinear (J := J) diffusion T t : Input J noiseDim → State stateDim) := by
    funext y
    exact (diffusedPathLinear_apply diffusion T t y).symm
  rw [hfun]
  exact partitionDerivative_clm_eq_zero
    (diffusedPathLinear diffusion T t) u c i hi z

/-- A singleton partition block differentiates the bridge to its coefficient `ξ_j(t)`. -/
theorem partitionDerivative_diffusedPath_eq_coefficient
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T t : ℝ) (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) (hi : c.partSize i = 1) (z : Input J noiseDim) :
    partitionDerivative (fun y ↦ diffusedPath diffusion T y t) u c i z =
      diffusionCoefficient diffusion T (partitionCoordinate u c i hi) t := by
  have hfun : (fun y : Input J noiseDim ↦ diffusedPath diffusion T y t) =
      (diffusedPathLinear (J := J) diffusion T t : Input J noiseDim → State stateDim) := by
    funext y
    exact (diffusedPathLinear_apply diffusion T t y).symm
  rw [hfun, partitionDerivative_clm_eq_of_partSize_eq_one
    (diffusedPathLinear diffusion T t) u c i hi z]
  unfold partitionDirections partitionCoordinate
  have hcoefficient := fderiv_diffusedPath_inputBasis diffusion T t z
    (u.equivFin.symm (c.emb i (Fin.cast hi.symm 0))).val
  rw [fderiv_diffusedPath] at hcoefficient
  exact hcoefficient

/-- Smooth spatial drift implies smooth dependence of every compensated Euler state on the
finite Brownian-bridge input. -/
theorem contDiff_compensatedStateNat {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (i : ℕ) :
    ContDiff ℝ ∞ (fun z : Input J noiseDim ↦
      compensatedStateNat drift diffusion T x₀ z i) := by
  induction i with
  | zero =>
      have hfun :
          (fun z : Input J noiseDim ↦ compensatedStateNat drift diffusion T x₀ z 0) =
            fun _ ↦ x₀ := by
        funext z
        simp
      rw [hfun]
      exact contDiff_const
  | succ i inductionHypothesis =>
      have hbridge : ContDiff ℝ ∞
          (fun z : Input J noiseDim ↦ diffusedPath diffusion T z (gridTime T J i)) := by
        have hfun :
            (fun z : Input J noiseDim ↦ diffusedPath diffusion T z (gridTime T J i)) =
              (diffusedPathLinear (J := J) diffusion T (gridTime T J i) :
                Input J noiseDim → State stateDim) := by
          funext z
          exact (diffusedPathLinear_apply diffusion T (gridTime T J i) z).symm
        rw [hfun]
        exact (diffusedPathLinear (J := J) diffusion T (gridTime T J i)).contDiff
      have hinner := ContDiff.add inductionHypothesis hbridge
      have hcomposition := ContDiff.comp (hDrift (gridTime T J i)) hinner
      have hformula := ContDiff.add inductionHypothesis
        (ContDiff.const_smul (stepSize T J) hcomposition)
      have hrecursion :
          (fun z : Input J noiseDim ↦
            compensatedStateNat drift diffusion T x₀ z (i + 1)) =
          fun z ↦ compensatedStateNat drift diffusion T x₀ z i +
            stepSize T J • drift (gridTime T J i)
              (compensatedStateNat drift diffusion T x₀ z i +
                diffusedPath diffusion T z (gridTime T J i)) := by
        funext z
        exact compensatedStateNat_succ drift diffusion T x₀ z i
      rw [hrecursion]
      exact hformula

/-- Smooth spatial drift implies smooth dependence of every Euler state on the finite bridge
input. -/
theorem contDiff_stateNat {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (i : ℕ) : ContDiff ℝ ∞ (fun z : Input J noiseDim ↦
      stateNat drift diffusion T x₀ z i) := by
  let current : Input J noiseDim → State stateDim :=
    fun z ↦ compensatedStateNat drift diffusion T x₀ z i
  let bridge : Input J noiseDim → State stateDim :=
    fun z ↦ diffusedPath diffusion T z (gridTime T J i)
  have hbridge : ContDiff ℝ ∞ bridge := by
    have hfun : bridge =
        (diffusedPathLinear (J := J) diffusion T (gridTime T J i) :
          Input J noiseDim → State stateDim) := by
      funext z
      exact (diffusedPathLinear_apply diffusion T (gridTime T J i) z).symm
    rw [hfun]
    exact (diffusedPathLinear (J := J) diffusion T (gridTime T J i)).contDiff
  have hsum := (contDiff_compensatedStateNat drift diffusion T x₀ hDrift i).add hbridge
  have hfun : (fun z : Input J noiseDim ↦ stateNat drift diffusion T x₀ z i) =
      fun z ↦ current z + bridge z := by
    funext z
    exact stateNat_eq_compensatedStateNat_add drift diffusion T x₀ i z
  rw [hfun]
  exact hsum

/-- Every mixed Euler-state derivative splits into the compensated-state derivative and the
derivative of the linear bridge forcing. -/
theorem stateDerivative_eq_compensated_add_bridge
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (i : ℕ)
    (u : Finset (Index J noiseDim)) (z : Input J noiseDim) :
    stateDerivative drift diffusion T x₀ i u z =
      compensatedStateDerivative drift diffusion T x₀ i u z +
        mixedDerivative
          (fun y ↦ diffusedPath diffusion T y (gridTime T J i)) u z := by
  let current : Input J noiseDim → State stateDim :=
    fun y ↦ compensatedStateNat drift diffusion T x₀ y i
  let bridge : Input J noiseDim → State stateDim :=
    fun y ↦ diffusedPath diffusion T y (gridTime T J i)
  have hcurrent : ContDiffAt ℝ u.card current z :=
    (contDiff_compensatedStateNat drift diffusion T x₀ hDrift i).contDiffAt.of_le
      (by simp)
  have hbridgeInf : ContDiff ℝ ∞ bridge := by
    have hfun : bridge =
        (diffusedPathLinear (J := J) diffusion T (gridTime T J i) :
          Input J noiseDim → State stateDim) := by
      funext y
      exact (diffusedPathLinear_apply diffusion T (gridTime T J i) y).symm
    rw [hfun]
    exact (diffusedPathLinear (J := J) diffusion T (gridTime T J i)).contDiff
  have hbridge : ContDiffAt ℝ u.card bridge z :=
    hbridgeInf.contDiffAt.of_le (by simp)
  unfold stateDerivative compensatedStateDerivative
  rw [show (fun y : Input J noiseDim ↦ stateNat drift diffusion T x₀ y i) =
      fun y ↦ current y + bridge y by
    funext y
    exact stateNat_eq_compensatedStateNat_add drift diffusion T x₀ i y]
  exact mixedDerivative_add current bridge u z hcurrent hbridge

/-- Mixed derivatives of order at least two do not see the linear bridge term. -/
theorem stateDerivative_eq_compensated_of_two_le
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (i : ℕ)
    (u : Finset (Index J noiseDim)) (hu : 2 ≤ u.card)
    (z : Input J noiseDim) :
    stateDerivative drift diffusion T x₀ i u z =
      compensatedStateDerivative drift diffusion T x₀ i u z := by
  rw [stateDerivative_eq_compensated_add_bridge drift diffusion T x₀ hDrift]
  rw [mixedDerivative_diffusedPath_eq_zero diffusion T (gridTime T J i) u hu z]
  exact add_zero _

/-- A singleton Euler-state derivative is the compensated derivative plus its bridge
coefficient. -/
theorem stateCoordinateDerivative_eq_compensated_add_coefficient
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (i : ℕ)
    (j : Index J noiseDim) (z : Input J noiseDim) :
    stateCoordinateDerivative drift diffusion T x₀ i j z =
      compensatedStateCoordinateDerivative drift diffusion T x₀ i j z +
        diffusionCoefficient diffusion T j (gridTime T J i) := by
  have hsplit := stateDerivative_eq_compensated_add_bridge
    drift diffusion T x₀ hDrift i ({j} : Finset (Index J noiseDim)) z
  simpa only [stateDerivative, compensatedStateDerivative, stateCoordinateDerivative,
    compensatedStateCoordinateDerivative, mixedDerivative_singleton,
    coordinateDerivative_diffusedPath] using hsplit

/-- An unordered drift-input derivative of order at least two is exactly the corresponding
compensated-state derivative. -/
theorem mixedDerivative_eulerDriftInput_of_two_le
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    (u : Finset (Index J noiseDim)) (hu : 2 ≤ u.card)
    (z : Input J noiseDim) :
    mixedDerivative (eulerDriftInput drift diffusion T x₀ step) u z =
      compensatedStateDerivative drift diffusion T x₀ step u z := by
  have hfun : eulerDriftInput drift diffusion T x₀ step =
      fun y : Input J noiseDim ↦ stateNat drift diffusion T x₀ y step := by
    funext y
    exact eulerDriftInput_eq_stateNat drift diffusion T x₀ step y
  rw [hfun]
  exact stateDerivative_eq_compensated_of_two_le
    drift diffusion T x₀ hDrift step u hu z

/-- On a singleton coordinate block, the unordered drift-input derivative splits into the
compensated derivative and the direct Brownian-bridge input. -/
theorem mixedDerivative_eulerDriftInput_singleton
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    (j : Index J noiseDim) (z : Input J noiseDim) :
    mixedDerivative (eulerDriftInput drift diffusion T x₀ step) {j} z =
      compensatedStateDerivative drift diffusion T x₀ step {j} z +
        diffusionCoefficient diffusion T j (gridTime T J step) := by
  have hfun : eulerDriftInput drift diffusion T x₀ step =
      fun y : Input J noiseDim ↦ stateNat drift diffusion T x₀ y step := by
    funext y
    exact eulerDriftInput_eq_stateNat drift diffusion T x₀ step y
  rw [hfun]
  simpa only [stateCoordinateDerivative, compensatedStateCoordinateDerivative,
    compensatedStateDerivative, mixedDerivative_singleton] using
    stateCoordinateDerivative_eq_compensated_add_coefficient
      drift diffusion T x₀ hDrift step j z

/-- Every nonempty unordered partition block contributes its compensated-state derivative and,
exactly for singleton blocks, one direct Brownian-bridge direction. -/
theorem mixedDerivative_eulerDriftInput_partitionBlock
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    {u : Finset (Index J noiseDim)} (p : Finpartition u) (block : p.parts)
    (z : Input J noiseDim) :
    mixedDerivative (eulerDriftInput drift diffusion T x₀ step) block.1 z =
      compensatedStateDerivative drift diffusion T x₀ step block.1 z +
        if hcard : block.1.card = 1 then
          diffusionCoefficient diffusion T
            (finpartitionSingletonCoordinate block hcard) (gridTime T J step)
        else 0 := by
  by_cases hcard : block.1.card = 1
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hcoordinate : finpartitionSingletonCoordinate block hcard = j := by
      apply Finset.mem_singleton.mp
      rw [← hj]
      exact finpartitionSingletonCoordinate_mem block hcard
    simp only [hcard, ↓reduceDIte, hcoordinate]
    rw [hj]
    exact mixedDerivative_eulerDriftInput_singleton
      drift diffusion T x₀ hDrift step j z
  · have hpositive : 0 < block.1.card :=
      Finset.card_pos.mpr (p.nonempty_of_mem_parts block.2)
    have htwo : 2 ≤ block.1.card := by omega
    rw [mixedDerivative_eulerDriftInput_of_two_le
      drift diffusion T x₀ hDrift step block.1 htwo z]
    simp only [hcard, ↓reduceDIte, add_zero]

/-- For a block of size at least two, differentiating the drift input only differentiates the
compensated state: the linear bridge has no higher derivatives. -/
theorem partitionDerivative_eulerDriftInput_of_two_le
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) (hi : 2 ≤ c.partSize i) (z : Input J noiseDim) :
    partitionDerivative (eulerDriftInput drift diffusion T x₀ step) u c i z =
      partitionDerivative
        (fun y ↦ compensatedStateNat drift diffusion T x₀ y step) u c i z := by
  let current : Input J noiseDim → State stateDim :=
    fun y ↦ compensatedStateNat drift diffusion T x₀ y step
  let bridge : Input J noiseDim → State stateDim :=
    fun y ↦ diffusedPath diffusion T y (gridTime T J step)
  have hcurrentInf : ContDiff ℝ ∞ current :=
    contDiff_compensatedStateNat drift diffusion T x₀ hDrift step
  have hbridgeInf : ContDiff ℝ ∞ bridge := by
    have hfun : bridge =
        (diffusedPathLinear (J := J) diffusion T (gridTime T J step) :
          Input J noiseDim → State stateDim) := by
      funext y
      exact (diffusedPathLinear_apply diffusion T (gridTime T J step) y).symm
    rw [hfun]
    exact (diffusedPathLinear (J := J) diffusion T (gridTime T J step)).contDiff
  have hcurrent : ContDiffAt ℝ (c.partSize i) current z :=
    hcurrentInf.contDiffAt.of_le (by simp)
  have hbridge : ContDiffAt ℝ (c.partSize i) bridge z :=
    hbridgeInf.contDiffAt.of_le (by simp)
  change partitionDerivative (fun y ↦ current y + bridge y) u c i z =
    partitionDerivative current u c i z
  rw [partitionDerivative_add current bridge u c i z hcurrent hbridge]
  rw [partitionDerivative_diffusedPath_eq_zero diffusion T
    (gridTime T J step) u c i hi z]
  exact add_zero _

/-- For a singleton block, the drift-input derivative is the compensated-state derivative plus
the corresponding Brownian-bridge coefficient. -/
theorem partitionDerivative_eulerDriftInput_of_partSize_eq_one
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) (hi : c.partSize i = 1) (z : Input J noiseDim) :
    partitionDerivative (eulerDriftInput drift diffusion T x₀ step) u c i z =
      partitionDerivative
          (fun y ↦ compensatedStateNat drift diffusion T x₀ y step) u c i z +
        diffusionCoefficient diffusion T (partitionCoordinate u c i hi)
          (gridTime T J step) := by
  let current : Input J noiseDim → State stateDim :=
    fun y ↦ compensatedStateNat drift diffusion T x₀ y step
  let bridge : Input J noiseDim → State stateDim :=
    fun y ↦ diffusedPath diffusion T y (gridTime T J step)
  have hcurrentInf : ContDiff ℝ ∞ current :=
    contDiff_compensatedStateNat drift diffusion T x₀ hDrift step
  have hbridgeInf : ContDiff ℝ ∞ bridge := by
    have hfun : bridge =
        (diffusedPathLinear (J := J) diffusion T (gridTime T J step) :
          Input J noiseDim → State stateDim) := by
      funext y
      exact (diffusedPathLinear_apply diffusion T (gridTime T J step) y).symm
    rw [hfun]
    exact (diffusedPathLinear (J := J) diffusion T (gridTime T J step)).contDiff
  have hcurrent : ContDiffAt ℝ (c.partSize i) current z :=
    hcurrentInf.contDiffAt.of_le (by simp)
  have hbridge : ContDiffAt ℝ (c.partSize i) bridge z :=
    hbridgeInf.contDiffAt.of_le (by simp)
  change partitionDerivative (fun y ↦ current y + bridge y) u c i z = _
  rw [partitionDerivative_add current bridge u c i z hcurrent hbridge]
  rw [partitionDerivative_diffusedPath_eq_coefficient diffusion T
    (gridTime T J step) u c i hi z]

/-- A block of order at least two in the payoff chain rule contributes only a compensated-state
derivative. -/
theorem partitionDerivative_stateNat_of_two_le
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) (hi : 2 ≤ c.partSize i) (z : Input J noiseDim) :
    partitionDerivative (fun y ↦ stateNat drift diffusion T x₀ y step) u c i z =
      partitionDerivative
        (fun y ↦ compensatedStateNat drift diffusion T x₀ y step) u c i z := by
  have hfun : (fun y : Input J noiseDim ↦ stateNat drift diffusion T x₀ y step) =
      eulerDriftInput drift diffusion T x₀ step := by
    funext y
    exact (eulerDriftInput_eq_stateNat drift diffusion T x₀ step y).symm
  rw [hfun]
  exact partitionDerivative_eulerDriftInput_of_two_le
    drift diffusion T x₀ hDrift step u c i hi z

/-- A singleton block in the payoff chain rule splits into one compensated-state child and one
direct bridge input. -/
theorem partitionDerivative_stateNat_of_partSize_eq_one
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) (hi : c.partSize i = 1) (z : Input J noiseDim) :
    partitionDerivative (fun y ↦ stateNat drift diffusion T x₀ y step) u c i z =
      partitionDerivative
          (fun y ↦ compensatedStateNat drift diffusion T x₀ y step) u c i z +
        diffusionCoefficient diffusion T (partitionCoordinate u c i hi)
          (gridTime T J step) := by
  have hfun : (fun y : Input J noiseDim ↦ stateNat drift diffusion T x₀ y step) =
      eulerDriftInput drift diffusion T x₀ step := by
    funext y
    exact (eulerDriftInput_eq_stateNat drift diffusion T x₀ step y).symm
  rw [hfun]
  exact partitionDerivative_eulerDriftInput_of_partSize_eq_one
    drift diffusion T x₀ hDrift step u c i hi z

/-- One-step derivative recursion for the compensated Euler state.

This is the continuous-linear-map form of the first-order recurrence used to prove
Equation `eq:partition-first`. -/
theorem fderiv_compensatedStateNat_succ {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (i : ℕ)
    (hstate : DifferentiableAt ℝ
      (fun y ↦ compensatedStateNat drift diffusion T x₀ y i) z)
    (hdrift : DifferentiableAt ℝ (drift (gridTime T J i))
      (compensatedStateNat drift diffusion T x₀ z i +
        diffusedPath diffusion T z (gridTime T J i))) :
    fderiv ℝ (fun y ↦ compensatedStateNat drift diffusion T x₀ y (i + 1)) z =
      fderiv ℝ (fun y ↦ compensatedStateNat drift diffusion T x₀ y i) z +
        stepSize T J •
          ((fderiv ℝ (drift (gridTime T J i))
              (compensatedStateNat drift diffusion T x₀ z i +
                diffusedPath diffusion T z (gridTime T J i))).comp
            (fderiv ℝ (fun y ↦ compensatedStateNat drift diffusion T x₀ y i) z +
              diffusedPathLinear diffusion T (gridTime T J i))) := by
  let current : Input J noiseDim → State stateDim :=
    fun y ↦ compensatedStateNat drift diffusion T x₀ y i
  let bridge : Input J noiseDim → State stateDim :=
    fun y ↦ diffusedPath diffusion T y (gridTime T J i)
  have hbridge : HasFDerivAt bridge
      (diffusedPathLinear diffusion T (gridTime T J i)) z := by
    refine (diffusedPathLinear (J := J) diffusion T
      (gridTime T J i)).hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [] with y
    simp [bridge]
  have hinner := hstate.hasFDerivAt.add hbridge
  have hcomposition := hdrift.hasFDerivAt.comp z hinner
  have hsum := hstate.hasFDerivAt.add (hcomposition.const_smul (stepSize T J))
  have hrecursion :
      (fun y ↦ compensatedStateNat drift diffusion T x₀ y (i + 1)) =
        fun y ↦ current y +
          stepSize T J • drift (gridTime T J i) (current y + bridge y) := by
    funext y
    exact compensatedStateNat_succ drift diffusion T x₀ y i
  have hformula : HasFDerivAt
      (fun y ↦ current y +
        stepSize T J • drift (gridTime T J i) (current y + bridge y))
      (fderiv ℝ current z +
        stepSize T J •
          ((fderiv ℝ (drift (gridTime T J i)) (current z + bridge z)).comp
            (fderiv ℝ current z + diffusedPathLinear diffusion T (gridTime T J i)))) z := by
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [] with y
    rfl
  rw [hrecursion]
  exact hformula.fderiv

/-- The first-order coordinate recurrence for `Y_{i,{j}}`.

The inhomogeneous direction is exactly the Brownian-bridge vector coefficient `ξ_j(t_i)`. -/
theorem compensatedStateCoordinateDerivative_succ {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (i : ℕ)
    (j : Index J noiseDim)
    (hstate : DifferentiableAt ℝ
      (fun y ↦ compensatedStateNat drift diffusion T x₀ y i) z)
    (hdrift : DifferentiableAt ℝ (drift (gridTime T J i))
      (compensatedStateNat drift diffusion T x₀ z i +
        diffusedPath diffusion T z (gridTime T J i))) :
    compensatedStateCoordinateDerivative drift diffusion T x₀ (i + 1) j z =
      compensatedStateCoordinateDerivative drift diffusion T x₀ i j z +
        stepSize T J •
          (fderiv ℝ (drift (gridTime T J i))
            (compensatedStateNat drift diffusion T x₀ z i +
              diffusedPath diffusion T z (gridTime T J i)))
            (compensatedStateCoordinateDerivative drift diffusion T x₀ i j z +
              diffusionCoefficient diffusion T j (gridTime T J i)) := by
  unfold compensatedStateCoordinateDerivative coordinateDerivative
  rw [fderiv_compensatedStateNat_succ drift diffusion T x₀ z i hstate hdrift]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply]
  have hbridge :
      diffusedPathLinear diffusion T (gridTime T J i) (inputBasis j) =
        diffusionCoefficient diffusion T j (gridTime T J i) := by
    rw [← fderiv_diffusedPath]
    exact fderiv_diffusedPath_inputBasis diffusion T (gridTime T J i) z j
  rw [hbridge]

/-- The first-order coordinate recurrence under the paper's smooth-drift hypothesis. -/
theorem compensatedStateCoordinateDerivative_succ_of_contDiff
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (z : Input J noiseDim) (i : ℕ)
    (j : Index J noiseDim) :
    compensatedStateCoordinateDerivative drift diffusion T x₀ (i + 1) j z =
      compensatedStateCoordinateDerivative drift diffusion T x₀ i j z +
        stepSize T J •
          (fderiv ℝ (drift (gridTime T J i))
            (compensatedStateNat drift diffusion T x₀ z i +
              diffusedPath diffusion T z (gridTime T J i)))
            (compensatedStateCoordinateDerivative drift diffusion T x₀ i j z +
              diffusionCoefficient diffusion T j (gridTime T J i)) := by
  apply compensatedStateCoordinateDerivative_succ drift diffusion T x₀ z i j
  · exact (contDiff_compensatedStateNat drift diffusion T x₀ hDrift i).differentiable
      (by simp)
      |>.differentiableAt
  · exact (hDrift (gridTime T J i)).differentiable (by simp) |>.differentiableAt

/-- The general one-step mixed-derivative recurrence for the compensated Euler state.

The sum is the set-partition form of Faà di Bruno.  It is the analytic recurrence that the
later tree construction iterates. -/
theorem compensatedStateDerivative_succ_of_contDiff
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (i : ℕ) (u : Finset (Index J noiseDim)) :
    compensatedStateDerivative drift diffusion T x₀ (i + 1) u z =
      compensatedStateDerivative drift diffusion T x₀ i u z +
        stepSize T J •
          ∑ c : OrderedFinpartition u.card,
            partitionChainTerm (drift (gridTime T J i))
              (eulerDriftInput drift diffusion T x₀ i) u c z := by
  let current : Input J noiseDim → State stateDim :=
    fun y ↦ compensatedStateNat drift diffusion T x₀ y i
  let bridge : Input J noiseDim → State stateDim :=
    fun y ↦ diffusedPath diffusion T y (gridTime T J i)
  let inner : Input J noiseDim → State stateDim :=
    eulerDriftInput drift diffusion T x₀ i
  have hcurrentInf : ContDiff ℝ ∞ current :=
    contDiff_compensatedStateNat drift diffusion T x₀ hDrift i
  have hbridgeInf : ContDiff ℝ ∞ bridge := by
    have hfun : bridge =
        (diffusedPathLinear (J := J) diffusion T (gridTime T J i) :
          Input J noiseDim → State stateDim) := by
      funext y
      exact (diffusedPathLinear_apply diffusion T (gridTime T J i) y).symm
    rw [hfun]
    exact (diffusedPathLinear (J := J) diffusion T (gridTime T J i)).contDiff
  have hinnerDef : inner = fun y ↦ current y + bridge y := by
    rfl
  have hinnerInf : ContDiff ℝ ∞ inner := by
    rw [hinnerDef]
    exact hcurrentInf.add hbridgeInf
  have hcompositionInf : ContDiff ℝ ∞
      ((drift (gridTime T J i)) ∘ inner) :=
    (hDrift (gridTime T J i)).comp hinnerInf
  have hcurrent : ContDiffAt ℝ u.card current z :=
    hcurrentInf.contDiffAt.of_le (by simp)
  have hcomposition : ContDiffAt ℝ u.card
      ((drift (gridTime T J i)) ∘ inner) z :=
    hcompositionInf.contDiffAt.of_le (by simp)
  have hscaled : ContDiffAt ℝ u.card
      (fun y ↦ stepSize T J • ((drift (gridTime T J i)) ∘ inner) y) z :=
    hcomposition.const_smul _
  have hrecursion :
      (fun y : Input J noiseDim ↦
        compensatedStateNat drift diffusion T x₀ y (i + 1)) =
      fun y ↦ current y +
        stepSize T J • ((drift (gridTime T J i)) ∘ inner) y := by
    funext y
    exact compensatedStateNat_succ drift diffusion T x₀ y i
  unfold compensatedStateDerivative
  rw [hrecursion]
  rw [mixedDerivative_add current
    (fun y ↦ stepSize T J • ((drift (gridTime T J i)) ∘ inner) y)
    u z hcurrent hscaled]
  rw [mixedDerivative_const_smul (stepSize T J)
    ((drift (gridTime T J i)) ∘ inner) u z hcomposition]
  rw [mixedDerivative_comp (drift (gridTime T J i)) inner u z]
  · exact (hDrift (gridTime T J i)).contDiffAt.of_le (by simp)
  · exact hinnerInf.contDiffAt.of_le (by simp)

end

end TimeDependentLattice.Euler
