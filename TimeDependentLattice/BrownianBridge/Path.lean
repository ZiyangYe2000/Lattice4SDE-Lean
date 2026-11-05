/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.BrownianBridge.Coefficients

/-!
# Brownian-bridge paths

This file assembles the scalar coefficient functions into the finite-dimensional path
`W_t(z)` and its image `Σ W_t(z)`.  Everything here is deterministic; the Gaussian law of the
input vector will be introduced in a later probability module.
-/

namespace TimeDependentLattice.BrownianBridge

noncomputable section

open scoped BigOperators

/-- The Euclidean space of Brownian-bridge input coordinates. -/
abbrev Input (J noiseDim : ℕ) := EuclideanSpace ℝ (Index J noiseDim)

/-- The standard basis vector belonging to one Brownian-bridge input coordinate. -/
def inputBasis {J noiseDim : ℕ} (j : Index J noiseDim) : Input J noiseDim :=
  PiLp.single 2 j 1

/-- Evaluation at one Brownian-bridge input coordinate, as a continuous linear map. -/
def inputCoordinate {J noiseDim : ℕ} (j : Index J noiseDim) : Input J noiseDim →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Index J noiseDim ↦ ℝ)).toContinuousLinearMap

@[simp]
theorem inputCoordinate_apply {J noiseDim : ℕ} (j : Index J noiseDim)
    (z : Input J noiseDim) : inputCoordinate j z = z j := rfl

/-- The uniform grid spacing `h = T / 2^J`. -/
def stepSize (T : ℝ) (J : ℕ) : ℝ := T / numSteps J

/-- The grid time `t_i = i h`. -/
def gridTime (T : ℝ) (J i : ℕ) : ℝ := i * stepSize T J

theorem stepSize_nonneg {T : ℝ} (hT : 0 ≤ T) (J : ℕ) :
    0 ≤ stepSize T J := by
  unfold stepSize
  positivity

theorem gridTime_nonneg {T : ℝ} (hT : 0 ≤ T) (J i : ℕ) :
    0 ≤ gridTime T J i := by
  unfold gridTime
  exact mul_nonneg (Nat.cast_nonneg _) (stepSize_nonneg hT J)

@[simp]
theorem gridTime_zero (T : ℝ) (J : ℕ) : gridTime T J 0 = 0 := by
  simp [gridTime]

@[simp]
theorem gridTime_terminal (T : ℝ) (J : ℕ) : gridTime T J (numSteps J) = T := by
  rw [gridTime, stepSize]
  have hsteps : ((numSteps J : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (numSteps_pos J))
  simpa only [mul_div_assoc] using (mul_div_cancel_left₀ T hsteps)

/-- Every time on the finite Euler grid lies in `[0,T]`. -/
theorem gridTime_le_terminal {T : ℝ} (hT : 0 ≤ T) (J : ℕ) {i : ℕ}
    (hi : i ≤ numSteps J) : gridTime T J i ≤ T := by
  calc
    gridTime T J i ≤ gridTime T J (numSteps J) := by
      unfold gridTime
      apply mul_le_mul_of_nonneg_right _ (stepSize_nonneg hT J)
      exact_mod_cast hi
    _ = T := gridTime_terminal T J

/-- The Brownian-bridge path `W_t(z)` assembled from its finite coefficient family. -/
def path {J noiseDim : ℕ} (T : ℝ) (z : Input J noiseDim) (t : ℝ) : Noise noiseDim :=
  ∑ j, (z j * coefficient T j t) • noiseBasis j.component

/-- For fixed `t`, the map from bridge inputs to `W_t(z)` is continuous linear. -/
def pathLinear {J noiseDim : ℕ} (T t : ℝ) : Input J noiseDim →L[ℝ] Noise noiseDim :=
  ∑ j, (inputCoordinate j).smulRight (coefficient T j t • noiseBasis j.component)

@[simp]
theorem pathLinear_apply {J noiseDim : ℕ} (T t : ℝ) (z : Input J noiseDim) :
    pathLinear T t z = path T z t := by
  simp [pathLinear, path, smul_smul, mul_comm]

@[simp]
theorem path_zero {J noiseDim : ℕ} (T : ℝ) (z : Input J noiseDim) : path T z 0 = 0 := by
  simp [path]

/-- The state-space forcing `Σ W_t(z)`. -/
def diffusedPath {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (z : Input J noiseDim) (t : ℝ) : State stateDim :=
  diffusion (path T z t)

/-- For fixed `t`, the map from bridge inputs to `Σ W_t(z)` is continuous linear. -/
def diffusedPathLinear {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T t : ℝ) :
    Input J noiseDim →L[ℝ] State stateDim :=
  diffusion.comp (pathLinear T t)

@[simp]
theorem diffusedPathLinear_apply {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T t : ℝ) (z : Input J noiseDim) :
    diffusedPathLinear diffusion T t z = diffusedPath diffusion T z t := by
  simp [diffusedPathLinear, diffusedPath]

@[simp]
theorem diffusedPath_zero {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (z : Input J noiseDim) :
    diffusedPath diffusion T z 0 = 0 := by
  simp [diffusedPath]

/-- Applying the diffusion matrix to the bridge path agrees with summing the vector
coefficients `ξ_j(t)`. -/
theorem diffusedPath_eq_sum {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (z : Input J noiseDim) (t : ℝ) :
    diffusedPath diffusion T z t = ∑ j, z j • diffusionCoefficient diffusion T j t := by
  simp only [diffusedPath, path, map_sum, map_smul, diffusionCoefficient, smul_smul]

end

end TimeDependentLattice.BrownianBridge
