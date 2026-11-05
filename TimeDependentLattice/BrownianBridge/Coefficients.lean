/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.BrownianBridge.Index
import TimeDependentLattice.FiniteDimension

/-!
# Brownian-bridge coefficient functions

This file gives the coefficient representation from Equation `eq:hat-explicit`.  The recursive
midpoint construction will later be proved equivalent to these functions; the derivative and
summability arguments use the coefficient representation directly.
-/

namespace TimeDependentLattice.BrownianBridge

noncomputable section

/-- The unit-height hat function `Λ` from Equation `eq:hat-explicit`. -/
def unitHat (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ 1 / 2 then
    2 * x
  else if 1 / 2 < x ∧ x ≤ 1 then
    2 * (1 - x)
  else
    0

@[simp]
theorem unitHat_zero : unitHat 0 = 0 := by
  norm_num [unitHat]

@[simp]
theorem unitHat_half : unitHat (1 / 2) = 1 := by
  norm_num [unitHat]

@[simp]
theorem unitHat_one : unitHat 1 = 0 := by
  norm_num [unitHat]

theorem unitHat_nonneg (x : ℝ) : 0 ≤ unitHat x := by
  rw [unitHat]
  split_ifs with hleft hright
  · exact mul_nonneg (by norm_num) hleft.1
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hright.2)
  · rfl

theorem unitHat_le_one (x : ℝ) : unitHat x ≤ 1 := by
  rw [unitHat]
  split_ifs with hleft hright <;> linarith

theorem unitHat_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : unitHat x = 0 := by
  rw [unitHat]
  split_ifs with hleft hright
  · have : x = 0 := le_antisymm hx hleft.1
    simp [this]
  · exfalso
    linarith [hright.1]
  · rfl

theorem unitHat_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : unitHat x = 0 := by
  rw [unitHat]
  split_ifs with hleft hright
  · exfalso
    linarith [hleft.2]
  · have : x = 1 := le_antisymm hright.2 hx
    simp [this]
  · rfl

/-- The left endpoint `u_(ℓ,k)` of the support interval of a detail coordinate. -/
def DetailIndex.leftEndpoint {J noiseDim : ℕ} (T : ℝ) (j : DetailIndex J noiseDim) : ℝ :=
  j.location.val * T / 2 ^ j.level.val

/-- The right endpoint `v_(ℓ,k)` of the support interval of a detail coordinate. -/
def DetailIndex.rightEndpoint {J noiseDim : ℕ} (T : ℝ) (j : DetailIndex J noiseDim) : ℝ :=
  (j.location.val + 1) * T / 2 ^ j.level.val

/-- The midpoint `c_(ℓ,k)` of the support interval of a detail coordinate. -/
def DetailIndex.center {J noiseDim : ℕ} (T : ℝ) (j : DetailIndex J noiseDim) : ℝ :=
  (j.leftEndpoint T + j.rightEndpoint T) / 2

/-- The open support interval of a detail hat function. -/
def DetailIndex.supportInterior {J noiseDim : ℕ} (T : ℝ)
    (j : DetailIndex J noiseDim) : Set ℝ :=
  Set.Ioo (j.leftEndpoint T) (j.rightEndpoint T)

/-- The support-interval length is `T 2⁻ˡ`. -/
theorem DetailIndex.rightEndpoint_sub_leftEndpoint {J noiseDim : ℕ} (T : ℝ)
    (j : DetailIndex J noiseDim) :
    j.rightEndpoint T - j.leftEndpoint T = T / 2 ^ j.level.val := by
  rw [DetailIndex.rightEndpoint, DetailIndex.leftEndpoint]
  ring

/-- For positive terminal time, the center lies in the open support interval. -/
theorem DetailIndex.center_mem_supportInterior {J noiseDim : ℕ} {T : ℝ}
    (hT : 0 < T) (j : DetailIndex J noiseDim) :
    j.center T ∈ j.supportInterior T := by
  rw [DetailIndex.supportInterior, Set.mem_Ioo, DetailIndex.center]
  have hlength : 0 < j.rightEndpoint T - j.leftEndpoint T := by
    rw [DetailIndex.rightEndpoint_sub_leftEndpoint]
    positivity
  constructor <;> linarith

/-- The scalar coefficient `ϑ_j(t)` in Equation `eq:hat-explicit`. -/
def coefficient {J noiseDim : ℕ} (T : ℝ) : Index J noiseDim → ℝ → ℝ
  | Sum.inl _, t => t / √T
  | Sum.inr j, t =>
      √T / 2 * (2 : ℝ) ^ (-(j.level.val : ℝ) / 2) *
        unitHat ((2 ^ j.level.val : ℕ) * t / T - j.location.val)

@[simp]
theorem coefficient_endpoint {J noiseDim : ℕ} (T t : ℝ) (r : Fin noiseDim) :
    coefficient (J := J) T (Sum.inl r) t = t / √T := rfl

@[simp]
theorem coefficient_endpoint_terminal {J noiseDim : ℕ} (T : ℝ) (r : Fin noiseDim) :
    coefficient (J := J) T (Sum.inl r) T = √T := by
  simp [Real.div_sqrt]

@[simp]
theorem coefficient_detail {J noiseDim : ℕ} (T t : ℝ) (j : DetailIndex J noiseDim) :
    coefficient T (Sum.inr j) t =
      √T / 2 * (2 : ℝ) ^ (-(j.level.val : ℝ) / 2) *
        unitHat ((2 ^ j.level.val : ℕ) * t / T - j.location.val) := rfl

/-- Every Brownian-bridge coefficient vanishes at time zero. -/
@[simp]
theorem coefficient_zero {J noiseDim : ℕ} (T : ℝ) (j : Index J noiseDim) :
    coefficient T j 0 = 0 := by
  cases j with
  | inl r => simp
  | inr j =>
      rw [coefficient_detail]
      have hargument :
          ((2 ^ j.level.val : ℕ) : ℝ) * 0 / T - j.location.val ≤ 0 := by
        simp
      rw [unitHat_eq_zero_of_nonpos hargument]
      ring

/-- Every detail coefficient vanishes at the terminal time. -/
@[simp]
theorem coefficient_detail_terminal {J noiseDim : ℕ} {T : ℝ} (hT : T ≠ 0)
    (j : DetailIndex J noiseDim) : coefficient T (Sum.inr j) T = 0 := by
  rw [coefficient_detail]
  have hlocation : j.location.val + 1 ≤ 2 ^ j.level.val := j.location.isLt
  have hlocationReal : (j.location.val : ℝ) + 1 ≤ (2 ^ j.level.val : ℕ) := by
    exact_mod_cast hlocation
  have hcancel :
      ((2 ^ j.level.val : ℕ) : ℝ) * T / T = (2 ^ j.level.val : ℕ) := by
    exact mul_div_cancel_right₀ _ hT
  have hargument :
      1 ≤ ((2 ^ j.level.val : ℕ) : ℝ) * T / T - j.location.val := by
    rw [hcancel]
    linarith
  rw [unitHat_eq_zero_of_one_le hargument]
  ring

/-- Detail coefficients are nonnegative. -/
theorem coefficient_detail_nonneg {J noiseDim : ℕ} {T : ℝ}
    (j : DetailIndex J noiseDim) (t : ℝ) : 0 ≤ coefficient T (Sum.inr j) t := by
  rw [coefficient_detail]
  have hfactor : 0 ≤ √T / 2 * (2 : ℝ) ^ (-(j.level.val : ℝ) / 2) := by
    positivity
  exact mul_nonneg hfactor (unitHat_nonneg _)

/-- The level-dependent uniform upper bound for a detail coefficient. -/
theorem coefficient_detail_le {J noiseDim : ℕ} {T : ℝ}
    (j : DetailIndex J noiseDim) (t : ℝ) :
    coefficient T (Sum.inr j) t ≤ √T / 2 * (2 : ℝ) ^ (-(j.level.val : ℝ) / 2) := by
  rw [coefficient_detail]
  have hfactor : 0 ≤ √T / 2 * (2 : ℝ) ^ (-(j.level.val : ℝ) / 2) := by
    positivity
  exact mul_le_of_le_one_right hfactor (unitHat_le_one _)

/-- A detail coefficient vanishes outside the interior of its dyadic support interval. -/
theorem coefficient_detail_eq_zero_of_not_mem_supportInterior
    {J noiseDim : ℕ} {T t : ℝ} (hT : 0 < T) (j : DetailIndex J noiseDim)
    (ht : t ∉ j.supportInterior T) :
    coefficient T (Sum.inr j) t = 0 := by
  have hpow : (0 : ℝ) < (2 ^ j.level.val : ℕ) := by positivity
  rw [DetailIndex.supportInterior, Set.mem_Ioo, not_and_or] at ht
  rw [coefficient_detail]
  rcases ht with hleft | hright
  · have harg :
        ((2 ^ j.level.val : ℕ) : ℝ) * t / T - j.location.val ≤ 0 := by
      rw [DetailIndex.leftEndpoint] at hleft
      apply sub_nonpos.mpr
      rw [div_le_iff₀ hT]
      have htleft : t ≤ j.location.val * T / 2 ^ j.level.val :=
        le_of_not_gt hleft
      calc
        ((2 ^ j.level.val : ℕ) : ℝ) * t ≤
            ((2 ^ j.level.val : ℕ) : ℝ) *
              (j.location.val * T / 2 ^ j.level.val) := by
                exact mul_le_mul_of_nonneg_left htleft hpow.le
        _ = (j.location.val : ℝ) * T := by
              field_simp
              norm_num [Nat.cast_pow]
              ring
    rw [unitHat_eq_zero_of_nonpos harg]
    ring
  · have harg :
        1 ≤ ((2 ^ j.level.val : ℕ) : ℝ) * t / T - j.location.val := by
      rw [DetailIndex.rightEndpoint] at hright
      rw [le_sub_iff_add_le, le_div_iff₀ hT]
      have hrightt :
          (j.location.val + 1) * T / 2 ^ j.level.val ≤ t :=
        le_of_not_gt hright
      calc
        (1 + (j.location.val : ℝ)) * T =
            ((2 ^ j.level.val : ℕ) : ℝ) *
              ((j.location.val + 1) * T / 2 ^ j.level.val) := by
                field_simp
                norm_num [Nat.cast_pow]
                ring
        _ ≤ ((2 ^ j.level.val : ℕ) : ℝ) * t :=
          mul_le_mul_of_nonneg_left hrightt hpow.le
    rw [unitHat_eq_zero_of_one_le harg]
    ring

/-- The vector coefficient `ξ_j(t) = Σ e_(r(j)) ϑ_j(t)`. -/
def diffusionCoefficient {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (j : Index J noiseDim) (t : ℝ) :
    State stateDim :=
  coefficient T j t • diffusion (noiseBasis j.component)

@[simp]
theorem diffusionCoefficient_endpoint_terminal {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (r : Fin noiseDim) :
    diffusionCoefficient (J := J) diffusion T (Sum.inl r) T =
      √T • diffusion (noiseBasis r) := by
  simp [diffusionCoefficient, Index.component]

end

end TimeDependentLattice.BrownianBridge
