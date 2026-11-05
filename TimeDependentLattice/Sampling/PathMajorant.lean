/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Regularity.Eta
import TimeDependentLattice.Sampling.HybridMoment

/-!
# The Brownian-bridge path majorant in Lemma 5.1

This file formalizes Equation `eq:auxiliary-noise-path-bound` from the paper.  Its key
combinatorial input is that, at a fixed time, level, and Brownian component, at most one
dyadic hat function is nonzero.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Regularity

/-- Regard a raw coordinate vector, as used by the product probability measure, as the
Euclidean Brownian-bridge input used by the Euler recursion. -/
def bridgeInput {J noiseDim : ℕ} (z : Index J noiseDim → ℝ) : Input J noiseDim :=
  WithLp.toLp 2 z

@[simp]
theorem bridgeInput_apply {J noiseDim : ℕ} (z : Index J noiseDim → ℝ)
    (j : Index J noiseDim) : bridgeInput z j = z j := rfl

/-- The set of location indices whose level-`level` hat is active at time `t`. -/
def activeDetailLocations {J noiseDim : ℕ} (T t : ℝ) (level : Fin J)
    (r : Fin noiseDim) : Finset (Fin (2 ^ level.val)) := by
  classical
  exact Finset.univ.filter fun k =>
    t ∈ (show DetailIndex J noiseDim from ⟨level, (k, r)⟩).supportInterior T

/-- At a fixed time, level, and component, at most one dyadic hat is active. -/
theorem card_activeDetailLocations_le_one
    {J noiseDim : ℕ} {T : ℝ} (hT : 0 < T) (t : ℝ) (level : Fin J)
    (r : Fin noiseDim) :
    (activeDetailLocations T t level r).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro k q hk hq
  have hk' :
      t ∈ (show DetailIndex J noiseDim from ⟨level, (k, r)⟩).supportInterior T := by
    simpa [activeDetailLocations] using hk
  have hq' :
      t ∈ (show DetailIndex J noiseDim from ⟨level, (q, r)⟩).supportInterior T := by
    simpa [activeDetailLocations] using hq
  have heq := detail_eq_of_same_level_component_of_common_support hT
    (⟨level, (k, r)⟩ : DetailIndex J noiseDim)
    (⟨level, (q, r)⟩ : DetailIndex J noiseDim) rfl rfl hk' hq'
  apply Fin.ext
  exact congrArg (fun j : DetailIndex J noiseDim => j.location.val) heq

/-- The contribution of all locations at one fixed level and Brownian component is bounded
by the height of one hat times the coordinate maximum `M_{ℓ,r}`. -/
theorem detailLevelComponent_sum_norm_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) (z : Index J noiseDim → ℝ) (t : ℝ)
    (level : Fin J) (r : Fin noiseDim) :
    (∑ k : Fin (2 ^ level.val),
      ‖z (Sum.inr ⟨level, (k, r)⟩) •
        diffusionCoefficient diffusion T (Sum.inr ⟨level, (k, r)⟩) t‖) ≤
      detailHeightFactor diffusion T (⟨level, (0, r)⟩ : DetailIndex J noiseDim) *
        detailLevelMaxAbs z level r := by
  classical
  let active := activeDetailLocations T t level r
  let bound := detailHeightFactor diffusion T
      (⟨level, (0, r)⟩ : DetailIndex J noiseDim) * detailLevelMaxAbs z level r
  have hsumFilter :
      (∑ k ∈ active,
        ‖z (Sum.inr ⟨level, (k, r)⟩) •
          diffusionCoefficient diffusion T (Sum.inr ⟨level, (k, r)⟩) t‖) =
        ∑ k : Fin (2 ^ level.val),
          ‖z (Sum.inr ⟨level, (k, r)⟩) •
            diffusionCoefficient diffusion T (Sum.inr ⟨level, (k, r)⟩) t‖ := by
    have hfilter := Finset.sum_filter_of_ne
      (s := (Finset.univ : Finset (Fin (2 ^ level.val))))
      (f := fun k =>
        ‖z (Sum.inr ⟨level, (k, r)⟩) •
          diffusionCoefficient diffusion T (Sum.inr ⟨level, (k, r)⟩) t‖)
      (p := fun k =>
        t ∈ (show DetailIndex J noiseDim from ⟨level, (k, r)⟩).supportInterior T)
      (by
        intro k hk hne
        have hsupport :
            t ∈ (show DetailIndex J noiseDim from
              ⟨level, (k, r)⟩).supportInterior T := by
          by_contra hout
          have hcoefficient := coefficient_detail_eq_zero_of_not_mem_supportInterior hT
            (⟨level, (k, r)⟩ : DetailIndex J noiseDim) hout
          apply hne
          rw [diffusionCoefficient, hcoefficient, zero_smul, smul_zero, norm_zero]
        exact hsupport)
    simpa [active, activeDetailLocations] using hfilter
  have hterm : ∀ k ∈ active,
      ‖z (Sum.inr ⟨level, (k, r)⟩) •
        diffusionCoefficient diffusion T (Sum.inr ⟨level, (k, r)⟩) t‖ ≤ bound := by
    intro k hk
    rw [norm_smul, Real.norm_eq_abs]
    rw [mul_comm]
    apply mul_le_mul
    · simpa [detailHeightFactor, DetailIndex.level, DetailIndex.component] using
        (norm_diffusionCoefficient_detail_le diffusion
          (⟨level, (k, r)⟩ : DetailIndex J noiseDim) t)
    · exact abs_detailLevelCoordinate_le_maxAbs z level r k
    · exact abs_nonneg _
    · exact detailHeightFactor_nonneg diffusion T _
  have hbound : 0 ≤ bound := by
    apply mul_nonneg (detailHeightFactor_nonneg diffusion T _)
    obtain ⟨k, hk⟩ := exists_detailLevelCoordinate_eq_maxAbs z level r
    rw [hk]
    exact abs_nonneg _
  calc
    (∑ k : Fin (2 ^ level.val),
      ‖z (Sum.inr ⟨level, (k, r)⟩) •
        diffusionCoefficient diffusion T (Sum.inr ⟨level, (k, r)⟩) t‖) =
        ∑ k ∈ active,
          ‖z (Sum.inr ⟨level, (k, r)⟩) •
            diffusionCoefficient diffusion T (Sum.inr ⟨level, (k, r)⟩) t‖ :=
      hsumFilter.symm
    _ ≤ active.card • bound := Finset.sum_le_card_nsmul active _ bound hterm
    _ ≤ 1 • bound := by
      exact nsmul_le_nsmul_left hbound (card_activeDetailLocations_le_one hT t level r)
    _ = bound := one_nsmul _

/-- The deterministic majorant on the right-hand side of paper Equation
`eq:auxiliary-noise-path-bound`, grouped by endpoint coordinates and by detail
level/component pairs. -/
def brownianPathMajorant {J stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (z : Index J noiseDim → ℝ) : ℝ :=
  (∑ r : Fin noiseDim,
      endpointFactor diffusion T r * |z (Sum.inl r)|) +
    ∑ level : Fin J, ∑ r : Fin noiseDim,
      detailHeightFactor diffusion T
          (⟨level, (0, r)⟩ : DetailIndex J noiseDim) *
        detailLevelMaxAbs z level r

theorem brownianPathMajorant_nonneg
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (z : Index J noiseDim → ℝ) :
    0 ≤ brownianPathMajorant diffusion T z := by
  unfold brownianPathMajorant
  apply add_nonneg <;> apply Finset.sum_nonneg
  · intro r hr
    exact mul_nonneg (endpointFactor_nonneg diffusion T r) (abs_nonneg _)
  · intro level hlevel
    apply Finset.sum_nonneg
    intro r hr
    apply mul_nonneg (detailHeightFactor_nonneg diffusion T _)
    obtain ⟨k, hk⟩ := exists_detailLevelCoordinate_eq_maxAbs z level r
    rw [hk]
    exact abs_nonneg _

/-- Equation `eq:auxiliary-noise-path-bound`: the diffused Brownian-bridge path at every
Euler grid point is bounded by the endpoint/detail majorant. -/
theorem norm_diffusedPath_grid_le_brownianPathMajorant
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 < T) (z : Index J noiseDim → ℝ) (i : ℕ)
    (hi : i ≤ numSteps J) :
    ‖diffusedPath diffusion T (bridgeInput z) (gridTime T J i)‖ ≤
      brownianPathMajorant diffusion T z := by
  rw [diffusedPath_eq_sum]
  calc
    ‖∑ j : Index J noiseDim,
        bridgeInput z j •
          diffusionCoefficient diffusion T j (gridTime T J i)‖ ≤
        ∑ j : Index J noiseDim,
          ‖bridgeInput z j •
            diffusionCoefficient diffusion T j (gridTime T J i)‖ :=
      norm_sum_le _ _
    _ = (∑ r : Fin noiseDim,
          ‖z (Sum.inl r) •
            diffusionCoefficient diffusion T (Sum.inl r) (gridTime T J i)‖) +
        ∑ j : DetailIndex J noiseDim,
          ‖z (Sum.inr j) •
            diffusionCoefficient diffusion T (Sum.inr j) (gridTime T J i)‖ := by
      rw [Fintype.sum_sum_type]
      congr 1
    _ ≤ (∑ r : Fin noiseDim,
          endpointFactor diffusion T r * |z (Sum.inl r)|) +
        ∑ level : Fin J, ∑ r : Fin noiseDim,
          detailHeightFactor diffusion T
              (⟨level, (0, r)⟩ : DetailIndex J noiseDim) *
            detailLevelMaxAbs z level r := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro r hr
        rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (norm_diffusionCoefficient_endpoint_le diffusion hT.le r i hi)
          (abs_nonneg _)
      · rw [Fintype.sum_sigma]
        apply Finset.sum_le_sum
        intro level hlevel
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_le_sum
        intro r hr
        exact detailLevelComponent_sum_norm_le diffusion hT z (gridTime T J i) level r
    _ = brownianPathMajorant diffusion T z := rfl

end

end TimeDependentLattice.Sampling
