/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.LocalEstimates

/-!
# Local Euler remainder estimates from standard integral representations

The public hypotheses below specify the actual state random variables, their moment bounds,
the drift regularity, and the SDE/Bochner-Fubini representation equations. The increment
constant and the local remainder estimates are conclusions.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open MeasureTheory Set
open scoped ENNReal

section Representatives

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- An `L²` representative has exactly the `lpNorm` of its actual random variable. -/
theorem norm_lp_eq_lpNorm_of_ae_eq (F : Lp E 2 μ) (f : Ω → E)
    (hRep : (fun ω ↦ F ω) =ᵐ[μ] f) : ‖F‖ = lpNorm f 2 μ := by
  rw [Lp.norm_def]
  change (eLpNorm (fun ω ↦ F ω) 2 μ).toReal = (eLpNorm f 2 μ).toReal
  rw [eLpNorm_congr_ae hRep]

omit [NormedSpace ℝ E] in
/-- Identify the canonical `toLp` lift with any supplied almost-everywhere representative. -/
theorem toLp_eq_of_ae_rep (F : Lp E 2 μ) (f : Ω → E) (hf : MemLp f 2 μ)
    (hRep : (fun ω ↦ F ω) =ᵐ[μ] f) : hf.toLp f = F := by
  apply Lp.ext
  exact hf.coeFn_toLp.trans hRep.symm

omit [NormedSpace ℝ E] in
/-- Spatial Lipschitz continuity supplies the continuity needed for random-state evaluation. -/
theorem continuous_of_spatial_norm_bound (b : E → E) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) : Continuous b := by
  have h : LipschitzWith L.toNNReal b := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, Real.coe_toNNReal L hL] using hLip x y
  exact h.continuous

omit [NormedSpace ℝ E] in
/-- Growth and spatial regularity also derive the `MemLp` premises used internally. -/
theorem drift_composition_memLp
    [IsProbabilityMeasure μ] (b : E → E) (X : Ω → E) {K0 L : ℝ}
    (hL : 0 ≤ L) (hX : MemLp X 2 μ)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (hgrowth : ∀ x, ‖b x‖ ≤ K0 + L * ‖x‖) :
    MemLp (fun ω ↦ b (X ω)) 2 μ := by
  have henv : MemLp (fun ω ↦ K0 + L * ‖X ω‖) 2 μ :=
    (memLp_const K0).add (hX.norm.const_mul L)
  exact henv.mono'
    ((continuous_of_spatial_norm_bound b hL hLip).comp_aestronglyMeasurable
      hX.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω ↦ hgrowth (X ω))

end Representatives

section HalfOrder

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full half-order local estimate from the actual SDE state and standard integral
representations. No state-increment, drift-increment, or local-remainder estimate is assumed. -/
theorem half_local_remainder_from_state_equation
    {T K0 L Ht initialNorm sigmaHS t h : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (hh : 0 ≤ h) (hhT : h ≤ T)
    (X : ℝ → Ω → E) (b : ℝ → E → E)
    (hX : ∀ s ∈ Icc t (t + h), MemLp (X s) 2 μ)
    (hMoment : ∀ s ∈ Icc t (t + h), lpNorm (X s) 2 μ ≤
      stateMomentConstant T K0 L initialNorm sigmaHS)
    (hLip : ∀ s ∈ Icc t (t + h), ∀ x y,
      ‖b s x - b s y‖ ≤ L * ‖x - y‖)
    (hGrowth : ∀ s ∈ Icc t (t + h), ∀ x, ‖b s x‖ ≤ K0 + L * ‖x‖)
    (hTime : ∀ s ∈ Icc t (t + h), ∀ x,
      ‖b s x - b t x‖ ≤ Ht * (1 + ‖x‖) * Real.sqrt (s - t))
    (driftLp noiseLp deltaLp : ℝ → Lp E 2 μ)
    (hDriftRep : ∀ s ∈ Icc t (t + h),
      (fun ω ↦ driftLp s ω) =ᵐ[μ] fun ω ↦ b s (X s ω))
    (hIncrementEq : ∀ s (hs : s ∈ Icc t (t + h)),
      ((hX s hs).sub (hX t ⟨le_rfl, by linarith⟩)).toLp
          (fun ω ↦ X s ω - X t ω) =
        (∫ r in t..s, driftLp r) + noiseLp s)
    (hNoise : ∀ s ∈ Icc t (t + h), ‖noiseLp s‖ ≤ sigmaHS * Real.sqrt (s - t))
    (hDeltaRep : ∀ s ∈ Icc t (t + h),
      (fun ω ↦ deltaLp s ω) =ᵐ[μ] fun ω ↦ b s (X s ω) - b t (X t ω))
    (hDeltaIntegrable : IntervalIntegrable deltaLp volume t (t + h))
    (R : Ω → E) (hR : MemLp R 2 μ)
    (hRRep : hR.toLp R = ∫ s in t..t + h, deltaLp s) :
    lpNorm R 2 μ ≤ (2 / 3 : ℝ) *
      (L * incrementConstant T K0 L initialNorm sigmaHS +
        Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) *
      h * Real.sqrt h := by
  have ht : t ∈ Icc t (t + h) := ⟨le_rfl, by linarith⟩
  have hMixed : ∀ s ∈ Icc t (t + h), ∀ r ∈ Icc t (t + h),
      MemLp (fun ω ↦ b s (X r ω)) 2 μ := by
    intro s hs r hr
    exact drift_composition_memLp (b s) (X r) hL (hX r hr)
      (hLip s hs) (hGrowth s hs)
  have hDriftBound : ∀ r ∈ Icc t (t + h), ‖driftLp r‖ ≤
      K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS := by
    intro r hr
    rw [norm_lp_eq_lpNorm_of_ae_eq _ _ (hDriftRep r hr)]
    exact (drift_growth_lpNorm_le (b r) (X r) hK0 hL (hX r hr)
      (hGrowth r hr)).trans (by gcongr; exact hMoment r hr)
  have hIncrement : ∀ s ∈ Icc t (t + h),
      lpNorm (fun ω ↦ X s ω - X t ω) 2 μ ≤
        incrementConstant T K0 L initialNorm sigmaHS * Real.sqrt (s - t) := by
    intro s hs
    have hsT : s - t ≤ T := by linarith [hs.2]
    have hs0 : 0 ≤ s - t := sub_nonneg.mpr hs.1
    apply state_increment_lpNorm_of_integral_eq hT hK0 hL hinitial hsigma hs0 hsT t
      (X s) (X t) ((hX s hs).sub (hX t ht)) (noiseLp s) driftLp
    · simpa using hIncrementEq s hs
    · intro r hr
      apply hDriftBound r
      constructor
      · exact hr.1
      · linarith [hr.2, hs.2]
    · exact hNoise s hs
  apply half_local_remainder_lpNorm_bound hh R hR deltaLp hDeltaIntegrable hRRep
  intro s hs
  rw [norm_lp_eq_lpNorm_of_ae_eq _ _ (hDeltaRep s hs)]
  exact drift_increment_lpNorm_le (b s) (b t) (X s) (X t) hL hHt
    (Real.sqrt_nonneg _) ((hX s hs).sub (hX t ht)) (hX t ht)
    ((hMixed s hs s hs).sub (hMixed s hs t ht))
    (hLip s hs) (hTime s hs) (hMoment t ht) (hIncrement s hs)

end HalfOrder

section OrderOne

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual first-order deterministic remainder bound from the local Itô/Fubini
representation, drift regularity, moment estimate, and operator/trace estimates.
In particular, no bound on `C_A`, the integrated remainder, or the global error is assumed. -/
theorem order_one_local_remainder_from_ito_representation
    {T K0 L B2 Lt initialNorm sigmaHS t h : ℝ}
    (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2) (hLt : 0 ≤ Lt)
    (hh : 0 ≤ h)
    (X : ℝ → Ω → E) (b : ℝ → E → E)
    (hX : ∀ s ∈ Icc t (t + h), MemLp (X s) 2 μ)
    (hMoment : ∀ s ∈ Icc t (t + h), lpNorm (X s) 2 μ ≤
      stateMomentConstant T K0 L initialNorm sigmaHS)
    (hLip : ∀ s ∈ Icc t (t + h), ∀ x y,
      ‖b s x - b s y‖ ≤ L * ‖x - y‖)
    (hGrowth : ∀ s ∈ Icc t (t + h), ∀ x, ‖b s x‖ ≤ K0 + L * ‖x‖)
    (hTime : ∀ s ∈ Icc t (t + h), ∀ x,
      ‖b s x - b t x‖ ≤ Lt * (1 + ‖x‖) * (s - t))
    (operator : ℝ → Ω → E →L[ℝ] E) (trace : ℝ → Ω → E)
    (hOperator : ∀ s ∈ Icc t (t + h), ∀ ω, ‖operator s ω‖ ≤ L)
    (hTrace : ∀ s ∈ Icc t (t + h), ∀ ω,
      ‖trace s ω‖ ≤ B2 * sigmaHS ^ 2)
    (hTraceMeas : ∀ s ∈ Icc t (t + h), AEStronglyMeasurable (trace s) μ)
    (temporalLp generatorLp : ℝ → Lp E 2 μ)
    (hTemporalRep : ∀ s ∈ Icc t (t + h),
      (fun ω ↦ temporalLp s ω) =ᵐ[μ] fun ω ↦ b s (X s ω) - b t (X s ω))
    (hGeneratorRep : ∀ s ∈ Icc t (t + h),
      (fun ω ↦ generatorLp s ω) =ᵐ[μ]
        fun ω ↦ operator s ω (b s (X s ω)) + (1 / 2 : ℝ) • trace s ω)
    (hTemporalIntegrable : IntervalIntegrable temporalLp volume t (t + h))
    (hGeneratorIntegrable : IntervalIntegrable (fun s ↦ (t + h - s) • generatorLp s)
      volume t (t + h))
    (A : Ω → E) (hA : MemLp A 2 μ)
    (hARep : hA.toLp A = (∫ s in t..t + h, temporalLp s) +
      (∫ s in t..t + h, (t + h - s) • generatorLp s)) :
    lpNorm A 2 μ ≤ driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS * h ^ 2 := by
  apply order_one_local_remainder_lpNorm_bound hh A hA temporalLp generatorLp
    hTemporalIntegrable hGeneratorIntegrable hARep
  · intro s hs
    rw [norm_lp_eq_lpNorm_of_ae_eq _ _ (hTemporalRep s hs)]
    have ht := drift_time_lpNorm_le (b s) (b t) (X s) hLt
      (sub_nonneg.mpr hs.1) (hX s hs) (hTime s hs)
    have hcx : Lt * (1 + lpNorm (X s) 2 μ) ≤
        Lt * (1 + stateMomentConstant T K0 L initialNorm sigmaHS) := by
      gcongr
      exact hMoment s hs
    exact ht.trans (mul_le_mul_of_nonneg_right hcx (sub_nonneg.mpr hs.1))
  · intro s hs
    rw [norm_lp_eq_lpNorm_of_ae_eq _ _ (hGeneratorRep s hs)]
    have hbX : MemLp (fun ω ↦ b s (X s ω)) 2 μ :=
      drift_composition_memLp (b s) (X s) hL (hX s hs)
        (hLip s hs) (hGrowth s hs)
    have hTraceMem : MemLp (trace s) 2 μ :=
      (memLp_const (B2 * sigmaHS ^ 2) :
        MemLp (fun _ : Ω ↦ B2 * sigmaHS ^ 2) 2 μ).mono'
          (hTraceMeas s hs) (Filter.Eventually.of_forall (hTrace s hs))
    have hGenMem : MemLp
        (fun ω ↦ operator s ω (b s (X s ω)) + (1 / 2 : ℝ) • trace s ω) 2 μ :=
      (Lp.memLp (generatorLp s)).ae_eq (hGeneratorRep s hs)
    have hActionMem : MemLp (fun ω ↦ operator s ω (b s (X s ω))) 2 μ := by
      have hx := hGenMem.sub (hTraceMem.const_smul (1 / 2 : ℝ))
      have heq : ((fun ω ↦ operator s ω (b s (X s ω)) +
          (1 / 2 : ℝ) • trace s ω) - (1 / 2 : ℝ) • trace s) =
          (fun ω ↦ operator s ω (b s (X s ω))) := by
        funext ω
        simp
      rwa [heq] at hx
    exact frozen_generator_lpNorm_le (b s) (X s) (operator s) (trace s)
      hK0 hL hB2 (hX s hs) hbX hActionMem (hGrowth s hs)
      (hOperator s hs) (hTrace s hs) (hMoment s hs)

end OrderOne

end

end TimeDependentLattice.Bias
