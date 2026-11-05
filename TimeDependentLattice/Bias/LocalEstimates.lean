/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.Constants
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Local estimates for the Euler-bias branch

The stochastic inputs are integral-equation and Itô/Fubini representations, not error rates.
The time integrals below take values in an arbitrary Banach space, in particular the genuine
`Lp (State d) 2 μ` space. Thus their norm estimates are deterministic Bochner-integral estimates.
The first lemmas also work directly with random variables and Mathlib's `lpNorm`.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open MeasureTheory Set
open scoped ENNReal

private theorem lpNorm_real_mul_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    lpNorm (fun ω ↦ c * f ω) 2 μ = c * lpNorm f 2 μ := by
  have heq : (c • f) = (fun ω ↦ c * f ω) := by funext ω; rfl
  simpa [heq, Real.norm_eq_abs, abs_of_nonneg hc] using
    (lpNorm_const_smul c f μ (p := 2))

/-- A spatial Lipschitz bound passes to the actual `L²` norm of two random states. -/
theorem drift_spatial_lpNorm_le
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E → E) (X Y : Ω → E) {L : ℝ} (hL : 0 ≤ L)
    (hXY : MemLp (fun ω ↦ X ω - Y ω) 2 μ)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) :
    lpNorm (fun ω ↦ b (X ω) - b (Y ω)) 2 μ ≤
      L * lpNorm (fun ω ↦ X ω - Y ω) 2 μ := by
  have h := lpNorm_mono_real (hXY.norm.const_mul L)
    (fun ω ↦ hLip (X ω) (Y ω))
  rw [lpNorm_real_mul_nonneg _ hL,
    lpNorm_norm hXY.aestronglyMeasurable 2] at h
  exact h

/-- The drift growth estimate in `L²`, with the origin constant and the actual state norm. -/
theorem drift_growth_lpNorm_le
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E → E) (X : Ω → E) {K0 L : ℝ}
    (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hX : MemLp X 2 μ)
    (hgrowth : ∀ x, ‖b x‖ ≤ K0 + L * ‖x‖) :
    lpNorm (fun ω ↦ b (X ω)) 2 μ ≤ K0 + L * lpNorm X 2 μ := by
  have henv : MemLp (fun ω ↦ K0 + L * ‖X ω‖) 2 μ :=
    (memLp_const K0).add (hX.norm.const_mul L)
  have hmono := lpNorm_mono_real henv (fun ω ↦ hgrowth (X ω))
  have hadd := lpNorm_add_le (memLp_const K0 : MemLp (fun _ : Ω ↦ K0) 2 μ)
    (g := fun ω ↦ L * ‖X ω‖) (by norm_num)
  rw [show ((fun _ : Ω ↦ K0) + fun ω ↦ L * ‖X ω‖) =
    (fun ω ↦ K0 + L * ‖X ω‖) from rfl] at hadd
  calc
    lpNorm (fun ω ↦ b (X ω)) 2 μ ≤ lpNorm (fun ω ↦ K0 + L * ‖X ω‖) 2 μ := hmono
    _ ≤ K0 + L * lpNorm X 2 μ := by
      simpa [Pi.add_apply, lpNorm_real_mul_nonneg _ hL,
        lpNorm_norm hX.aestronglyMeasurable 2, lpNorm_const',
        Real.norm_eq_abs, abs_of_nonneg hK0] using hadd

/-- Time regularity of the drift, evaluated at a random state, without assuming a local
remainder estimate. The exponent factor may be `sqrt (s-t)` or `s-t`. -/
theorem drift_time_lpNorm_le
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b c : E → E) (X : Ω → E) {H δ : ℝ}
    (hH : 0 ≤ H) (hδ : 0 ≤ δ) (hX : MemLp X 2 μ)
    (htime : ∀ x, ‖b x - c x‖ ≤ H * (1 + ‖x‖) * δ) :
    lpNorm (fun ω ↦ b (X ω) - c (X ω)) 2 μ ≤
      H * (1 + lpNorm X 2 μ) * δ := by
  have henv : MemLp (fun ω ↦ (H * δ) * (1 + ‖X ω‖)) 2 μ :=
    ((memLp_const (1 : ℝ)).add hX.norm).const_mul (H * δ)
  have hmono := lpNorm_mono_real henv (f := fun ω ↦ b (X ω) - c (X ω))
    (fun ω ↦ by simpa [mul_assoc, mul_left_comm, mul_comm] using htime (X ω))
  have hadd := lpNorm_add_le (memLp_const (1 : ℝ) : MemLp (fun _ : Ω ↦ (1 : ℝ)) 2 μ)
    (g := fun ω ↦ ‖X ω‖) (by norm_num)
  rw [show ((fun _ : Ω ↦ (1 : ℝ)) + fun ω ↦ ‖X ω‖) =
    (fun ω ↦ 1 + ‖X ω‖) from rfl] at hadd
  have hone : lpNorm (fun ω : Ω ↦ (1 : ℝ) + ‖X ω‖) 2 μ ≤ 1 + lpNorm X 2 μ := by
    simpa [Pi.add_apply, lpNorm_norm hX.aestronglyMeasurable 2, lpNorm_const'] using hadd
  calc
    lpNorm (fun ω ↦ b (X ω) - c (X ω)) 2 μ ≤
        lpNorm (fun ω ↦ (H * δ) * (1 + ‖X ω‖)) 2 μ := hmono
    _ = (H * δ) * lpNorm (fun ω ↦ 1 + ‖X ω‖) 2 μ :=
      lpNorm_real_mul_nonneg _ (mul_nonneg hH hδ)
    _ ≤ (H * δ) * (1 + lpNorm X 2 μ) :=
      mul_le_mul_of_nonneg_left hone (mul_nonneg hH hδ)
    _ = H * (1 + lpNorm X 2 μ) * δ := by ring

/-- Spatial and temporal drift differences combine to give the local half-order envelope.
The state moment and time increment bounds are kept separate from the drift assumptions. -/
theorem drift_increment_lpNorm_le
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b c : E → E) (X Y : Ω → E) {L H CX Cinc δ : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hXY : MemLp (fun ω ↦ X ω - Y ω) 2 μ) (hY : MemLp Y 2 μ)
    (hspaceMem : MemLp (fun ω ↦ b (X ω) - b (Y ω)) 2 μ)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (htime : ∀ x, ‖b x - c x‖ ≤ H * (1 + ‖x‖) * δ)
    (hstate : lpNorm Y 2 μ ≤ CX)
    (hinc : lpNorm (fun ω ↦ X ω - Y ω) 2 μ ≤ Cinc * δ) :
    lpNorm (fun ω ↦ b (X ω) - c (Y ω)) 2 μ ≤
      (L * Cinc + H * (1 + CX)) * δ := by
  have htri := lpNorm_add_le hspaceMem
    (g := fun ω ↦ b (Y ω) - c (Y ω)) (by norm_num)
  have heq : ((fun ω ↦ b (X ω) - b (Y ω)) +
      (fun ω ↦ b (Y ω) - c (Y ω))) =
      (fun ω ↦ b (X ω) - c (Y ω)) := by
    funext ω
    simp
  rw [heq] at htri
  have hspatial := drift_spatial_lpNorm_le b X Y hL hXY hLip
  have htemporal := drift_time_lpNorm_le b c Y hH hδ hY htime
  have hs := mul_le_mul_of_nonneg_left hinc hL
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_left hstate 1) hH) hδ
  calc
    lpNorm (fun ω ↦ b (X ω) - c (Y ω)) 2 μ ≤
      lpNorm (fun ω ↦ b (X ω) - b (Y ω)) 2 μ +
        lpNorm (fun ω ↦ b (Y ω) - c (Y ω)) 2 μ := htri
    _ ≤ (L * Cinc + H * (1 + CX)) * δ := by nlinarith

/-- The `L²` bound for the frozen spatial generator in the order-one Itô formula.
The operator bound and covariance-trace bound are stated pointwise, rather than assuming
the bound for the integrated remainder. -/
theorem frozen_generator_lpNorm_le
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E → E) (X : Ω → E) (A : Ω → E →L[ℝ] E) (trace : Ω → E)
    {K0 L B2 sigmaHS CX : ℝ}
    (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hX : MemLp X 2 μ) (hbX : MemLp (fun ω ↦ b (X ω)) 2 μ)
    (hAX : MemLp (fun ω ↦ A ω (b (X ω))) 2 μ)
    (hgrowth : ∀ x, ‖b x‖ ≤ K0 + L * ‖x‖)
    (hA : ∀ ω, ‖A ω‖ ≤ L)
    (htrace : ∀ ω, ‖trace ω‖ ≤ B2 * sigmaHS ^ 2)
    (hstate : lpNorm X 2 μ ≤ CX) :
    lpNorm (fun ω ↦ A ω (b (X ω)) + (1 / 2 : ℝ) • trace ω) 2 μ ≤
      L * (K0 + L * CX) + (1 / 2 : ℝ) * B2 * sigmaHS ^ 2 := by
  have hact := lpNorm_mono_real (hbX.norm.const_mul L)
    (f := fun ω ↦ A ω (b (X ω))) (fun ω ↦
      (A ω).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (hA ω) (norm_nonneg _)))
  rw [lpNorm_real_mul_nonneg _ hL,
    lpNorm_norm hbX.aestronglyMeasurable 2] at hact
  have htr := lpNorm_mono_real
    (memLp_const (B2 * sigmaHS ^ 2) : MemLp (fun _ : Ω ↦ B2 * sigmaHS ^ 2) 2 μ)
    htrace
  have htr' : lpNorm trace 2 μ ≤ B2 * sigmaHS ^ 2 := by
    simpa [lpNorm_const', Real.norm_eq_abs,
      abs_of_nonneg hB2,
      abs_of_nonneg (mul_nonneg hB2 (sq_nonneg sigmaHS))] using htr
  have hsum := lpNorm_add_le hAX (g := (1 / 2 : ℝ) • trace) (by norm_num)
  have heq : ((fun ω ↦ A ω (b (X ω))) + (1 / 2 : ℝ) • trace) =
      (fun ω ↦ A ω (b (X ω)) + (1 / 2 : ℝ) • trace ω) := by funext ω; rfl
  rw [heq, lpNorm_const_smul] at hsum
  norm_num at hsum
  have hgrowthLp := drift_growth_lpNorm_le b X hK0 hL hX hgrowth
  have hgrowthBound : lpNorm (fun ω ↦ b (X ω)) 2 μ ≤ K0 + L * CX :=
    hgrowthLp.trans (by gcongr)
  have hact' := hact.trans (mul_le_mul_of_nonneg_left hgrowthBound hL)
  nlinarith

section TimeIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact integral of the square-root envelope, including a zero length interval. -/
theorem integral_sqrt_sub_eq {t h : ℝ} (hh : 0 ≤ h) :
    (∫ s in t..t + h, Real.sqrt (s - t)) = (2 / 3 : ℝ) * h * Real.sqrt h := by
  rw [intervalIntegral.integral_comp_sub_right]
  simp only [sub_self, add_sub_cancel_left]
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
  have hexp : (1 / 2 : ℝ) + 1 = 1 + 1 / 2 := by ring
  rw [hexp, Real.rpow_add_of_nonneg hh (by norm_num) (by norm_num)]
  norm_num [Real.rpow_one]
  ring

/-- The half-order local remainder estimate is proved by integration of its drift envelope.
Instantiate `E` with `Lp (State d) 2 μ` for the probabilistic application. -/
theorem half_local_remainder_bound
    {t h D : ℝ} (hh : 0 ≤ h) (f : ℝ → E)
    (hf : IntervalIntegrable f volume t (t + h))
    (hbound : ∀ s ∈ Icc t (t + h), ‖f s‖ ≤ D * Real.sqrt (s - t)) :
    ‖∫ s in t..t + h, f s‖ ≤ (2 / 3 : ℝ) * D * h * Real.sqrt h := by
  have henv : IntervalIntegrable (fun s ↦ D * Real.sqrt (s - t)) volume t (t + h) :=
    (continuous_const.mul
      (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
  calc
    ‖∫ s in t..t + h, f s‖ ≤ ∫ s in t..t + h, ‖f s‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ s in t..t + h, D * Real.sqrt (s - t) :=
      intervalIntegral.integral_mono_on (by linarith) hf.norm henv hbound
    _ = (2 / 3 : ℝ) * D * h * Real.sqrt h := by
      rw [intervalIntegral.integral_const_mul, integral_sqrt_sub_eq hh]
      ring

/-- The increment constant is derived from an integral-equation representation and the
Itô-isometry bound on its additive-noise increment. -/
theorem state_increment_of_integral_eq
    {T K0 L initialNorm sigmaHS δ : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (hδ : 0 ≤ δ) (hδT : δ ≤ T) (t : ℝ)
    (Xs Xt noise : E) (drift : ℝ → E)
    (hEq : Xs - Xt = (∫ s in t..t + δ, drift s) + noise)
    (hdrift : ∀ s ∈ Icc t (t + δ), ‖drift s‖ ≤
      K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS)
    (hnoise : ‖noise‖ ≤ sigmaHS * Real.sqrt δ) :
    ‖Xs - Xt‖ ≤ incrementConstant T K0 L initialNorm sigmaHS * Real.sqrt δ := by
  have hD : 0 ≤ K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS :=
    add_nonneg hK0 (mul_nonneg hL
      (stateMomentConstant_nonneg hT hK0 hinitial hsigma))
  have hint : ‖∫ s in t..t + δ, drift s‖ ≤
      (K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS) * δ := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + δ) (f := drift) (fun s hs ↦
        hdrift s ⟨(uIoc_of_le (by linarith : t ≤ t + δ) ▸ hs).1.le,
          (uIoc_of_le (by linarith : t ≤ t + δ) ▸ hs).2⟩)
    simpa [abs_of_nonneg hδ, mul_comm] using hb
  have hsqrt := Real.sqrt_le_sqrt hδT
  have hδbound : δ ≤ Real.sqrt T * Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ, Real.sqrt_nonneg δ]
  rw [hEq]
  calc
    ‖(∫ s in t..t + δ, drift s) + noise‖ ≤
        ‖∫ s in t..t + δ, drift s‖ + ‖noise‖ := norm_add_le _ _
    _ ≤ (K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS) * δ +
        sigmaHS * Real.sqrt δ := add_le_add hint hnoise
    _ ≤ incrementConstant T K0 L initialNorm sigmaHS * Real.sqrt δ := by
      unfold incrementConstant
      nlinarith [mul_le_mul_of_nonneg_left hδbound hD]

/-- Integration of a linear time-increment envelope. -/
theorem linear_local_integral_bound
    {t h D : ℝ} (hh : 0 ≤ h) (f : ℝ → E)
    (hf : IntervalIntegrable f volume t (t + h))
    (hbound : ∀ s ∈ Icc t (t + h), ‖f s‖ ≤ D * (s - t)) :
    ‖∫ s in t..t + h, f s‖ ≤ D * h ^ 2 / 2 := by
  have henv : IntervalIntegrable (fun s ↦ D * (s - t)) volume t (t + h) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  calc
    ‖∫ s in t..t + h, f s‖ ≤ ∫ s in t..t + h, ‖f s‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ s in t..t + h, D * (s - t) :=
      intervalIntegral.integral_mono_on (by linarith) hf.norm henv hbound
    _ = D * h ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (f := fun x : ℝ ↦ x)]
      simp only [sub_self, add_sub_cancel_left, integral_id,
        zero_pow (by norm_num : 2 ≠ 0), sub_zero]
      ring

/-- The frozen spatial generator is multiplied by the Fubini weight `t+h-s`. -/
theorem weighted_local_integral_bound
    {t h D : ℝ} (hh : 0 ≤ h) (f : ℝ → E)
    (hf : IntervalIntegrable (fun s ↦ (t + h - s) • f s) volume t (t + h))
    (hbound : ∀ s ∈ Icc t (t + h), ‖f s‖ ≤ D) :
    ‖∫ s in t..t + h, (t + h - s) • f s‖ ≤ D * h ^ 2 / 2 := by
  have henv : IntervalIntegrable (fun s ↦ D * (t + h - s)) volume t (t + h) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  calc
    ‖∫ s in t..t + h, (t + h - s) • f s‖ ≤
        ∫ s in t..t + h, ‖(t + h - s) • f s‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ s in t..t + h, D * (t + h - s) := by
      apply intervalIntegral.integral_mono_on (by linarith) hf.norm henv
      intro s hs
      have hw : 0 ≤ t + h - s := sub_nonneg.mpr hs.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hbound s hs) hw
    _ = D * h ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (f := fun x : ℝ ↦ x)]
      simp only [add_sub_cancel_left, sub_self, integral_id,
        zero_pow (by norm_num : 2 ≠ 0), sub_zero]
      ring

/-- The deterministic part of the Itô/Fubini remainder has the paper's `C_A h²` bound.
Only the local decomposition and its two integrand estimates are supplied as inputs. -/
theorem order_one_local_remainder_bound
    {T K0 L B2 Lt initialNorm sigmaHS t h : ℝ}
    (hh : 0 ≤ h) (A : E) (temporal generator : ℝ → E)
    (htemporal : IntervalIntegrable temporal volume t (t + h))
    (hgenerator : IntervalIntegrable (fun s ↦ (t + h - s) • generator s)
      volume t (t + h))
    (hEq : A = (∫ s in t..t + h, temporal s) +
      (∫ s in t..t + h, (t + h - s) • generator s))
    (htime : ∀ s ∈ Icc t (t + h), ‖temporal s‖ ≤
      (Lt * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) * (s - t))
    (hgen : ∀ s ∈ Icc t (t + h), ‖generator s‖ ≤
      L * (K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS) +
        (1 / 2 : ℝ) * B2 * sigmaHS ^ 2) :
    ‖A‖ ≤ driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS * h ^ 2 := by
  have ht := linear_local_integral_bound hh temporal htemporal htime
  have hg := weighted_local_integral_bound hh generator hgenerator hgen
  rw [hEq]
  calc
    ‖(∫ s in t..t + h, temporal s) +
        (∫ s in t..t + h, (t + h - s) • generator s)‖ ≤
        ‖∫ s in t..t + h, temporal s‖ +
          ‖∫ s in t..t + h, (t + h - s) • generator s‖ := norm_add_le _ _
    _ ≤ (Lt * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) * h ^ 2 / 2 +
        (L * (K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS) +
          (1 / 2 : ℝ) * B2 * sigmaHS ^ 2) * h ^ 2 / 2 := add_le_add ht hg
    _ = driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS * h ^ 2 := by
      unfold driftRemainderConstant
      ring

end TimeIntegral

section RandomRemainder

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The half-order local estimate for a genuine random remainder. The representation premise
is an equality in `L²`, as supplied by the usual deterministic Bochner/Fubini theorem. -/
theorem half_local_remainder_lpNorm_bound
    {t h D : ℝ} (hh : 0 ≤ h) (R : Ω → E) (hR : MemLp R 2 μ)
    (f : ℝ → Lp E 2 μ) (hf : IntervalIntegrable f volume t (t + h))
    (hRep : hR.toLp R = ∫ s in t..t + h, f s)
    (hbound : ∀ s ∈ Icc t (t + h), ‖f s‖ ≤ D * Real.sqrt (s - t)) :
    lpNorm R 2 μ ≤ (2 / 3 : ℝ) * D * h * Real.sqrt h := by
  change (eLpNorm R 2 μ).toReal ≤ _
  rw [← Lp.norm_toLp R hR, hRep]
  exact half_local_remainder_bound hh f hf hbound

/-- The actual random-state increment bound from its `L²` integral-equation representation. -/
theorem state_increment_lpNorm_of_integral_eq
    {T K0 L initialNorm sigmaHS δ : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (hδ : 0 ≤ δ) (hδT : δ ≤ T) (t : ℝ)
    (Xs Xt : Ω → E) (hdiff : MemLp (fun ω ↦ Xs ω - Xt ω) 2 μ)
    (noise : Lp E 2 μ) (drift : ℝ → Lp E 2 μ)
    (hEq : hdiff.toLp (fun ω ↦ Xs ω - Xt ω) =
      (∫ s in t..t + δ, drift s) + noise)
    (hdrift : ∀ s ∈ Icc t (t + δ), ‖drift s‖ ≤
      K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS)
    (hnoise : ‖noise‖ ≤ sigmaHS * Real.sqrt δ) :
    lpNorm (fun ω ↦ Xs ω - Xt ω) 2 μ ≤
      incrementConstant T K0 L initialNorm sigmaHS * Real.sqrt δ := by
  change (eLpNorm (fun ω ↦ Xs ω - Xt ω) 2 μ).toReal ≤ _
  rw [← Lp.norm_toLp _ hdiff]
  have heq' : hdiff.toLp (fun ω ↦ Xs ω - Xt ω) - 0 =
      (∫ s in t..t + δ, drift s) + noise := by simpa using hEq
  simpa using state_increment_of_integral_eq hT hK0 hL hinitial hsigma hδ hδT t
    (hdiff.toLp (fun ω ↦ Xs ω - Xt ω)) 0 noise drift heq' hdrift hnoise

/-- The first-order local deterministic remainder bound for an actual random variable.
Only the Itô/Fubini representation equality, not its integrated estimate, is external. -/
theorem order_one_local_remainder_lpNorm_bound
    {T K0 L B2 Lt initialNorm sigmaHS t h : ℝ}
    (hh : 0 ≤ h) (A : Ω → E) (hA : MemLp A 2 μ)
    (temporal generator : ℝ → Lp E 2 μ)
    (htemporal : IntervalIntegrable temporal volume t (t + h))
    (hgenerator : IntervalIntegrable (fun s ↦ (t + h - s) • generator s)
      volume t (t + h))
    (hEq : hA.toLp A = (∫ s in t..t + h, temporal s) +
      (∫ s in t..t + h, (t + h - s) • generator s))
    (htime : ∀ s ∈ Icc t (t + h), ‖temporal s‖ ≤
      (Lt * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) * (s - t))
    (hgen : ∀ s ∈ Icc t (t + h), ‖generator s‖ ≤
      L * (K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS) +
        (1 / 2 : ℝ) * B2 * sigmaHS ^ 2) :
    lpNorm A 2 μ ≤ driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS * h ^ 2 := by
  change (eLpNorm A 2 μ).toReal ≤ _
  rw [← Lp.norm_toLp A hA]
  exact order_one_local_remainder_bound hh (hA.toLp A) temporal generator
    htemporal hgenerator hEq htime hgen

end RandomRemainder

end

end TimeDependentLattice.Bias
