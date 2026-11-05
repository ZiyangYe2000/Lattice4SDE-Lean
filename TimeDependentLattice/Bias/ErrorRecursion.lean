/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.EulerBias
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Grid-maximum error estimates from local remainders

For the Euler application, `error i ω = X i ω - Y i ω` and `difference i ω` is
`b(t_i, X i ω) - b(t_i, Y i ω)`.  The results below derive the scalar Gronwall
recurrence from a telescoped vector error decomposition, spatial Lipschitz continuity,
and local stochastic remainder bounds.  The norm is the actual `L²` norm of the maximum
over all grid points, rather than an arbitrary scalar error sequence.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

/-- Maximum of `‖error i‖` over `0 ≤ i ≤ j`, represented recursively. -/
def gridMaxNorm {Ω E : Type*} [NormedAddCommGroup E]
    (error : ℕ → Ω → E) : ℕ → Ω → ℝ
  | 0, ω => ‖error 0 ω‖
  | j + 1, ω => max (gridMaxNorm error j ω) ‖error (j + 1) ω‖

theorem gridMaxNorm_nonneg {Ω E : Type*} [NormedAddCommGroup E]
    (error : ℕ → Ω → E) (j : ℕ) (ω : Ω) : 0 ≤ gridMaxNorm error j ω := by
  induction j with
  | zero => exact norm_nonneg _
  | succ j ih => exact le_trans ih (le_max_left _ _)

theorem norm_le_gridMaxNorm {Ω E : Type*} [NormedAddCommGroup E]
    (error : ℕ → Ω → E) {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    ‖error i ω‖ ≤ gridMaxNorm error j ω := by
  induction j with
  | zero => simpa only [Nat.le_zero.mp hij, gridMaxNorm] using (le_refl ‖error 0 ω‖)
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst i
        exact le_max_right _ _
      · exact (ih (Nat.le_of_lt_succ h)).trans (le_max_left _ _)

theorem gridMaxNorm_le {Ω E : Type*} [NormedAddCommGroup E]
    (error : ℕ → Ω → E) {j : ℕ} {ω : Ω} {C : ℝ}
    (h : ∀ i ≤ j, ‖error i ω‖ ≤ C) : gridMaxNorm error j ω ≤ C := by
  induction j with
  | zero => exact h 0 le_rfl
  | succ j ih =>
      exact max_le (ih (fun i hi => h i (hi.trans j.le_succ))) (h _ le_rfl)

theorem memLp_gridMaxNorm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {p : ℝ≥0∞}
    (error : ℕ → Ω → E) {j : ℕ} (h : ∀ i ≤ j, MemLp (error i) p μ) :
    MemLp (gridMaxNorm error j) p μ := by
  induction j with
  | zero => exact (h 0 le_rfl).norm
  | succ j ih =>
      exact (ih (fun i hi => h i (hi.trans j.le_succ))).sup (h _ le_rfl).norm

/-- The terminal `L²` error is bounded by the `L²` norm of the grid maximum. -/
theorem lpNorm_le_gridMaxNorm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} (error : ℕ → Ω → E) {j : ℕ}
    (h : ∀ i ≤ j, MemLp (error i) 2 μ) :
    lpNorm (error j) 2 μ ≤ lpNorm (gridMaxNorm error j) 2 μ :=
  lpNorm_mono_real (memLp_gridMaxNorm error h)
    (fun ω => norm_le_gridMaxNorm error le_rfl ω)

private theorem sum_range_mono_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    {i j : ℕ} (hij : i ≤ j) :
    ∑ k ∈ Finset.range i, f k ≤ ∑ k ∈ Finset.range j, f k := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun k _ _ => hf k)

/-- Pathwise discrete maximum estimate before taking any expectation. -/
theorem gridMaxNorm_le_local_remainders
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (error difference remainder martingale : ℕ → Ω → E)
    {m : ℕ} {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (ω : Ω) (hdecomp : ∀ j ≤ m,
      error j ω = h • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω) + martingale j ω)
    (hlip : ∀ i < m, ‖difference i ω‖ ≤ L * ‖error i ω‖)
    {j : ℕ} (hj : j ≤ m) :
    gridMaxNorm error j ω ≤
      L * h * (∑ i ∈ Finset.range j, gridMaxNorm error i ω) +
        (∑ i ∈ Finset.range j, ‖remainder i ω‖) +
        gridMaxNorm martingale j ω := by
  apply gridMaxNorm_le
  intro k hk
  rw [hdecomp k (hk.trans hj)]
  calc
    ‖h • (∑ i ∈ Finset.range k, difference i ω) +
        (∑ i ∈ Finset.range k, remainder i ω) + martingale k ω‖ ≤
      h * (∑ i ∈ Finset.range k, ‖difference i ω‖) +
        (∑ i ∈ Finset.range k, ‖remainder i ω‖) + ‖martingale k ω‖ := by
      calc
        _ ≤ ‖h • (∑ i ∈ Finset.range k, difference i ω) +
              (∑ i ∈ Finset.range k, remainder i ω)‖ + ‖martingale k ω‖ :=
          norm_add_le _ _
        _ ≤ (‖h • (∑ i ∈ Finset.range k, difference i ω)‖ +
              ‖∑ i ∈ Finset.range k, remainder i ω‖) + ‖martingale k ω‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ _ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
          gcongr <;> exact norm_sum_le _ _
    _ ≤ L * h * (∑ i ∈ Finset.range k, gridMaxNorm error i ω) +
        (∑ i ∈ Finset.range k, ‖remainder i ω‖) +
        gridMaxNorm martingale j ω := by
      have hd : (∑ i ∈ Finset.range k, ‖difference i ω‖) ≤
          L * ∑ i ∈ Finset.range k, gridMaxNorm error i ω := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        exact (hlip i ((Finset.mem_range.mp hi).trans_le (hk.trans hj))).trans
          (mul_le_mul_of_nonneg_left (norm_le_gridMaxNorm error le_rfl ω) hL)
      have hm := norm_le_gridMaxNorm martingale hk ω
      nlinarith [mul_le_mul_of_nonneg_left hd hh]
    _ ≤ _ := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left
            (sum_range_mono_nonneg (fun i => gridMaxNorm_nonneg error i ω) hk)
            (mul_nonneg hL hh))
          (sum_range_mono_nonneg (fun i => norm_nonneg (remainder i ω)) hk)) le_rfl

private theorem lpNorm_mono_real_ae {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E} {g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (h : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ g ω) :
    lpNorm f 2 μ ≤ lpNorm g 2 μ := by
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top
    (eLpNorm_mono_ae_real hf.aestronglyMeasurable h)

private theorem lpNorm_nonneg_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    lpNorm (fun ω => c * f ω) 2 μ = c * lpNorm f 2 μ := by
  simpa [Pi.smul_def, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hc] using
    (lpNorm_const_smul c f μ (p := (2 : ℝ≥0∞)))

/-- Minkowski's inequality turns the vector decomposition into the actual maximum-error
`L²` recurrence.  Both the decomposition and the spatial Lipschitz bound are only required
almost everywhere, as for stochastic processes. -/
theorem gridMaxNorm_lpNorm_le_remainders
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (error difference remainder martingale : ℕ → Ω → E)
    {m : ℕ} {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (herror : ∀ i ≤ m, MemLp (error i) 2 μ)
    (hrem : ∀ i < m, MemLp (remainder i) 2 μ)
    (hmart : ∀ i ≤ m, MemLp (martingale i) 2 μ)
    (hdecomp : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      error j ω = h • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω) + martingale j ω)
    (hlip : ∀ᵐ ω ∂μ, ∀ i < m, ‖difference i ω‖ ≤ L * ‖error i ω‖)
    {j : ℕ} (hj : j ≤ m) :
    lpNorm (gridMaxNorm error j) 2 μ ≤
      L * h * (∑ i ∈ Finset.range j, lpNorm (gridMaxNorm error i) 2 μ) +
        (∑ i ∈ Finset.range j, lpNorm (remainder i) 2 μ) +
        lpNorm (gridMaxNorm martingale j) 2 μ := by
  let U : Ω → ℝ := fun ω => ∑ i ∈ Finset.range j, gridMaxNorm error i ω
  let R : Ω → ℝ := fun ω => ∑ i ∈ Finset.range j, ‖remainder i ω‖
  let M : Ω → ℝ := gridMaxNorm martingale j
  have hu (i : ℕ) (hi : i ∈ Finset.range j) : MemLp (gridMaxNorm error i) 2 μ :=
    memLp_gridMaxNorm error (fun k hk => herror k
      (hk.trans ((Finset.mem_range.mp hi).le.trans hj)))
  have hr (i : ℕ) (hi : i ∈ Finset.range j) : MemLp (remainder i) 2 μ :=
    hrem i ((Finset.mem_range.mp hi).trans_le hj)
  have hU : MemLp U 2 μ := memLp_finsetSum _ hu
  have hR : MemLp R 2 μ := memLp_finsetSum _ (fun i hi => (hr i hi).norm)
  have hM : MemLp M 2 μ := memLp_gridMaxNorm martingale
    (fun i hi => hmart i (hi.trans hj))
  have hdom : ∀ᵐ ω ∂μ, ‖gridMaxNorm error j ω‖ ≤ L * h * U ω + R ω + M ω := by
    filter_upwards [hdecomp, hlip] with ω hd hl
    rw [Real.norm_eq_abs, abs_of_nonneg (gridMaxNorm_nonneg error j ω)]
    exact gridMaxNorm_le_local_remainders error difference remainder martingale
      hh hL ω hd hl hj
  have hbound := lpNorm_mono_real_ae
    (memLp_gridMaxNorm error (fun i hi => herror i (hi.trans hj)))
    (((hU.const_mul (L * h)).add hR).add hM) hdom
  have htriangle :
      lpNorm (fun ω => L * h * U ω + R ω + M ω) 2 μ ≤
        L * h * lpNorm U 2 μ + lpNorm R 2 μ + lpNorm M 2 μ := by
    calc
      _ ≤ lpNorm (fun ω => L * h * U ω + R ω) 2 μ + lpNorm M 2 μ :=
        lpNorm_add_le ((hU.const_mul (L * h)).add hR) (by norm_num)
      _ ≤ (lpNorm (fun ω => L * h * U ω) 2 μ + lpNorm R 2 μ) +
          lpNorm M 2 μ := by
        gcongr
        exact lpNorm_add_le (hU.const_mul (L * h)) (by norm_num)
      _ = _ := by rw [lpNorm_nonneg_mul μ U (mul_nonneg hL hh)]
  have hUsum : lpNorm U 2 μ ≤
      ∑ i ∈ Finset.range j, lpNorm (gridMaxNorm error i) 2 μ := by
    have hUeq : U = ∑ i ∈ Finset.range j, gridMaxNorm error i := by
      ext ω
      simp [U]
    rw [hUeq]
    exact lpNorm_sum_le hu (by norm_num)
  have hRsum : lpNorm R 2 μ ≤
      ∑ i ∈ Finset.range j, lpNorm (remainder i) 2 μ := by
    have hReq : R = ∑ i ∈ Finset.range j, fun ω => ‖remainder i ω‖ := by
      ext ω
      simp [R]
    rw [hReq]
    calc
      _ ≤ ∑ i ∈ Finset.range j, lpNorm (fun ω => ‖remainder i ω‖) 2 μ :=
        lpNorm_sum_le (fun i hi => (hr i hi).norm) (by norm_num)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact lpNorm_norm (hr i hi).aestronglyMeasurable 2
  exact (hbound.trans htriangle).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hUsum (mul_nonneg hL hh))
      hRsum) le_rfl)

/-- Uniform local remainder estimates give a Gronwall recurrence; this theorem derives the
recurrence from vector identities rather than taking it as a hypothesis. -/
theorem gridMaxNorm_recurrence_of_local_bounds
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (error difference remainder martingale : ℕ → Ω → E)
    {m : ℕ} {h L localBound martingaleBound : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hlocal0 : 0 ≤ localBound)
    (herror : ∀ i ≤ m, MemLp (error i) 2 μ)
    (hrem : ∀ i < m, MemLp (remainder i) 2 μ)
    (hmart : ∀ i ≤ m, MemLp (martingale i) 2 μ)
    (hdecomp : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      error j ω = h • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω) + martingale j ω)
    (hlip : ∀ᵐ ω ∂μ, ∀ i < m, ‖difference i ω‖ ≤ L * ‖error i ω‖)
    (hlocal : ∀ i < m, lpNorm (remainder i) 2 μ ≤ localBound)
    (hmartBound : ∀ j ≤ m, lpNorm (gridMaxNorm martingale j) 2 μ ≤ martingaleBound)
    {j : ℕ} (hj : j ≤ m) :
    lpNorm (gridMaxNorm error j) 2 μ ≤
      (m : ℝ) * localBound + martingaleBound +
        L * h * (∑ i ∈ Finset.range j, lpNorm (gridMaxNorm error i) 2 μ) := by
  have hrec := gridMaxNorm_lpNorm_le_remainders μ error difference remainder martingale
    hh hL herror hrem hmart hdecomp hlip hj
  have hsum : (∑ i ∈ Finset.range j, lpNorm (remainder i) 2 μ) ≤
      (m : ℝ) * localBound := by
    calc
      _ ≤ ∑ _i ∈ Finset.range j, localBound := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlocal i ((Finset.mem_range.mp hi).trans_le hj)
      _ = (j : ℝ) * localBound := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hlocal0
  linarith [hmartBound j hj]

@[simp] theorem gridMaxNorm_zero {Ω E : Type*} [NormedAddCommGroup E] (j : ℕ) :
    gridMaxNorm (fun _ (_ : Ω) => (0 : E)) j = 0 := by
  funext ω
  induction j with
  | zero => simp [gridMaxNorm]
  | succ j ih => simp [gridMaxNorm, ih]

/-- The square-root conversion used when presenting the grid step as `m^(-1/2)`. -/
theorem sqrt_step_eq_rate {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m) :
    Real.sqrt (T / (m : ℝ)) = Real.sqrt T * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_div hT, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- Paper Theorem 3.7, for the genuine `L²` grid maximum and local half-order remainders.
The stochastic input is the one-step remainder bound, not a scalar error recurrence. -/
theorem euler_strong_half_from_local_remainders
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (error difference remainder : ℕ → Ω → E)
    {m : ℕ} (hm : 0 < m) {T K0 L Ht initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (herror : ∀ i ≤ m, MemLp (error i) 2 μ)
    (hrem : ∀ i < m, MemLp (remainder i) 2 μ)
    (hdecomp : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      error j ω = (T / (m : ℝ)) • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω))
    (hlip : ∀ᵐ ω ∂μ, ∀ i < m, ‖difference i ω‖ ≤ L * ‖error i ω‖)
    (hlocal : ∀ i < m, lpNorm (remainder i) 2 μ ≤
      (2 / 3 : ℝ) *
        (L * incrementConstant T K0 L initialNorm sigmaHS +
          Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) *
        (T / (m : ℝ)) * Real.sqrt (T / (m : ℝ))) :
    lpNorm (gridMaxNorm error m) 2 μ ≤
      strongHalfConstant T K0 L Ht initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  apply euler_strong_half_of_recurrence hm hT hK0 hL hHt hinitial hsigma
    (fun j => lpNorm (gridMaxNorm error j) 2 μ) (fun _ => lpNorm_nonneg)
  intro j hj
  have hd : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      error j ω = (T / (m : ℝ)) • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω) + (0 : E) := by
    simpa only [add_zero] using hdecomp
  have hrec := gridMaxNorm_recurrence_of_local_bounds (martingaleBound := 0)
    μ error difference remainder
    (fun _ _ => 0) (by positivity : 0 ≤ T / (m : ℝ)) hL
    (by positivity [stateMomentConstant_nonneg (L := L) hT hK0 hinitial hsigma,
      incrementConstant_nonneg hT hK0 hL hinitial hsigma])
    herror hrem (fun _ _ => by simp) hd hlip hlocal
    (fun _ _ => by simp) hj
  have hscalar : (m : ℝ) *
      ((2 / 3 : ℝ) *
        (L * incrementConstant T K0 L initialNorm sigmaHS +
          Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) *
        (T / (m : ℝ)) * Real.sqrt (T / (m : ℝ))) + 0 =
      (2 / 3 : ℝ) * T * Real.sqrt T *
        (L * incrementConstant T K0 L initialNorm sigmaHS +
          Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS)) *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [sqrt_step_eq_rate hT hm]
    field_simp
    ring
  rw [hscalar] at hrec
  simpa only [mul_div_assoc] using hrec

/-- Paper Theorem 3.8 from one-step deterministic remainders and a maximal martingale
estimate (the standard Doob/Itô input).  It controls the maximum on the full Euler grid. -/
theorem euler_strong_one_from_local_remainders
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (error difference remainder martingale : ℕ → Ω → E)
    {m : ℕ} (hm : 0 < m) {T K0 L B2 Lt initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hLt : 0 ≤ Lt) (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (herror : ∀ i ≤ m, MemLp (error i) 2 μ)
    (hrem : ∀ i < m, MemLp (remainder i) 2 μ)
    (hmart : ∀ i ≤ m, MemLp (martingale i) 2 μ)
    (hdecomp : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      error j ω = (T / (m : ℝ)) • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω) + martingale j ω)
    (hlip : ∀ᵐ ω ∂μ, ∀ i < m, ‖difference i ω‖ ≤ L * ‖error i ω‖)
    (hlocal : ∀ i < m, lpNorm (remainder i) 2 μ ≤
      driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS * (T / (m : ℝ)) ^ 2)
    (hmartBound : ∀ j ≤ m, lpNorm (gridMaxNorm martingale j) 2 μ ≤
      2 * L * sigmaHS * Real.sqrt (T / 3) * (T / (m : ℝ))) :
    lpNorm (gridMaxNorm error m) 2 μ ≤
      T * strongOneConstant T K0 L B2 Lt initialNorm sigmaHS *
        (m : ℝ) ^ (-(1 : ℝ)) := by
  apply euler_strong_one_of_recurrence hm hT hK0 hL hB2 hLt hinitial hsigma
    (fun j => lpNorm (gridMaxNorm error j) 2 μ) (fun _ => lpNorm_nonneg)
  intro j hj
  have hrec := gridMaxNorm_recurrence_of_local_bounds μ error difference remainder martingale
    (by positivity : 0 ≤ T / (m : ℝ)) hL
    (by positivity [driftRemainderConstant_nonneg hT hK0 hL hB2 hLt hinitial hsigma])
    herror hrem hmart hdecomp hlip hlocal hmartBound hj
  have hscalar : (m : ℝ) *
      (driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS * (T / (m : ℝ)) ^ 2) +
        2 * L * sigmaHS * Real.sqrt (T / 3) * (T / (m : ℝ)) =
      (T * driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS +
        2 * L * sigmaHS * Real.sqrt (T / 3)) * (T / (m : ℝ)) := by
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hscalar] at hrec
  simpa only [mul_div_assoc] using hrec

end
end TimeDependentLattice.Bias
