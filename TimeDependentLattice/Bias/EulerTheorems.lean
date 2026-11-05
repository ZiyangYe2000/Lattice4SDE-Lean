/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.CoupledBounds
import TimeDependentLattice.Bias.PayoffTransfer
import TimeDependentLattice.Bias.LocalAssembly
import TimeDependentLattice.Bias.DiffusionBounds
import TimeDependentLattice.Bias.StochasticEstimates

/-!
# Euler strong and payoff-bias theorems on the paper's uniform grid

The input records contain the standard SDE integral equation, state moments, and
Bochner/Itô representation identities.  They do not contain error recurrences, local
Euler rates, or payoff-transfer bounds.  Those estimates are deduced below.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory Set TimeDependentLattice.Euler TimeDependentLattice.Trees

/-- The paper's fixed uniform time grid, including the endpoint `t_m = T`. -/
def uniformEulerGrid (T : ℝ) (m i : ℕ) : ℝ := (i : ℝ) * (T / (m : ℝ))

@[simp] theorem uniformEulerGrid_zero (T : ℝ) (m : ℕ) : uniformEulerGrid T m 0 = 0 := by
  simp [uniformEulerGrid]

theorem uniformEulerGrid_step (T : ℝ) (m i : ℕ) :
    uniformEulerGrid T m (i + 1) - uniformEulerGrid T m i = T / (m : ℝ) := by
  simp only [uniformEulerGrid, Nat.cast_add, Nat.cast_one]
  ring

theorem uniformEulerGrid_terminal (T : ℝ) {m : ℕ} (hm : 0 < m) :
    uniformEulerGrid T m m = T := by
  unfold uniformEulerGrid
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

theorem uniformEulerGrid_mem {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {i : ℕ} (hi : i ≤ m) : uniformEulerGrid T m i ∈ Icc 0 T := by
  constructor
  · unfold uniformEulerGrid
    positivity
  · calc
      uniformEulerGrid T m i ≤ uniformEulerGrid T m m := by
        unfold uniformEulerGrid
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (by positivity)
      _ = T := uniformEulerGrid_terminal T hm

theorem uniformEulerGrid_interval_mem {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    {i : ℕ} (hi : i < m) {s : ℝ}
    (hs : s ∈ Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ))) :
    s ∈ Icc 0 T := by
  have hleft := uniformEulerGrid_mem hT hm hi.le
  have hright := uniformEulerGrid_mem hT hm (Nat.succ_le_of_lt hi)
  have hstep := uniformEulerGrid_step T m i
  constructor <;> linarith [hs.1, hs.2, hleft.1, hright.2]

/-- Standard existence/moment inputs for the coupled exact process and defined Euler chain.
The exponential-moment bound is the terminal consequence of paper Lemma E.2. -/
structure CoupledMomentInputs
    {Ω : Type*} [MeasurableSpace Ω] {stateDim : ℕ}
    (μ : Measure Ω) {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (m : ℕ) (K0 sigmaHS : ℝ)
    (x₀ : State stateDim) (noise X : ℝ → Ω → State stateDim) where
  steps_pos : 0 < m
  time_nonneg : 0 ≤ T
  origin_nonneg : 0 ≤ K0
  sigma_nonneg : 0 ≤ sigmaHS
  drift_origin : ∀ t ∈ Icc 0 T, ‖drift t 0‖ ≤ K0
  exact_memLp : ∀ s ∈ Icc 0 T, MemLp (X s) 2 μ
  exact_moment : ∀ s ∈ Icc 0 T, lpNorm (X s) 2 μ ≤
    stateMomentConstant T K0 bounds.driftLipschitzConstant ‖x₀‖ sigmaHS
  euler_memLp : ∀ i ≤ m,
    MemLp (coupledEulerChain drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise i) 2 μ
  solution_integrable : ∀ᵐ ω ∂μ, ∀ i < m,
    IntervalIntegrable (fun s ↦ drift s (X s ω)) volume
      (uniformEulerGrid T m i) (uniformEulerGrid T m (i + 1))
  solution_initial : ∀ᵐ ω ∂μ, X 0 ω = x₀
  solution_step : ∀ᵐ ω ∂μ, ∀ i < m,
    X (uniformEulerGrid T m (i + 1)) ω = X (uniformEulerGrid T m i) ω +
      (∫ s in uniformEulerGrid T m i..uniformEulerGrid T m (i + 1), drift s (X s ω)) +
        (noise (uniformEulerGrid T m (i + 1)) ω - noise (uniformEulerGrid T m i) ω)
  exact_exponential : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖X T ω‖)) μ
  euler_exponential : Integrable (fun ω ↦ Real.exp (2 * bounds.β *
    ‖coupledEulerChain drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise m ω‖)) μ
  joint_exponential :
    (∫ ω, Real.exp (2 * bounds.β * ‖X T ω‖) ∂μ) +
      (∫ ω, Real.exp (2 * bounds.β *
        ‖coupledEulerChain drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise m ω‖) ∂μ) ≤
      stateExponentialPrefactor (2 * bounds.β) T K0 bounds.driftLipschitzConstant sigmaHS *
        Real.exp (2 * bounds.β * Real.exp (bounds.driftLipschitzConstant * T) * ‖x₀‖)

/-- Standard `L²` representatives and Fubini identities for the half-order branch.
The temporal assumption is exactly the paper's one-half Hölder drift condition. -/
structure HalfOrderStochasticInputs
    {Ω : Type*} [MeasurableSpace Ω] {stateDim : ℕ}
    (μ : Measure Ω) {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (m : ℕ) (K0 Ht sigmaHS : ℝ)
    (x₀ : State stateDim) (noise X : ℝ → Ω → State stateDim)
    extends CoupledMomentInputs μ bounds m K0 sigmaHS x₀ noise X where
  holder_nonneg : 0 ≤ Ht
  time_holder : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x,
    ‖drift s x - drift t x‖ ≤ Ht * (1 + ‖x‖) * Real.sqrt |s - t|
  driftLp : ℝ → Lp (State stateDim) 2 μ
  noiseLp : ℕ → ℝ → Lp (State stateDim) 2 μ
  incrementLp : ℕ → ℝ → Lp (State stateDim) 2 μ
  deltaLp : ℕ → ℝ → Lp (State stateDim) 2 μ
  drift_rep : ∀ s ∈ Icc 0 T,
    (fun ω ↦ driftLp s ω) =ᵐ[μ] fun ω ↦ drift s (X s ω)
  increment_rep : ∀ i < m, ∀ s ∈
      Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)),
    (fun ω ↦ incrementLp i s ω) =ᵐ[μ]
      fun ω ↦ X s ω - X (uniformEulerGrid T m i) ω
  increment_eq : ∀ i < m, ∀ s ∈
      Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)),
    incrementLp i s = (∫ r in uniformEulerGrid T m i..s, driftLp r) + noiseLp i s
  noise_rep : ∀ i < m, ∀ s ∈
      Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)),
    (fun ω ↦ noiseLp i s ω) =ᵐ[μ]
      fun ω ↦ noise s ω - noise (uniformEulerGrid T m i) ω
  noise_isometry : ∀ i < m, ∀ s ∈
      Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)),
    (∫ ω, ‖noise s ω - noise (uniformEulerGrid T m i) ω‖ ^ 2 ∂μ) =
      sigmaHS ^ 2 * (s - uniformEulerGrid T m i)
  delta_rep : ∀ i < m, ∀ s ∈
      Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)),
    (fun ω ↦ deltaLp i s ω) =ᵐ[μ] fun ω ↦
      drift s (X s ω) - drift (uniformEulerGrid T m i) (X (uniformEulerGrid T m i) ω)
  delta_integrable : ∀ i < m, IntervalIntegrable (deltaLp i) volume
    (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ))
  remainderLp : ℕ → Lp (State stateDim) 2 μ
  remainder_rep : ∀ i < m, (fun ω ↦ remainderLp i ω) =ᵐ[μ]
    localDriftRemainder drift X (uniformEulerGrid T m) i
  remainder_eq : ∀ i < m, remainderLp i =
    ∫ s in uniformEulerGrid T m i..uniformEulerGrid T m i + T / (m : ℝ), deltaLp i s

private theorem toLp_eq_of_rep {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] (f : Ω → E) (hf : MemLp f 2 μ) (F : Lp E 2 μ)
    (hRep : (fun ω ↦ F ω) =ᵐ[μ] f) : hf.toLp f = F :=
  Lp.ext (hf.coeFn_toLp.trans hRep.symm)

/-- Itô's isometry for the actual additive-noise increment implies its `L²` bound. -/
theorem HalfOrderStochasticInputs.noise_increment
    {Ω : Type*} [MeasurableSpace Ω] {stateDim : ℕ} {μ : Measure Ω}
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Ht sigmaHS : ℝ}
    {bounds : GevreyBounds drift payoff T} {m : ℕ} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim}
    (data : HalfOrderStochasticInputs μ bounds m K0 Ht sigmaHS x₀ noise X)
    (i : ℕ) (hi : i < m) (s : ℝ)
    (hs : s ∈ Icc (uniformEulerGrid T m i)
      (uniformEulerGrid T m i + T / (m : ℝ))) :
    ‖data.noiseLp i s‖ ≤ sigmaHS * Real.sqrt (s - uniformEulerGrid T m i) := by
  have hmem : MemLp (fun ω ↦ noise s ω - noise (uniformEulerGrid T m i) ω) 2 μ :=
    (Lp.memLp (data.noiseLp i s)).ae_eq (data.noise_rep i hi s hs)
  rw [← toLp_eq_of_rep _ hmem (data.noiseLp i s) (data.noise_rep i hi s hs),
    Lp.norm_toLp]
  exact lpNorm_increment_le_of_isometry hmem data.sigma_nonneg
    (sub_nonneg.mpr hs.1) (data.noise_isometry i hi s hs)

theorem HalfOrderStochasticInputs.remainder_memLp
    {Ω : Type*} [MeasurableSpace Ω] {stateDim : ℕ} {μ : Measure Ω}
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Ht sigmaHS : ℝ}
    {bounds : GevreyBounds drift payoff T} {m : ℕ} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim}
    (data : HalfOrderStochasticInputs μ bounds m K0 Ht sigmaHS x₀ noise X)
    {i : ℕ} (hi : i < m) :
    MemLp (localDriftRemainder drift X (uniformEulerGrid T m) i) 2 μ :=
  (Lp.memLp (data.remainderLp i)).ae_eq (data.remainder_rep i hi)

/-- The actual one-step half-order remainder follows from the source data. -/
theorem HalfOrderStochasticInputs.local_bound
    {Ω : Type*} [MeasurableSpace Ω] {stateDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Ht sigmaHS : ℝ}
    {bounds : GevreyBounds drift payoff T} {m : ℕ} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim}
    (data : HalfOrderStochasticInputs μ bounds m K0 Ht sigmaHS x₀ noise X)
    {i : ℕ} (hi : i < m) :
    lpNorm (localDriftRemainder drift X (uniformEulerGrid T m) i) 2 μ ≤
      (2 / 3 : ℝ) *
        (bounds.driftLipschitzConstant *
            incrementConstant T K0 bounds.driftLipschitzConstant ‖x₀‖ sigmaHS +
          Ht * (1 + stateMomentConstant T K0 bounds.driftLipschitzConstant ‖x₀‖ sigmaHS)) *
        (T / (m : ℝ)) * Real.sqrt (T / (m : ℝ)) := by
  have hh : 0 ≤ T / (m : ℝ) := div_nonneg data.time_nonneg (Nat.cast_nonneg m)
  have hhT : T / (m : ℝ) ≤ T := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast data.steps_pos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast data.steps_pos
    apply (div_le_iff₀ hm0).2
    nlinarith [data.time_nonneg]
  have hinterval : ∀ {s : ℝ},
      s ∈ Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)) →
        s ∈ Icc 0 T := fun {_} hs =>
    uniformEulerGrid_interval_mem data.time_nonneg data.steps_pos hi hs
  have hstart := uniformEulerGrid_mem data.time_nonneg data.steps_pos hi.le
  apply half_local_remainder_from_state_equation
    (driftLp := data.driftLp) (noiseLp := data.noiseLp i) (deltaLp := data.deltaLp i)
    (hR := data.remainder_memLp hi)
    data.time_nonneg data.origin_nonneg
    bounds.driftLipschitzConstant_pos.le data.holder_nonneg (norm_nonneg x₀)
    data.sigma_nonneg hh hhT X drift
    (fun s hs => data.exact_memLp s (hinterval hs))
    (fun s hs => data.exact_moment s (hinterval hs))
  · intro s hs x y
    exact drift_lipschitz_of_gevrey bounds (hinterval hs).1 (hinterval hs).2 x y
  · intro s hs x
    exact bounds.drift_norm_le_origin_add_lipschitz
      (fun t ht0 htT => data.drift_origin t ⟨ht0, htT⟩)
      (hinterval hs).1 (hinterval hs).2 x
  · intro s hs x
    simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using
      data.time_holder _ hstart s (hinterval hs) x
  · intro s hs
    exact data.drift_rep s (hinterval hs)
  · intro s hs
    rw [toLp_eq_of_rep _ _ (data.incrementLp i s) (data.increment_rep i hi s hs)]
    exact data.increment_eq i hi s hs
  · exact data.noise_increment i hi
  · exact data.delta_rep i hi
  · exact data.delta_integrable i hi
  · rw [toLp_eq_of_rep _ _ (data.remainderLp i) (data.remainder_rep i hi)]
    exact data.remainder_eq i hi

/-- Paper Theorem 3.7: the actual grid-maximum strong error, with every local estimate
derived from the SDE/Bochner and moment inputs. -/
theorem theorem3_7_coupled_strong
    {Ω : Type*} [MeasurableSpace Ω] {stateDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Ht sigmaHS : ℝ}
    {bounds : GevreyBounds drift payoff T} {m : ℕ} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim}
    (data : HalfOrderStochasticInputs μ bounds m K0 Ht sigmaHS x₀ noise X) :
    lpNorm (gridMaxNorm
      (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X) m) 2 μ ≤
      strongHalfConstant T K0 bounds.driftLipschitzConstant Ht ‖x₀‖ sigmaHS *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  apply coupledEuler_strong_half_of_local μ bounds (uniformEulerGrid T m) x₀ noise X
    data.steps_pos data.time_nonneg data.origin_nonneg data.holder_nonneg data.sigma_nonneg
  · exact fun i _ => uniformEulerGrid_step T m i
  · exact fun i hi => uniformEulerGrid_mem data.time_nonneg data.steps_pos hi.le
  · exact data.solution_integrable
  · simpa only [uniformEulerGrid_zero] using data.solution_initial
  · exact data.solution_step
  · exact fun i hi => data.exact_memLp _ (uniformEulerGrid_mem data.time_nonneg data.steps_pos hi)
  · exact data.euler_memLp
  · exact fun _ hi => data.remainder_memLp hi
  · exact fun _ hi => data.local_bound hi

/-- Paper Theorem 3.7: the actual expectation bias, obtained by the proved payoff transfer.
No payoff-difference inequality or Euler convergence rate is an input. -/
theorem theorem3_7_coupled_bias
    {Ω : Type*} [MeasurableSpace Ω] {stateDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Ht sigmaHS : ℝ}
    {bounds : GevreyBounds drift payoff T} {m : ℕ} {x₀ : State stateDim}
    {noise X : ℝ → Ω → State stateDim}
    (data : HalfOrderStochasticInputs μ bounds m K0 Ht sigmaHS x₀ noise X) :
    |(∫ ω, payoff (coupledEulerChain drift (uniformEulerGrid T m)
        (T / (m : ℝ)) x₀ noise m ω) ∂μ) - (∫ ω, payoff (X T ω) ∂μ)| ≤
      biasHalfConstant bounds.G₀ bounds.G₁ bounds.β T K0 bounds.driftLipschitzConstant
        Ht ‖x₀‖ sigmaHS * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hX := data.exact_memLp T ⟨data.time_nonneg, le_rfl⟩
  have hpay := payoff_integral_sub_le_payoffDifferenceConstant bounds hX
    (data.euler_memLp m le_rfl) data.exact_exponential data.euler_exponential
    data.joint_exponential
  have herr : ∀ i ≤ m, MemLp
      (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X i) 2 μ := by
    intro i hi
    exact (data.exact_memLp _ (uniformEulerGrid_mem data.time_nonneg data.steps_pos hi)).sub
      (data.euler_memLp i hi)
  have hterminal := lpNorm_le_gridMaxNorm
    (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X) herr
  have hsymm : lpNorm (fun ω => coupledEulerChain drift (uniformEulerGrid T m)
      (T / (m : ℝ)) x₀ noise m ω - X T ω) 2 μ =
      lpNorm (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X m) 2 μ := by
    rw [show coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X m =
      fun ω => X T ω - coupledEulerChain drift (uniformEulerGrid T m) (T / (m : ℝ))
        x₀ noise m ω by
          funext ω
          simp only [coupledGridError, uniformEulerGrid_terminal T data.steps_pos]]
    exact lpNorm_sub_comm _ _ 2 μ
  rw [hsymm] at hpay
  refine hpay.trans ?_
  have h := mul_le_mul_of_nonneg_left
    (hterminal.trans (theorem3_7_coupled_strong data))
    (payoffDifferenceConstant_nonneg (beta := bounds.β) (T := T) (K0 := K0)
      (L := bounds.driftLipschitzConstant) (initialNorm := ‖x₀‖) (sigmaHS := sigmaHS)
      bounds.G₀_pos.le bounds.G₁_pos.le)
  simpa only [biasHalfConstant, mul_assoc] using h

/-- Standard Itô/Fubini and maximal-martingale inputs for the first-order branch.
The generator uses the actual frozen drift Jacobian and Hessian trace. -/
structure OneOrderStochasticInputs
    {Ω : Type*} [MeasurableSpace Ω] {stateDim noiseDim : ℕ}
    (μ : Measure Ω) {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (diffusion : Diffusion stateDim noiseDim)
    (m : ℕ) (K0 Lt : ℝ) (x₀ : State stateDim) (noise X : ℝ → Ω → State stateDim)
    extends CoupledMomentInputs μ bounds m K0 (diffusionHilbertSchmidt diffusion) x₀ noise X where
  temporal_nonneg : 0 ≤ Lt
  time_lipschitz : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x,
    ‖drift s x - drift t x‖ ≤ Lt * (1 + ‖x‖) * |s - t|
  temporalLp : ℕ → ℝ → Lp (State stateDim) 2 μ
  generatorLp : ℕ → ℝ → Lp (State stateDim) 2 μ
  temporal_rep : ∀ i < m, ∀ s ∈
      Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)),
    (fun ω ↦ temporalLp i s ω) =ᵐ[μ] fun ω ↦
      drift s (X s ω) - drift (uniformEulerGrid T m i) (X s ω)
  generator_rep : ∀ i < m, ∀ s ∈
      Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)),
    (fun ω ↦ generatorLp i s ω) =ᵐ[μ] fun ω ↦
      (fderiv ℝ (drift (uniformEulerGrid T m i)) (X s ω)) (drift s (X s ω)) +
        (1 / 2 : ℝ) • driftDiffusionTrace drift diffusion (uniformEulerGrid T m i) (X s ω)
  temporal_integrable : ∀ i < m, IntervalIntegrable (temporalLp i) volume
    (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ))
  generator_integrable : ∀ i < m, IntervalIntegrable
    (fun s ↦ (uniformEulerGrid T m i + T / (m : ℝ) - s) • generatorLp i s) volume
      (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ))
  A : ℕ → Ω → State stateDim
  A_memLp : ∀ i < m, MemLp (A i) 2 μ
  A_integral_eq : ∀ i (hi : i < m), (A_memLp i hi).toLp (A i) =
    (∫ s in uniformEulerGrid T m i..uniformEulerGrid T m i + T / (m : ℝ), temporalLp i s) +
      (∫ s in uniformEulerGrid T m i..uniformEulerGrid T m i + T / (m : ℝ),
        (uniformEulerGrid T m i + T / (m : ℝ) - s) • generatorLp i s)
  martingale : ℕ → Ω → State stateDim
  martingale_memLp : ∀ j ≤ m, MemLp (martingale j) 2 μ
  filtration : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›
  martingale_property : Martingale (fun j : Fin (m + 1) ↦ martingale j) filtration μ
  doob_l2 : FiniteDoobL2 (E := State stateDim) μ
  remainder_split : ∀ᵐ ω ∂μ, ∀ j ≤ m,
    (∑ i ∈ Finset.range j, localDriftRemainder drift X (uniformEulerGrid T m) i ω) =
      (∑ i ∈ Finset.range j, A i ω) + martingale j ω
  stochastic_integrand_integrable : ∀ i < m, IntervalIntegrable
    (fun s ↦ (uniformEulerGrid T m i + T / (m : ℝ) - s) ^ 2 *
      driftDiffusionSecondMoment μ drift diffusion (uniformEulerGrid T m i) (X s)) volume
    (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ))
  /-- Itô isometry and orthogonality for the cumulative stochastic integrals, before
  applying the model's derivative bound or estimating the scalar time integrals. -/
  martingale_isometry : ∀ j ≤ m, (∫ ω, ‖martingale j ω‖ ^ 2 ∂μ) =
    ∑ i ∈ Finset.range j,
      ∫ s in uniformEulerGrid T m i..uniformEulerGrid T m i + T / (m : ℝ),
        (uniformEulerGrid T m i + T / (m : ℝ) - s) ^ 2 *
          driftDiffusionSecondMoment μ drift diffusion (uniformEulerGrid T m i) (X s)

/-- The terminal second moment in the display preceding paper Equation (E.15).
The factor `T h² / 3` is deduced from the actual Itô integrand. -/
theorem OneOrderStochasticInputs.martingale_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {stateDim noiseDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Lt : ℝ}
    {bounds : GevreyBounds drift payoff T} {diffusion : Diffusion stateDim noiseDim}
    {m : ℕ} {x₀ : State stateDim} {noise X : ℝ → Ω → State stateDim}
    (data : OneOrderStochasticInputs μ bounds diffusion m K0 Lt x₀ noise X)
    (j : ℕ) (hj : j ≤ m) :
    (∫ ω, ‖data.martingale j ω‖ ^ 2 ∂μ) ≤
      bounds.driftLipschitzConstant ^ 2 * diffusionHilbertSchmidt diffusion ^ 2 *
        T / 3 * (T / (m : ℝ)) ^ 2 := by
  rw [data.martingale_isometry j hj]
  apply sum_weighted_variances_le (div_nonneg data.time_nonneg (Nat.cast_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (show (m : ℝ) * (T / (m : ℝ)) = T by
      have hm : (m : ℝ) ≠ 0 := by exact_mod_cast data.steps_pos.ne'
      field_simp) hj
    (uniformEulerGrid T m)
    (fun i s ↦ driftDiffusionSecondMoment μ drift diffusion (uniformEulerGrid T m i) (X s))
    data.stochastic_integrand_integrable
  intro i hi s _hs
  have ht := uniformEulerGrid_mem data.time_nonneg data.steps_pos hi.le
  exact driftDiffusionSecondMoment_le bounds diffusion ht.1 ht.2 (X s)

/-- Paper Equation (E.15), now derived from square-integrable martingales, the generic
Doob theorem, and the Itô-isometry second-moment calculation above. -/
theorem OneOrderStochasticInputs.martingale_maximal
    {Ω : Type*} [MeasurableSpace Ω] {stateDim noiseDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Lt : ℝ}
    {bounds : GevreyBounds drift payoff T} {diffusion : Diffusion stateDim noiseDim}
    {m : ℕ} {x₀ : State stateDim} {noise X : ℝ → Ω → State stateDim}
    (data : OneOrderStochasticInputs μ bounds diffusion m K0 Lt x₀ noise X)
    (j : ℕ) (hj : j ≤ m) :
    lpNorm (gridMaxNorm data.martingale j) 2 μ ≤
      2 * bounds.driftLipschitzConstant * diffusionHilbertSchmidt diffusion *
        Real.sqrt (T / 3) * (T / (m : ℝ)) :=
  maximal_le_of_second_moment data.doob_l2 data.martingale data.filtration
    data.martingale_property data.martingale_memLp hj bounds.driftLipschitzConstant_pos.le
    (diffusionHilbertSchmidt_nonneg diffusion) data.time_nonneg
    (div_nonneg data.time_nonneg (Nat.cast_nonneg _)) (data.martingale_second_moment j hj)

private theorem continuous_driftDiffusionTrace
    {stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (diffusion : Diffusion stateDim noiseDim) (t : ℝ) :
    Continuous (driftDiffusionTrace drift diffusion t) := by
  unfold driftDiffusionTrace
  apply continuous_finsetSum
  intro r _
  exact ((bounds.drift_smooth t).continuous_iteratedFDeriv (by simp)).eval continuous_const

/-- The deterministic first-order local bound follows from the actual drift derivatives,
the temporal assumption, the state moment, and the Itô/Fubini representation. -/
theorem OneOrderStochasticInputs.local_bound
    {Ω : Type*} [MeasurableSpace Ω] {stateDim noiseDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Lt : ℝ}
    {bounds : GevreyBounds drift payoff T} {diffusion : Diffusion stateDim noiseDim}
    {m : ℕ} {x₀ : State stateDim} {noise X : ℝ → Ω → State stateDim}
    (data : OneOrderStochasticInputs μ bounds diffusion m K0 Lt x₀ noise X)
    {i : ℕ} (hi : i < m) :
    lpNorm (data.A i) 2 μ ≤
      driftRemainderConstant T K0 bounds.driftLipschitzConstant
        (secondDriftDerivativeConstant bounds) Lt ‖x₀‖ (diffusionHilbertSchmidt diffusion) *
          (T / (m : ℝ)) ^ 2 := by
  have hh : 0 ≤ T / (m : ℝ) := div_nonneg data.time_nonneg (Nat.cast_nonneg m)
  have hinterval : ∀ {s : ℝ},
      s ∈ Icc (uniformEulerGrid T m i) (uniformEulerGrid T m i + T / (m : ℝ)) →
        s ∈ Icc 0 T := fun {_} hs =>
    uniformEulerGrid_interval_mem data.time_nonneg data.steps_pos hi hs
  have hstart := uniformEulerGrid_mem data.time_nonneg data.steps_pos hi.le
  apply order_one_local_remainder_from_ito_representation
    (operator := fun s ω => fderiv ℝ (drift (uniformEulerGrid T m i)) (X s ω))
    (trace := fun s ω => driftDiffusionTrace drift diffusion (uniformEulerGrid T m i) (X s ω))
    (temporalLp := data.temporalLp i) (generatorLp := data.generatorLp i)
    (hA := data.A_memLp i hi)
    data.origin_nonneg
    bounds.driftLipschitzConstant_pos.le (secondDriftDerivativeConstant_nonneg bounds)
    data.temporal_nonneg hh X drift
    (fun s hs => data.exact_memLp s (hinterval hs))
    (fun s hs => data.exact_moment s (hinterval hs))
  · intro s hs x y
    exact drift_lipschitz_of_gevrey bounds (hinterval hs).1 (hinterval hs).2 x y
  · intro s hs x
    exact bounds.drift_norm_le_origin_add_lipschitz
      (fun t ht0 htT => data.drift_origin t ⟨ht0, htT⟩)
      (hinterval hs).1 (hinterval hs).2 x
  · intro s hs x
    simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using
      data.time_lipschitz _ hstart s (hinterval hs) x
  · intro s _ ω
    exact drift_fderiv_norm_le bounds hstart.1 hstart.2 (X s ω)
  · intro s _ ω
    exact drift_trace_norm_le bounds diffusion hstart.1 hstart.2 (X s ω)
  · intro s hs
    exact (continuous_driftDiffusionTrace bounds diffusion _).comp_aestronglyMeasurable
      (data.exact_memLp s (hinterval hs)).aestronglyMeasurable
  · exact data.temporal_rep i hi
  · exact data.generator_rep i hi
  · exact data.temporal_integrable i hi
  · exact data.generator_integrable i hi
  · exact data.A_integral_eq i hi

/-- Paper Theorem 3.8: the actual grid-maximum strong error on the fixed grid. -/
theorem theorem3_8_coupled_strong
    {Ω : Type*} [MeasurableSpace Ω] {stateDim noiseDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Lt : ℝ}
    {bounds : GevreyBounds drift payoff T} {diffusion : Diffusion stateDim noiseDim}
    {m : ℕ} {x₀ : State stateDim} {noise X : ℝ → Ω → State stateDim}
    (data : OneOrderStochasticInputs μ bounds diffusion m K0 Lt x₀ noise X) :
    lpNorm (gridMaxNorm
      (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X) m) 2 μ ≤
      T * strongOneConstant T K0 bounds.driftLipschitzConstant
        (secondDriftDerivativeConstant bounds) Lt ‖x₀‖ (diffusionHilbertSchmidt diffusion) *
          (m : ℝ) ^ (-(1 : ℝ)) := by
  apply coupledEuler_strong_one_of_local μ bounds (uniformEulerGrid T m) x₀ noise X
    data.A data.martingale data.steps_pos data.time_nonneg data.origin_nonneg
    (secondDriftDerivativeConstant_nonneg bounds) data.temporal_nonneg data.sigma_nonneg
  · exact fun i _ => uniformEulerGrid_step T m i
  · exact fun i hi => uniformEulerGrid_mem data.time_nonneg data.steps_pos hi.le
  · exact data.solution_integrable
  · simpa only [uniformEulerGrid_zero] using data.solution_initial
  · exact data.solution_step
  · exact fun i hi => data.exact_memLp _ (uniformEulerGrid_mem data.time_nonneg data.steps_pos hi)
  · exact data.euler_memLp
  · exact data.A_memLp
  · exact data.martingale_memLp
  · exact data.remainder_split
  · exact fun _ hi => data.local_bound hi
  · exact data.martingale_maximal

/-- Paper Theorem 3.8: the actual first-order payoff bias, with the actual diffusion's
Hilbert--Schmidt norm and the second-derivative constant from Assumption 2.1. -/
theorem theorem3_8_coupled_bias
    {Ω : Type*} [MeasurableSpace Ω] {stateDim noiseDim : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Lt : ℝ}
    {bounds : GevreyBounds drift payoff T} {diffusion : Diffusion stateDim noiseDim}
    {m : ℕ} {x₀ : State stateDim} {noise X : ℝ → Ω → State stateDim}
    (data : OneOrderStochasticInputs μ bounds diffusion m K0 Lt x₀ noise X) :
    |(∫ ω, payoff (coupledEulerChain drift (uniformEulerGrid T m)
        (T / (m : ℝ)) x₀ noise m ω) ∂μ) - (∫ ω, payoff (X T ω) ∂μ)| ≤
      biasOneConstant bounds.G₀ bounds.G₁ bounds.β T K0 bounds.driftLipschitzConstant
        (secondDriftDerivativeConstant bounds) Lt ‖x₀‖ (diffusionHilbertSchmidt diffusion) *
          (m : ℝ) ^ (-(1 : ℝ)) := by
  have hX := data.exact_memLp T ⟨data.time_nonneg, le_rfl⟩
  have hpay := payoff_integral_sub_le_payoffDifferenceConstant bounds hX
    (data.euler_memLp m le_rfl) data.exact_exponential data.euler_exponential
    data.joint_exponential
  have herr : ∀ i ≤ m, MemLp
      (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X i) 2 μ := by
    intro i hi
    exact (data.exact_memLp _ (uniformEulerGrid_mem data.time_nonneg data.steps_pos hi)).sub
      (data.euler_memLp i hi)
  have hterminal := lpNorm_le_gridMaxNorm
    (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X) herr
  have hsymm : lpNorm (fun ω => coupledEulerChain drift (uniformEulerGrid T m)
      (T / (m : ℝ)) x₀ noise m ω - X T ω) 2 μ =
      lpNorm (coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X m) 2 μ := by
    rw [show coupledGridError drift (uniformEulerGrid T m) (T / (m : ℝ)) x₀ noise X m =
      fun ω => X T ω - coupledEulerChain drift (uniformEulerGrid T m) (T / (m : ℝ))
        x₀ noise m ω by
          funext ω
          simp only [coupledGridError, uniformEulerGrid_terminal T data.steps_pos]]
    exact lpNorm_sub_comm _ _ 2 μ
  rw [hsymm] at hpay
  refine hpay.trans ?_
  have h := mul_le_mul_of_nonneg_left
    (hterminal.trans (theorem3_8_coupled_strong data))
    (payoffDifferenceConstant_nonneg (beta := bounds.β) (T := T) (K0 := K0)
      (L := bounds.driftLipschitzConstant) (initialNorm := ‖x₀‖)
      (sigmaHS := diffusionHilbertSchmidt diffusion) bounds.G₀_pos.le bounds.G₁_pos.le)
  simpa only [biasOneConstant, mul_assoc, mul_left_comm, mul_comm] using h

end
end TimeDependentLattice.Bias
