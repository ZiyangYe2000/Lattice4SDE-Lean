/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.ErrorRecursion
import TimeDependentLattice.Bias.PayoffTransfer

/-!
# Euler payoff rates for actual coupled random states

These theorems combine the grid-maximum error estimates with the proved payoff transfer.
The state-error decomposition, one-step remainder bounds, martingale bound, and exponential
state moments are explicit inputs.  Neither a scalar error recurrence nor a payoff-bias bound
is assumed.  The separate local-estimate layer supplies the one-step remainder inequalities.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators
open MeasureTheory
open TimeDependentLattice.Euler TimeDependentLattice.Trees

/-- The half-order expectation bias, for actual exact and approximate grid states, obtained
from their local remainder bounds and the terminal exponential-moment input of (E.5). -/
theorem euler_bias_half_from_local_remainders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 Ht initialNorm sigmaHS : ℝ}
    (bounds : GevreyBounds drift payoff T)
    (X Y difference remainder : ℕ → Ω → State stateDim)
    {m : ℕ} (hm : 0 < m)
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hHt : 0 ≤ Ht)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (hX : ∀ i ≤ m, MemLp (X i) 2 μ) (hY : ∀ i ≤ m, MemLp (Y i) 2 μ)
    (hrem : ∀ i < m, MemLp (remainder i) 2 μ)
    (hdecomp : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      X j ω - Y j ω = (T / (m : ℝ)) • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω))
    (hlip : ∀ᵐ ω ∂μ, ∀ i < m,
      ‖difference i ω‖ ≤ bounds.driftLipschitzConstant * ‖X i ω - Y i ω‖)
    (hlocal : ∀ i < m, lpNorm (remainder i) 2 μ ≤
      (2 / 3 : ℝ) *
        (bounds.driftLipschitzConstant *
            incrementConstant T K0 bounds.driftLipschitzConstant initialNorm sigmaHS +
          Ht * (1 + stateMomentConstant T K0 bounds.driftLipschitzConstant
            initialNorm sigmaHS)) *
        (T / (m : ℝ)) * Real.sqrt (T / (m : ℝ)))
    (hExpX : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖X m ω‖)) μ)
    (hExpY : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖Y m ω‖)) μ)
    (hMoment : (∫ ω, Real.exp (2 * bounds.β * ‖X m ω‖) ∂μ) +
      (∫ ω, Real.exp (2 * bounds.β * ‖Y m ω‖) ∂μ) ≤
        stateExponentialPrefactor (2 * bounds.β) T K0
          bounds.driftLipschitzConstant sigmaHS *
            Real.exp (2 * bounds.β * Real.exp (bounds.driftLipschitzConstant * T) *
              initialNorm)) :
    |(∫ ω, payoff (Y m ω) ∂μ) - ∫ ω, payoff (X m ω) ∂μ| ≤
      biasHalfConstant bounds.G₀ bounds.G₁ bounds.β T K0
        bounds.driftLipschitzConstant Ht initialNorm sigmaHS *
          (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let error : ℕ → Ω → State stateDim := fun j ω ↦ X j ω - Y j ω
  have herror : ∀ i ≤ m, MemLp (error i) 2 μ :=
    fun i hi ↦ (hX i hi).sub (hY i hi)
  have hstrong := euler_strong_half_from_local_remainders μ error difference remainder hm
    hT hK0 bounds.driftLipschitzConstant_pos.le hHt hinitial hsigma herror hrem
    hdecomp hlip hlocal
  have hterminal := lpNorm_le_gridMaxNorm error herror
  have hpayoff := payoff_integral_sub_le_payoffDifferenceConstant bounds
    (hX m le_rfl) (hY m le_rfl) hExpX hExpY hMoment
  have hsymm : lpNorm (fun ω ↦ Y m ω - X m ω) 2 μ = lpNorm (error m) 2 μ := by
    change lpNorm (Y m - X m) 2 μ = lpNorm (X m - Y m) 2 μ
    exact lpNorm_sub_comm (Y m) (X m) 2 μ
  rw [hsymm] at hpayoff
  refine hpayoff.trans ?_
  have h := mul_le_mul_of_nonneg_left (hterminal.trans hstrong)
    (payoffDifferenceConstant_nonneg (beta := bounds.β) (T := T) (K0 := K0)
      (L := bounds.driftLipschitzConstant) (initialNorm := initialNorm) (sigmaHS := sigmaHS)
      bounds.G₀_pos.le bounds.G₁_pos.le)
  simpa only [biasHalfConstant, mul_assoc] using h

/-- The first-order expectation bias from actual local deterministic remainders and a maximal
martingale estimate.  `B2` is the scalar second-derivative bound used in the local remainder
input; the local-estimate layer can specialize it to the paper's `mathsf B_2`. -/
theorem euler_bias_one_from_local_remainders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T K0 B2 Lt initialNorm sigmaHS : ℝ}
    (bounds : GevreyBounds drift payoff T)
    (X Y difference remainder martingale : ℕ → Ω → State stateDim)
    {m : ℕ} (hm : 0 < m)
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hB2 : 0 ≤ B2) (hLt : 0 ≤ Lt)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS)
    (hX : ∀ i ≤ m, MemLp (X i) 2 μ) (hY : ∀ i ≤ m, MemLp (Y i) 2 μ)
    (hrem : ∀ i < m, MemLp (remainder i) 2 μ)
    (hmart : ∀ i ≤ m, MemLp (martingale i) 2 μ)
    (hdecomp : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      X j ω - Y j ω = (T / (m : ℝ)) • (∑ i ∈ Finset.range j, difference i ω) +
        (∑ i ∈ Finset.range j, remainder i ω) + martingale j ω)
    (hlip : ∀ᵐ ω ∂μ, ∀ i < m,
      ‖difference i ω‖ ≤ bounds.driftLipschitzConstant * ‖X i ω - Y i ω‖)
    (hlocal : ∀ i < m, lpNorm (remainder i) 2 μ ≤
      driftRemainderConstant T K0 bounds.driftLipschitzConstant B2 Lt initialNorm sigmaHS *
        (T / (m : ℝ)) ^ 2)
    (hmartBound : ∀ j ≤ m, lpNorm (gridMaxNorm martingale j) 2 μ ≤
      2 * bounds.driftLipschitzConstant * sigmaHS * Real.sqrt (T / 3) * (T / (m : ℝ)))
    (hExpX : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖X m ω‖)) μ)
    (hExpY : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖Y m ω‖)) μ)
    (hMoment : (∫ ω, Real.exp (2 * bounds.β * ‖X m ω‖) ∂μ) +
      (∫ ω, Real.exp (2 * bounds.β * ‖Y m ω‖) ∂μ) ≤
        stateExponentialPrefactor (2 * bounds.β) T K0
          bounds.driftLipschitzConstant sigmaHS *
            Real.exp (2 * bounds.β * Real.exp (bounds.driftLipschitzConstant * T) *
              initialNorm)) :
    |(∫ ω, payoff (Y m ω) ∂μ) - ∫ ω, payoff (X m ω) ∂μ| ≤
      biasOneConstant bounds.G₀ bounds.G₁ bounds.β T K0
        bounds.driftLipschitzConstant B2 Lt initialNorm sigmaHS *
          (m : ℝ) ^ (-(1 : ℝ)) := by
  let error : ℕ → Ω → State stateDim := fun j ω ↦ X j ω - Y j ω
  have herror : ∀ i ≤ m, MemLp (error i) 2 μ :=
    fun i hi ↦ (hX i hi).sub (hY i hi)
  have hstrong := euler_strong_one_from_local_remainders μ error difference remainder martingale
    hm hT hK0 bounds.driftLipschitzConstant_pos.le hB2 hLt hinitial hsigma herror hrem
    hmart hdecomp hlip hlocal hmartBound
  have hterminal := lpNorm_le_gridMaxNorm error herror
  have hpayoff := payoff_integral_sub_le_payoffDifferenceConstant bounds
    (hX m le_rfl) (hY m le_rfl) hExpX hExpY hMoment
  have hsymm : lpNorm (fun ω ↦ Y m ω - X m ω) 2 μ = lpNorm (error m) 2 μ := by
    change lpNorm (Y m - X m) 2 μ = lpNorm (X m - Y m) 2 μ
    exact lpNorm_sub_comm (Y m) (X m) 2 μ
  rw [hsymm] at hpayoff
  refine hpayoff.trans ?_
  have h := mul_le_mul_of_nonneg_left (hterminal.trans hstrong)
    (payoffDifferenceConstant_nonneg (beta := bounds.β) (T := T) (K0 := K0)
      (L := bounds.driftLipschitzConstant) (initialNorm := initialNorm) (sigmaHS := sigmaHS)
      bounds.G₀_pos.le bounds.G₁_pos.le)
  simpa only [biasOneConstant, mul_assoc, mul_left_comm, mul_comm] using h

end

end TimeDependentLattice.Bias
