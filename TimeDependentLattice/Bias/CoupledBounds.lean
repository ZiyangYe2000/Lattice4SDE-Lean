/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.EulerProcess
import TimeDependentLattice.Bias.ErrorRecursion

/-!
# Strong bounds for the actual coupled Euler chain

The exact process satisfies its standard SDE integral equation with the same additive noise
as the defined Euler chain.  The vector error identity and the spatial Lipschitz error estimate
are derived internally.  Local stochastic remainder estimates are inputs to this assembly
layer; the elementary estimates yielding them are in `LocalEstimates`.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory TimeDependentLattice.Euler

/-- The actual difference of the exact process and the coupled Euler chain at the grid. -/
def coupledGridError {Ω : Type*} {stateDim : ℕ}
    (drift : Drift stateDim) (grid : ℕ → ℝ) (h : ℝ) (x₀ : State stateDim)
    (noise X : ℝ → Ω → State stateDim) (i : ℕ) (ω : Ω) : State stateDim :=
  X (grid i) ω - coupledEulerChain drift grid h x₀ noise i ω

/-- The spatial drift difference appearing after subtracting exact and Euler equations. -/
def coupledGridDriftDifference {Ω : Type*} {stateDim : ℕ}
    (drift : Drift stateDim) (grid : ℕ → ℝ) (h : ℝ) (x₀ : State stateDim)
    (noise X : ℝ → Ω → State stateDim) (i : ℕ) (ω : Ω) : State stateDim :=
  drift (grid i) (X (grid i) ω) -
    drift (grid i) (coupledEulerChain drift grid h x₀ noise i ω)

theorem coupledGridDriftDifference_le
    {Ω : Type*} {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T h : ℝ} (bounds : Trees.GevreyBounds drift payoff T)
    (grid : ℕ → ℝ) (x₀ : State stateDim) (noise X : ℝ → Ω → State stateDim)
    {i : ℕ} (hi0 : 0 ≤ grid i) (hiT : grid i ≤ T) (ω : Ω) :
    ‖coupledGridDriftDifference drift grid h x₀ noise X i ω‖ ≤
      bounds.driftLipschitzConstant * ‖coupledGridError drift grid h x₀ noise X i ω‖ :=
  drift_lipschitz_of_gevrey bounds hi0 hiT _ _

/-- Theorem 3.7 for the actual coupled exact/Euler processes, after local remainder
estimates.  No scalar error recurrence or vector error decomposition is assumed. -/
theorem coupledEuler_strong_half_of_local
    {Ω : Type*} [MeasurableSpace Ω] {stateDim m : ℕ}
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 Ht sigmaHS : ℝ}
    (μ : Measure Ω) (bounds : Trees.GevreyBounds drift payoff T)
    (grid : ℕ → ℝ) (x₀ : State stateDim) (noise X : ℝ → Ω → State stateDim)
    (hm : 0 < m) (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hHt : 0 ≤ Ht) (hsigma : 0 ≤ sigmaHS)
    (hgrid : ∀ i < m, grid (i + 1) - grid i = T / (m : ℝ))
    (hgridTime : ∀ i < m, 0 ≤ grid i ∧ grid i ≤ T)
    (hint : ∀ᵐ ω ∂μ, ∀ i < m,
      IntervalIntegrable (fun s ↦ drift s (X s ω)) volume (grid i) (grid (i + 1)))
    (hzero : ∀ᵐ ω ∂μ, X (grid 0) ω = x₀)
    (hsolution : ∀ᵐ ω ∂μ, ∀ i < m, X (grid (i + 1)) ω = X (grid i) ω +
      (∫ s in grid i..grid (i + 1), drift s (X s ω)) +
        (noise (grid (i + 1)) ω - noise (grid i) ω))
    (hX : ∀ i ≤ m, MemLp (X (grid i)) 2 μ)
    (hY : ∀ i ≤ m, MemLp (coupledEulerChain drift grid (T / (m : ℝ)) x₀ noise i) 2 μ)
    (hrem : ∀ i < m, MemLp (localDriftRemainder drift X grid i) 2 μ)
    (hlocal : ∀ i < m, lpNorm (localDriftRemainder drift X grid i) 2 μ ≤
      (2 / 3 : ℝ) *
        (bounds.driftLipschitzConstant *
            incrementConstant T K0 bounds.driftLipschitzConstant ‖x₀‖ sigmaHS +
          Ht * (1 + stateMomentConstant T K0 bounds.driftLipschitzConstant ‖x₀‖ sigmaHS)) *
        (T / (m : ℝ)) * Real.sqrt (T / (m : ℝ))) :
    lpNorm (gridMaxNorm (coupledGridError drift grid (T / (m : ℝ)) x₀ noise X) m) 2 μ ≤
      strongHalfConstant T K0 bounds.driftLipschitzConstant Ht ‖x₀‖ sigmaHS *
        (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  apply euler_strong_half_from_local_remainders μ
    (coupledGridError drift grid (T / (m : ℝ)) x₀ noise X)
    (coupledGridDriftDifference drift grid (T / (m : ℝ)) x₀ noise X)
    (localDriftRemainder drift X grid) hm hT hK0
    bounds.driftLipschitzConstant_pos.le hHt (norm_nonneg x₀) hsigma
  · intro i hi
    exact (hX i hi).sub (hY i hi)
  · exact hrem
  · exact coupledEuler_error_eq_sum_ae drift grid (T / (m : ℝ)) x₀ noise X
      hgrid hint hzero hsolution
  · exact Filter.Eventually.of_forall fun ω i hi =>
      coupledGridDriftDifference_le bounds grid x₀ noise X
        (hgridTime i hi).1 (hgridTime i hi).2 ω
  · exact hlocal

/-- Theorem 3.8 for the actual coupled processes.  The integral splitting into `A` and `M`
is the Itô/Fubini identity; its local and martingale bounds are supplied separately. -/
theorem coupledEuler_strong_one_of_local
    {Ω : Type*} [MeasurableSpace Ω] {stateDim m : ℕ}
    {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 B2 Lt sigmaHS : ℝ}
    (μ : Measure Ω) (bounds : Trees.GevreyBounds drift payoff T)
    (grid : ℕ → ℝ) (x₀ : State stateDim) (noise X : ℝ → Ω → State stateDim)
    (A M : ℕ → Ω → State stateDim)
    (hm : 0 < m) (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hB2 : 0 ≤ B2) (hLt : 0 ≤ Lt)
    (hsigma : 0 ≤ sigmaHS)
    (hgrid : ∀ i < m, grid (i + 1) - grid i = T / (m : ℝ))
    (hgridTime : ∀ i < m, 0 ≤ grid i ∧ grid i ≤ T)
    (hint : ∀ᵐ ω ∂μ, ∀ i < m,
      IntervalIntegrable (fun s ↦ drift s (X s ω)) volume (grid i) (grid (i + 1)))
    (hzero : ∀ᵐ ω ∂μ, X (grid 0) ω = x₀)
    (hsolution : ∀ᵐ ω ∂μ, ∀ i < m, X (grid (i + 1)) ω = X (grid i) ω +
      (∫ s in grid i..grid (i + 1), drift s (X s ω)) +
        (noise (grid (i + 1)) ω - noise (grid i) ω))
    (hX : ∀ i ≤ m, MemLp (X (grid i)) 2 μ)
    (hY : ∀ i ≤ m, MemLp (coupledEulerChain drift grid (T / (m : ℝ)) x₀ noise i) 2 μ)
    (hA : ∀ i < m, MemLp (A i) 2 μ)
    (hM : ∀ i ≤ m, MemLp (M i) 2 μ)
    (hsplit : ∀ᵐ ω ∂μ, ∀ j ≤ m,
      (∑ i ∈ Finset.range j, localDriftRemainder drift X grid i ω) =
        (∑ i ∈ Finset.range j, A i ω) + M j ω)
    (hlocal : ∀ i < m, lpNorm (A i) 2 μ ≤
      driftRemainderConstant T K0 bounds.driftLipschitzConstant B2 Lt ‖x₀‖ sigmaHS *
        (T / (m : ℝ)) ^ 2)
    (hmartBound : ∀ j ≤ m, lpNorm (gridMaxNorm M j) 2 μ ≤
      2 * bounds.driftLipschitzConstant * sigmaHS * Real.sqrt (T / 3) * (T / (m : ℝ))) :
    lpNorm (gridMaxNorm (coupledGridError drift grid (T / (m : ℝ)) x₀ noise X) m) 2 μ ≤
      T * strongOneConstant T K0 bounds.driftLipschitzConstant B2 Lt ‖x₀‖ sigmaHS *
        (m : ℝ) ^ (-(1 : ℝ)) := by
  apply euler_strong_one_from_local_remainders μ
    (coupledGridError drift grid (T / (m : ℝ)) x₀ noise X)
    (coupledGridDriftDifference drift grid (T / (m : ℝ)) x₀ noise X)
    A M hm hT hK0 bounds.driftLipschitzConstant_pos.le hB2 hLt (norm_nonneg x₀) hsigma
  · intro i hi
    exact (hX i hi).sub (hY i hi)
  · exact hA
  · exact hM
  · have hd := coupledEuler_error_eq_sum_ae drift grid (T / (m : ℝ)) x₀ noise X
      hgrid hint hzero hsolution
    filter_upwards [hd, hsplit] with ω hdω hsω
    intro j hj
    change X (grid j) ω - coupledEulerChain drift grid (T / (m : ℝ)) x₀ noise j ω = _
    rw [hdω j hj, hsω j hj]
    simp only [coupledGridDriftDifference]
    abel
  · exact Filter.Eventually.of_forall fun ω i hi =>
      coupledGridDriftDifference_le bounds grid x₀ noise X
        (hgridTime i hi).1 (hgridTime i hi).2 ω
  · exact hlocal
  · exact hmartBound

end
end TimeDependentLattice.Bias
