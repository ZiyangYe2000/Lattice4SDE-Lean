/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.EulerProcess
import TimeDependentLattice.Bias.PayoffTransfer
import TimeDependentLattice.Sampling.LatticeEstimator
import Mathlib.Probability.IdentDistrib

/-!
# Gaussian-coordinate and coupled Euler expectations

Equation (2.22) of the paper: the Gaussian-coordinate representation of the Euler terminal
state transports both payoff integrability and its expectation to the coupled Euler chain.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Sampling TimeDependentLattice.Trees

/-- The Gaussian-coordinate terminal state in the Brownian-bridge representation. -/
def gaussianEulerTerminalState
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Index J noiseDim → ℝ) : State stateDim :=
  terminalState drift diffusion T x₀ (bridgeInput z)

/-- Equation (2.22), obtained from the Gaussian-coordinate representation of the Euler
terminal state. -/
theorem eulerGaussianIntegral_eq_of_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    {Y : Ω → State stateDim}
    (hlaw : IdentDistrib Y
      (gaussianEulerTerminalState (J := J) drift diffusion T x₀) μ
      (Measure.pi fun _ : Index J noiseDim ↦ gaussianReal 0 1)) :
    eulerGaussianIntegral (J := J) drift diffusion payoff T x₀ =
      ∫ ω, payoff (Y ω) ∂μ := by
  simpa only [eulerGaussianIntegral, gaussianEulerTerminalState, integrand,
    Function.comp_apply] using
      (hlaw.comp bounds.payoff_smooth.continuous.measurable).integral_eq.symm

/-- The actual Gaussian integrand is integrable under the moment inputs of Lemma E.2. -/
theorem integrable_rawEulerIntegrand_of_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    {Y : Ω → State stateDim} (hY : MemLp Y 2 μ)
    (hExp : Integrable (fun ω ↦ Real.exp (2 * bounds.β * ‖Y ω‖)) μ)
    (hlaw : IdentDistrib Y
      (gaussianEulerTerminalState (J := J) drift diffusion T x₀) μ
      (Measure.pi fun _ : Index J noiseDim ↦ gaussianReal 0 1)) :
    Integrable (fun z : Index J noiseDim → ℝ ↦
      integrand drift diffusion payoff T x₀ (bridgeInput z))
      (Measure.pi fun _ : Index J noiseDim ↦ gaussianReal 0 1) := by
  have hpay := payoff_integrable_of_second_and_exponential_moments bounds hY hExp
  simpa only [gaussianEulerTerminalState, integrand, Function.comp_def] using
    (hlaw.comp bounds.payoff_smooth.continuous.measurable).integrable_snd hpay

end

end TimeDependentLattice.Bias
