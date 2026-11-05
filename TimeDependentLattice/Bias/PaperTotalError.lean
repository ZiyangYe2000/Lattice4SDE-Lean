/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.GaussianExpectation
import TimeDependentLattice.Bias.UniformTheorems
import TimeDependentLattice.Bias.TotalError
import TimeDependentLattice.Sampling.PaperTheorems

/-!
# The paper's total-error theorems for the actual estimators

The sampling conclusions are called directly. For the sufficient Euler conditions,
the Gaussian-coordinate representation of the terminal Euler state identifies the two
expectations.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Sampling TimeDependentLattice.Trees

/-- Real `L^q` form of the triangle step, including integrability of the total error. -/
theorem totalError_real_of_sampling_and_bias
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {estimator : Ξ → ℝ} (hmeas : Measurable estimator)
    {approximateIntegral exactIntegral samplingBound biasBound q : ℝ}
    (hq : 1 ≤ q) (hsamplingNonneg : 0 ≤ samplingBound)
    (hsampling : eLpNorm' (fun ξ ↦ estimator ξ - approximateIntegral) q ν ≤
      ENNReal.ofReal samplingBound)
    (hbias : |approximateIntegral - exactIntegral| ≤ biasBound) :
    MemLp (fun ξ ↦ estimator ξ - exactIntegral) (ENNReal.ofReal q) ν ∧
      lpNorm (fun ξ ↦ estimator ξ - exactIntegral) (ENNReal.ofReal q) ν ≤
        samplingBound + biasBound := by
  have hbiasNonneg : 0 ≤ biasBound := (abs_nonneg _).trans hbias
  have h := totalError_of_sampling_and_real_bias estimator approximateIntegral exactIntegral hq
    (hmeas.sub_const approximateIntegral).aestronglyMeasurable hsampling hbias
  rw [← ENNReal.ofReal_add hsamplingNonneg hbiasNonneg] at h
  have hm := (hmeas.sub_const exactIntegral).aestronglyMeasurable (μ := ν)
  exact ⟨memLp_of_eLpNorm'_le_real (by linarith) hm h,
    lpNorm_le_of_eLpNorm'_le_real (by linarith) (add_nonneg hsamplingNonneg hbiasNonneg) hm h⟩

section Single

variable {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
  {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε : ℝ}
  {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ} {x₀ : State stateDim}

/-- Corollary 3.9, single rule: Theorem 3.1 combined with Assumption 3.6. -/
theorem corollary3_9_single_paper
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (exactIntegral : ℝ) {C_bias θ : ℝ}
    (hbias : |eulerGaussianIntegral (J := J) drift diffusion payoff T x₀ - exactIntegral| ≤
      C_bias * (numSteps J : ℝ) ^ (-θ)) :
    MemLp (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ input.1 input.2 -
        exactIntegral) 1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ∧
    lpNorm (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ input.1 input.2 -
        exactIntegral) 1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      eulerSamplingConstant diffusion bounds K₀ ε x₀ * (N : ℝ) ^ (-1 + ε) +
        C_bias * (numSteps J : ℝ) ^ (-θ) := by
  let : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty sampling.prime_points.two_le
  have hs : 0 ≤ eulerSamplingConstant diffusion bounds K₀ ε x₀ *
      (N : ℝ) ^ (-1 + ε) := mul_nonneg
    (eulerSamplingConstant_nonneg diffusion bounds K₀ ε x₀)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  simpa only [ENNReal.ofReal_one, eulerLatticeRule] using totalError_real_of_sampling_and_bias
    (measurable_gaussianLatticeRule_joint sampling.quantile_measurable N
      (measurable_rawEulerIntegrand bounds x₀)) le_rfl hs sampling.single_bound hbias

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {noise X : ℝ → Ω → State stateDim}

/-- Corollary 3.9 with the half-order bias obtained from Theorem 3.7. -/
theorem corollary3_9_single_half
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀) {H_t : ℝ}
    (euler : HalfOrderStochasticInputs μ bounds (numSteps J) K₀ H_t
      (diffusionHilbertSchmidt diffusion) x₀ noise X)
    (hlaw : IdentDistrib
      (coupledEulerChain drift (uniformEulerGrid T (numSteps J))
        (T / (numSteps J : ℝ)) x₀ noise (numSteps J))
      (gaussianEulerTerminalState (J := J) drift diffusion T x₀) μ
      (Measure.pi fun _ : Index J noiseDim ↦ gaussianReal 0 1)) :
    MemLp (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ input.1 input.2 -
        ∫ ω, payoff (X T ω) ∂μ) 1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ∧
    lpNorm (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ input.1 input.2 -
        ∫ ω, payoff (X T ω) ∂μ) 1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      eulerSamplingConstant diffusion bounds K₀ ε x₀ * (N : ℝ) ^ (-1 + ε) +
        biasHalfConstant bounds.G₀ bounds.G₁ bounds.β T K₀ bounds.driftLipschitzConstant
          H_t ‖x₀‖ (diffusionHilbertSchmidt diffusion) *
            (numSteps J : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hb := theorem3_7_coupled_bias euler
  rw [← eulerGaussianIntegral_eq_of_identDistrib bounds x₀ hlaw] at hb
  exact corollary3_9_single_paper sampling _ hb

/-- Corollary 3.9 with the first-order bias obtained from Theorem 3.8. -/
theorem corollary3_9_single_one
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀) {L_t : ℝ}
    (euler : OneOrderStochasticInputs μ bounds diffusion (numSteps J) K₀ L_t x₀ noise X)
    (hlaw : IdentDistrib
      (coupledEulerChain drift (uniformEulerGrid T (numSteps J))
        (T / (numSteps J : ℝ)) x₀ noise (numSteps J))
      (gaussianEulerTerminalState (J := J) drift diffusion T x₀) μ
      (Measure.pi fun _ : Index J noiseDim ↦ gaussianReal 0 1)) :
    MemLp (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ input.1 input.2 -
        ∫ ω, payoff (X T ω) ∂μ) 1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ∧
    lpNorm (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ input.1 input.2 -
        ∫ ω, payoff (X T ω) ∂μ) 1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      eulerSamplingConstant diffusion bounds K₀ ε x₀ * (N : ℝ) ^ (-1 + ε) +
        biasOneConstant bounds.G₀ bounds.G₁ bounds.β T K₀ bounds.driftLipschitzConstant
          (secondDriftDerivativeConstant bounds) L_t ‖x₀‖ (diffusionHilbertSchmidt diffusion) *
            (numSteps J : ℝ) ^ (-(1 : ℝ)) := by
  have hb := theorem3_8_coupled_bias euler
  rw [← eulerGaussianIntegral_eq_of_identDistrib bounds x₀ hlaw] at hb
  exact corollary3_9_single_paper sampling _ hb

end Single

end

end TimeDependentLattice.Bias
