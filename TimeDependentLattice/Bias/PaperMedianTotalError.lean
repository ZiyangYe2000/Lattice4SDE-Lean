/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.PaperTotalError

/-!
# Total error of the paper's median estimator

The actual median sampling theorem is combined with the general Euler-bias assumption
or the sufficient conditions of Theorems 3.7 and 3.8. The Gaussian-coordinate representation
of the terminal Euler state identifies its expectation with the sampling integral.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Sampling TimeDependentLattice.Trees

variable {J stateDim noiseDim N k : ℕ} {drift : Drift stateDim}
  {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε q : ℝ}
  {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ} {x₀ : State stateDim}

/-- Corollary 3.9 for the actual median, with Assumption 3.6 as the Euler-bias input. -/
theorem corollary3_9_median_paper
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε))
    (medianEstimator : RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input, IsOddMedian k
      (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
        (input i).1 (input i).2) (medianEstimator input))
    (exactIntegral : ℝ) {C_bias θ : ℝ}
    (hbias : |eulerGaussianIntegral (J := J) drift diffusion payoff T x₀ - exactIntegral| ≤
      C_bias * (numSteps J : ℝ) ^ (-θ)) :
    MemLp (fun input ↦ medianEstimator input - exactIntegral) (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ∧
    lpNorm (fun input ↦ medianEstimator input - exactIntegral) (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ≤
      eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ * (N : ℝ) ^ (-1 + ε) +
        C_bias * (numSteps J : ℝ) ^ (-θ) := by
  let : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty sampling.prime_points.two_le
  have hs : 0 ≤ eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ *
      (N : ℝ) ^ (-1 + ε) :=
    mul_nonneg (eulerMedianSamplingConstant_pos sampling hk hq hRange).le
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  exact totalError_real_of_sampling_and_bias
    (measurable_eulerMedian bounds x₀ sampling.quantile_measurable hk medianEstimator hmedian)
    hq hs (sampling.median_bound hk hq hRange medianEstimator hmedian) hbias

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {noise X : ℝ → Ω → State stateDim}

/-- Corollary 3.9 for the median, with the actual half-order bias from Theorem 3.7. -/
theorem corollary3_9_median_half
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε))
    (medianEstimator : RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input, IsOddMedian k
      (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
        (input i).1 (input i).2) (medianEstimator input))
    {H_t : ℝ}
    (euler : HalfOrderStochasticInputs μ bounds (numSteps J) K₀ H_t
      (diffusionHilbertSchmidt diffusion) x₀ noise X)
    (hlaw : IdentDistrib
      (coupledEulerChain drift (uniformEulerGrid T (numSteps J))
        (T / (numSteps J : ℝ)) x₀ noise (numSteps J))
      (gaussianEulerTerminalState (J := J) drift diffusion T x₀) μ
      (Measure.pi fun _ : Index J noiseDim ↦ gaussianReal 0 1)) :
    MemLp (fun input ↦ medianEstimator input - ∫ ω, payoff (X T ω) ∂μ)
      (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ∧
    lpNorm (fun input ↦ medianEstimator input - ∫ ω, payoff (X T ω) ∂μ)
      (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ≤
      eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ * (N : ℝ) ^ (-1 + ε) +
        biasHalfConstant bounds.G₀ bounds.G₁ bounds.β T K₀ bounds.driftLipschitzConstant
          H_t ‖x₀‖ (diffusionHilbertSchmidt diffusion) *
            (numSteps J : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hb := theorem3_7_coupled_bias euler
  rw [← eulerGaussianIntegral_eq_of_identDistrib bounds x₀ hlaw] at hb
  exact corollary3_9_median_paper sampling hk hq hRange medianEstimator hmedian _ hb

/-- Corollary 3.9 for the median, with the actual first-order bias from Theorem 3.8. -/
theorem corollary3_9_median_one
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε))
    (medianEstimator : RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input, IsOddMedian k
      (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
        (input i).1 (input i).2) (medianEstimator input))
    {L_t : ℝ}
    (euler : OneOrderStochasticInputs μ bounds diffusion (numSteps J) K₀ L_t x₀ noise X)
    (hlaw : IdentDistrib
      (coupledEulerChain drift (uniformEulerGrid T (numSteps J))
        (T / (numSteps J : ℝ)) x₀ noise (numSteps J))
      (gaussianEulerTerminalState (J := J) drift diffusion T x₀) μ
      (Measure.pi fun _ : Index J noiseDim ↦ gaussianReal 0 1)) :
    MemLp (fun input ↦ medianEstimator input - ∫ ω, payoff (X T ω) ∂μ)
      (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ∧
    lpNorm (fun input ↦ medianEstimator input - ∫ ω, payoff (X T ω) ∂μ)
      (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ≤
      eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ * (N : ℝ) ^ (-1 + ε) +
        biasOneConstant bounds.G₀ bounds.G₁ bounds.β T K₀ bounds.driftLipschitzConstant
          (secondDriftDerivativeConstant bounds) L_t ‖x₀‖ (diffusionHilbertSchmidt diffusion) *
            (numSteps J : ℝ) ^ (-(1 : ℝ)) := by
  have hb := theorem3_8_coupled_bias euler
  rw [← eulerGaussianIntegral_eq_of_identDistrib bounds x₀ hlaw] at hb
  exact corollary3_9_median_paper sampling hk hq hRange medianEstimator hmedian _ hb

end

end TimeDependentLattice.Bias
