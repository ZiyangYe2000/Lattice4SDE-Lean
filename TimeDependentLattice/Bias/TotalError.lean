/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Bias.Constants
import TimeDependentLattice.Sampling.EulerMedian
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Sampling error plus Euler bias

This file contains the abstract triangle-inequality step underlying paper Corollary 3.9.  It is
independent of how the sampling estimate and the Euler bias estimate are proved.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Sampling TimeDependentLattice.Trees

/-- Abstract form of paper Corollary 3.9: an `L^q` sampling-error estimate relative to `I_m`
and a deterministic bias estimate between `I_m` and `I` add to give the total error.

The bias is expressed in `ℝ≥0∞`, matching Mathlib's `eLpNorm'`.  A later specialization converts
the paper's real bound `C_bias m^{-θ}` with `ENNReal.ofReal`. -/
theorem totalError_of_sampling_and_bias
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (estimator : Ω → ℝ) (approximateIntegral exactIntegral : ℝ)
    {q : ℝ} (hq : 1 ≤ q)
    {samplingBound biasBound : ℝ≥0∞}
    (hmeas : AEStronglyMeasurable (fun ω ↦ estimator ω - approximateIntegral) μ)
    (hsampling :
      eLpNorm' (fun ω ↦ estimator ω - approximateIntegral) q μ ≤ samplingBound)
    (hbias : ‖approximateIntegral - exactIntegral‖ₑ ≤ biasBound) :
    eLpNorm' (fun ω ↦ estimator ω - exactIntegral) q μ ≤
      samplingBound + biasBound := by
  have hqPos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hdecomp :
      (fun ω ↦ estimator ω - exactIntegral) =
        (fun ω ↦ estimator ω - approximateIntegral) +
          (fun _ : Ω ↦ approximateIntegral - exactIntegral) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [hdecomp]
  calc
    eLpNorm'
        ((fun ω ↦ estimator ω - approximateIntegral) +
          (fun _ : Ω ↦ approximateIntegral - exactIntegral)) q μ ≤
      eLpNorm' (fun ω ↦ estimator ω - approximateIntegral) q μ +
        eLpNorm' (fun _ : Ω ↦ approximateIntegral - exactIntegral) q μ :=
      eLpNorm'_add_le hmeas aestronglyMeasurable_const hq
    _ = eLpNorm' (fun ω ↦ estimator ω - approximateIntegral) q μ +
        ‖approximateIntegral - exactIntegral‖ₑ := by
      rw [eLpNorm'_const_of_isProbabilityMeasure _ hqPos]
    _ ≤ samplingBound + biasBound := add_le_add hsampling hbias

/-- Real-valued bias version of `totalError_of_sampling_and_bias`, matching Assumption 3.6. -/
theorem totalError_of_sampling_and_real_bias
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (estimator : Ω → ℝ) (approximateIntegral exactIntegral : ℝ)
    {q : ℝ} (hq : 1 ≤ q)
    {samplingBound biasBound : ℝ}
    (hmeas : AEStronglyMeasurable (fun ω ↦ estimator ω - approximateIntegral) μ)
    (hsampling :
      eLpNorm' (fun ω ↦ estimator ω - approximateIntegral) q μ ≤
        ENNReal.ofReal samplingBound)
    (hbias : |approximateIntegral - exactIntegral| ≤ biasBound) :
    eLpNorm' (fun ω ↦ estimator ω - exactIntegral) q μ ≤
      ENNReal.ofReal samplingBound + ENNReal.ofReal biasBound := by
  apply totalError_of_sampling_and_bias estimator approximateIntegral exactIntegral hq
    hmeas hsampling
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal hbias

/-! ## Paper Corollary 3.9 -/

/-- Single-rule total error for the Euler lattice estimator. -/
theorem corollary3_9_single
    {J stateDim noiseDim N : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x0 : State stateDim)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (hN : 2 ≤ N)
    (exactIntegral : ℝ) {samplingBound biasBound : ℝ}
    (hsampling :
      eLpNorm'
          (fun input : LatticeGenerator (Index J noiseDim) N ×
              LatticeShift (Index J noiseDim) ↦
            eulerLatticeError normalQuantile N drift diffusion payoff T x0
              input.1 input.2)
          1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
        ENNReal.ofReal samplingBound)
    (hbias :
      |eulerGaussianIntegral (J := J) drift diffusion payoff T x0 - exactIntegral| ≤
        biasBound) :
    eLpNorm'
        (fun input : LatticeGenerator (Index J noiseDim) N ×
            LatticeShift (Index J noiseDim) ↦
          eulerLatticeRule normalQuantile N drift diffusion payoff T x0 input.1 input.2 -
            exactIntegral)
        1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal samplingBound + ENNReal.ofReal biasBound := by
  letI : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty hN
  apply totalError_of_sampling_and_real_bias
    (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeRule normalQuantile N drift diffusion payoff T x0 input.1 input.2)
    (eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
    exactIntegral le_rfl
  · simpa [eulerLatticeError] using
      (measurable_eulerLatticeError_joint bounds x0 hquantile).aestronglyMeasurable
  · simpa [eulerLatticeError] using hsampling
  · exact hbias

/-- Median total error for the Euler lattice estimator. -/
theorem corollary3_9_median
    {J stateDim noiseDim N k : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T q : ℝ} (hq : 1 ≤ q)
    (x0 : State stateDim)
    (hN : 2 ≤ N)
    (medianEstimator :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (exactIntegral : ℝ) {samplingBound biasBound : ℝ}
    (hmeas : AEStronglyMeasurable
      (fun input ↦ medianEstimator input -
        eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
      (repeatedRandomizedLatticeMeasure
        (ι := Index J noiseDim) N (2 * k - 1)))
    (hsampling :
      eLpNorm'
          (fun input ↦ medianEstimator input -
            eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
          q (repeatedRandomizedLatticeMeasure
            (ι := Index J noiseDim) N (2 * k - 1)) ≤
        ENNReal.ofReal samplingBound)
    (hbias :
      |eulerGaussianIntegral (J := J) drift diffusion payoff T x0 - exactIntegral| ≤
        biasBound) :
    eLpNorm' (fun input ↦ medianEstimator input - exactIntegral) q
        (repeatedRandomizedLatticeMeasure
          (ι := Index J noiseDim) N (2 * k - 1)) ≤
      ENNReal.ofReal samplingBound + ENNReal.ofReal biasBound := by
  letI : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty hN
  exact totalError_of_sampling_and_real_bias medianEstimator
    (eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
    exactIntegral hq hmeas hsampling hbias

/-- Paper Corollary 3.9 for the single rule, with the sampling and Euler rates displayed
in the conclusion. -/
theorem corollary3_9_single_rate
    {J stateDim noiseDim N : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x0 : State stateDim)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (hN : 2 ≤ N) (exactIntegral : ℝ)
    {samplingConstant biasConstant epsilon theta : ℝ}
    (hsampling :
      eLpNorm'
          (fun input : LatticeGenerator (Index J noiseDim) N ×
              LatticeShift (Index J noiseDim) ↦
            eulerLatticeError normalQuantile N drift diffusion payoff T x0
              input.1 input.2)
          1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
        ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon)))
    (hbias :
      |eulerGaussianIntegral (J := J) drift diffusion payoff T x0 - exactIntegral| ≤
        biasConstant * (numSteps J : ℝ) ^ (-theta)) :
    eLpNorm'
        (fun input : LatticeGenerator (Index J noiseDim) N ×
            LatticeShift (Index J noiseDim) ↦
          eulerLatticeRule normalQuantile N drift diffusion payoff T x0 input.1 input.2 -
            exactIntegral)
        1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon)) +
        ENNReal.ofReal (biasConstant * (numSteps J : ℝ) ^ (-theta)) := by
  exact corollary3_9_single bounds x0 hquantile hN exactIntegral
    hsampling hbias

/-- Paper Corollary 3.9 for the median rule, with the sampling and Euler rates displayed
in the conclusion. -/
theorem corollary3_9_median_rate
    {J stateDim noiseDim N k : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T q : ℝ} (hq : 1 ≤ q)
    (x0 : State stateDim) (hN : 2 ≤ N)
    (medianEstimator :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (exactIntegral : ℝ)
    {samplingConstant biasConstant epsilon theta : ℝ}
    (hmeas : AEStronglyMeasurable
      (fun input ↦ medianEstimator input -
        eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
      (repeatedRandomizedLatticeMeasure
        (ι := Index J noiseDim) N (2 * k - 1)))
    (hsampling :
      eLpNorm'
          (fun input ↦ medianEstimator input -
            eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
          q (repeatedRandomizedLatticeMeasure
            (ι := Index J noiseDim) N (2 * k - 1)) ≤
        ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon)))
    (hbias :
      |eulerGaussianIntegral (J := J) drift diffusion payoff T x0 - exactIntegral| ≤
        biasConstant * (numSteps J : ℝ) ^ (-theta)) :
    eLpNorm' (fun input ↦ medianEstimator input - exactIntegral) q
        (repeatedRandomizedLatticeMeasure
          (ι := Index J noiseDim) N (2 * k - 1)) ≤
      ENNReal.ofReal (samplingConstant * (N : ℝ) ^ (-1 + epsilon)) +
        ENNReal.ofReal (biasConstant * (numSteps J : ℝ) ^ (-theta)) := by
  exact corollary3_9_median hq x0 hN medianEstimator exactIntegral
    hmeas hsampling hbias

end

end TimeDependentLattice.Bias
