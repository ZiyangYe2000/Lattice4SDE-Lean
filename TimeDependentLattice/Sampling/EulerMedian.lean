/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.EulerMain
import TimeDependentLattice.Sampling.MedianRate

/-!
# Median sampling theorem for the Euler lattice estimator

This file realizes the `R = 2k - 1` independent copies in paper Theorem 3.1 as a finite product
probability space and applies the already-proved median moment estimate.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- Median part of paper Theorem 3.1 for the explicitly defined Euler lattice estimators.

The hypothesis `hmedian` says that `medianEstimator` is a median of the `2k-1` estimates.  The two
`wce` hypotheses are the same cited random-wce interface as in the single-rule theorem. -/
theorem theorem3_1_median_lattice
    {J stateDim noiseDim N k : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim)
    (horigin : ∀ t, 0 ≤ t → t ≤ T → ‖drift t 0‖ ≤ K₀)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (hNprime : Nat.Prime N)
    {ε q : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    (hqOne : 1 ≤ q) (hk : 0 < k) (hqRange : q < k / (1 - ε))
    {wce : LatticeGenerator (Index J noiseDim) N → ℝ≥0∞}
    (hwceMeas : Measurable wce)
    (hshift : ∀ generator,
      (∫⁻ shift,
          ‖eulerLatticeError normalQuantile N drift diffusion payoff T x₀
              generator shift‖ₑ ^ (2 : ℝ)
          ∂uniformShiftMeasure (Index J noiseDim)) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter
                (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
              zeroDiv
                (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x₀ u ^ 2)
                (auxiliarySubsetWeight (eulerSamplingRho diffusion bounds ε)
                  (samplingLambda ε)
                  (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x₀) u)) *
          wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator,
        wce generator ^ (2 * samplingLambda ε)
          ∂uniformGeneratorMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter
              (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
            auxiliarySubsetWeight (eulerSamplingRho diffusion bounds ε)
                (samplingLambda ε)
                (eulerGaussianSpaceComponent
                  drift diffusion payoff T bounds x₀) u ^
              samplingLambda ε *
                eulerSamplingRho diffusion bounds ε ^ u.card) /
        ((N - 1 : ℕ) : ℝ≥0∞))
    (medianEstimator :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input,
      IsOddMedian k
        (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
          (input i).1 (input i).2)
        (medianEstimator input)) :
    eLpNorm'
        (fun input ↦ medianEstimator input -
          eulerGaussianIntegral (J := J) drift diffusion payoff T x₀)
        q (repeatedRandomizedLatticeMeasure
          (ι := Index J noiseDim) N (2 * k - 1)) ≤
      medianPaperPrefactor (2 * k - 1) k (2 * samplingLambda ε) q *
        ((2 * ENNReal.ofReal
          (latticeUniformMomentConstant (diffusion := diffusion)
            bounds (eulerSamplingRho diffusion bounds ε) (samplingLambda ε)
              (eulerTransferConstant diffusion bounds K₀ x₀))) /
          (N : ℝ≥0∞)) ^ (1 - ε) := by
  letI : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty hNprime.two_le
  have hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖ := by
    intro z i hi
    exact bounds.drift_norm_le_origin_add_lipschitz horigin
      (gridTime_nonneg hT.le J i)
      (gridTime_le_terminal hT.le J (Nat.le_of_lt hi)) _
  have hρ : 0 < eulerSamplingRho diffusion bounds ε :=
    eulerSamplingRho_pos bounds hεPos hεHalf
  let Pair := LatticeGenerator (Index J noiseDim) N ×
    LatticeShift (Index J noiseDim)
  let μPair : Measure Pair := randomizedLatticeMeasure (ι := Index J noiseDim) N
  let error : Pair → ℝ := fun input ↦
    eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2
  let value : Fin (2 * k - 1) →
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ :=
    fun i input ↦ error (input i)
  have herror : Measurable error := by
    simpa [error, Pair] using measurable_eulerLatticeError_joint bounds x₀ hquantile
  have hsingle := euler_lattice_fractional_moment bounds hT hK₀ x₀ hdrift
    hquantile hNprime hρ
    (samplingLambda_mem_interval hεPos hεHalf).1
    (samplingLambda_mem_interval hεPos hεHalf).2
    hwceMeas hshift hwce
  have hcopyMoment : ∀ i,
      (∫⁻ input,
          ‖value i input‖ₑ ^ (2 * samplingLambda ε)
          ∂repeatedRandomizedLatticeMeasure
            (ι := Index J noiseDim) N (2 * k - 1)) ≤
        ENNReal.ofReal
            (latticeUniformMomentConstant (diffusion := diffusion)
              bounds (eulerSamplingRho diffusion bounds ε) (samplingLambda ε)
                (eulerTransferConstant diffusion bounds K₀ x₀)) /
          ((N - 1 : ℕ) : ℝ≥0∞) := by
    intro i
    have hpres : MeasurePreserving (Function.eval i)
        (repeatedRandomizedLatticeMeasure
          (ι := Index J noiseDim) N (2 * k - 1)) μPair := by
      simpa [repeatedRandomizedLatticeMeasure, μPair] using
        (measurePreserving_eval
          (fun _ : Fin (2 * k - 1) ↦
            randomizedLatticeMeasure (ι := Index J noiseDim) N) i)
    have htransport := hpres.lintegral_comp
      (f := fun input : Pair ↦ ‖error input‖ₑ ^ (2 * samplingLambda ε))
      (ENNReal.continuous_rpow_const.measurable.comp herror.enorm)
    calc
      (∫⁻ input, ‖value i input‖ₑ ^ (2 * samplingLambda ε)
          ∂repeatedRandomizedLatticeMeasure
            (ι := Index J noiseDim) N (2 * k - 1)) =
          ∫⁻ input : Pair, ‖error input‖ₑ ^ (2 * samplingLambda ε) ∂μPair := by
            simpa [value] using htransport
      _ ≤ _ := by simpa [error, Pair, μPair] using hsingle
  have hvaluesMeas : ∀ i, Measurable (value i) := by
    intro i
    exact herror.comp (measurable_pi_apply i)
  have hvaluesIndep : iIndepFun value
      (repeatedRandomizedLatticeMeasure
        (ι := Index J noiseDim) N (2 * k - 1)) := by
    simpa [value, error, Pair, repeatedRandomizedLatticeMeasure, μPair] using
      (iIndepFun_pi (μ := fun _ : Fin (2 * k - 1) ↦ μPair)
        (X := fun _ ↦ error) (fun _ ↦ herror.aemeasurable))
  have hmedianError : ∀ input,
      IsOddMedian k (fun i ↦ value i input)
        (medianEstimator input -
          eulerGaussianIntegral (J := J) drift diffusion payoff T x₀) := by
    intro input
    simpa [value, error, Pair, eulerLatticeError] using
      (hmedian input).sub_const
        (eulerGaussianIntegral (J := J) drift diffusion payoff T x₀)
  simpa only [Fintype.card_fin] using median_lq_rate_of_fractional_moment_paper
    (by simp) hmedianError hvaluesMeas hvaluesIndep hεPos hεHalf
    (lt_of_lt_of_le zero_lt_one hqOne) hk hqRange hNprime.two_le hcopyMoment

/-- The selected odd median of the actual measurable Euler estimates is measurable.  This
discharges the ordinary `L^q` interpretation without a further estimator assumption. -/
theorem measurable_eulerMedian
    {J stateDim noiseDim N k : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile) (hk : 0 < k)
    (medianEstimator :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input,
      IsOddMedian k
        (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
          (input i).1 (input i).2)
        (medianEstimator input)) : Measurable medianEstimator := by
  apply measurable_oddMedian (by simp; omega) hmedian
  intro i
  have hproj : Measurable (fun input :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) ↦ input i) :=
    measurable_pi_apply i
  have h := ((measurable_eulerLatticeError_joint (J := J) (N := N)
    (diffusion := diffusion) bounds x₀ hquantile).comp
    hproj).add
      (measurable_const (a := eulerGaussianIntegral (J := J) drift diffusion payoff T x₀))
  change Measurable (fun input :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) ↦
    (eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ (input i).1 (input i).2 -
      eulerGaussianIntegral (J := J) drift diffusion payoff T x₀) +
      eulerGaussianIntegral (J := J) drift diffusion payoff T x₀) at h
  simpa only [sub_add_cancel] using h

end

end TimeDependentLattice.Sampling
