/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.PaperUniformTheorems
import TimeDependentLattice.Bias.PaperMedianTotalError

/-!
# Dimension-uniform total error for the paper's actual estimators

These forms of Corollary 3.9 in the paper call the dimension-uniform sampling theorem directly
and use Assumption 3.6 for the Euler bias. The bias constant is one scalar common to the models
under consideration; no numerical sampling-error estimate is an additional input.
-/

namespace TimeDependentLattice.Bias

noncomputable section

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Sampling TimeDependentLattice.Trees

variable {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
  {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε : ℝ}
  {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ} {x₀ : State stateDim}

/-- Corollary 3.9, dimension-uniform single rule, from Corollary 3.4 and Assumption 3.6. -/
theorem corollary3_9_single_uniform_paper
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    {R₀ : ℝ} (hinitial : ‖x₀‖ ≤ R₀) {M : NNReal}
    (hcolumns : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
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
      uniformEulerSamplingConstant bounds K₀ R₀ M ε * (N : ℝ) ^ (-1 + ε) +
        C_bias * (numSteps J : ℝ) ^ (-θ) := by
  let : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty sampling.prime_points.two_le
  have hs : 0 ≤ uniformEulerSamplingConstant bounds K₀ R₀ M ε *
      (N : ℝ) ^ (-1 + ε) := mul_nonneg
    (uniformEulerSamplingConstant_pos bounds K₀ R₀ M
      sampling.epsilon_pos sampling.epsilon_lt_half).le
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  simpa only [ENNReal.ofReal_one, eulerLatticeRule] using totalError_real_of_sampling_and_bias
    (measurable_gaussianLatticeRule_joint sampling.quantile_measurable N
      (measurable_rawEulerIntegrand bounds x₀)) le_rfl hs
    (sampling.single_uniform_bound hinitial hcolumns) hbias

/-- Corollary 3.9, dimension-uniform median, retaining the exact prefactor in equation (5.11). -/
theorem corollary3_9_median_uniform_paper
    {k : ℕ} {q : ℝ}
    (sampling : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    {R₀ : ℝ} (hinitial : ‖x₀‖ ≤ R₀) {M : NNReal}
    (hcolumns : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
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
      uniformEulerMedianSamplingConstant bounds K₀ R₀ M ε q k * (N : ℝ) ^ (-1 + ε) +
        C_bias * (numSteps J : ℝ) ^ (-θ) := by
  let : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty sampling.prime_points.two_le
  have hs : 0 ≤ uniformEulerMedianSamplingConstant bounds K₀ R₀ M ε q k *
      (N : ℝ) ^ (-1 + ε) := mul_nonneg
    (uniformEulerMedianSamplingConstant_pos bounds K₀ R₀ M
      sampling.epsilon_pos sampling.epsilon_lt_half hk (by linarith) hRange).le
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  exact totalError_real_of_sampling_and_bias
    (measurable_eulerMedian bounds x₀ sampling.quantile_measurable hk medianEstimator hmedian)
    hq hs (sampling.median_uniform_bound hinitial hcolumns hk hq hRange medianEstimator hmedian)
    hbias

end

end TimeDependentLattice.Bias
