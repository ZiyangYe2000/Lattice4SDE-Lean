/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.PaperTheorems

/-!
# Dimension-uniform real sampling bounds

These are the single and median parts of Corollary 3.4 in the paper. The common initial-data and
diffusion-column bounds replace the dimension-dependent quantities in Theorem 3.1, while the
median multiplier is exactly the one in equation (5.11).
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- The common median constant in Corollary 3.4, with the prefactor of equation (5.11). -/
def uniformEulerMedianSamplingConstant
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ R₀ : ℝ) (M : NNReal)
    (ε q : ℝ) (k : ℕ) : ℝ :=
  medianPaperPrefactorReal (2 * k - 1) k (2 * samplingLambda ε) q *
    uniformEulerSamplingConstant bounds K₀ R₀ M ε

private theorem uniform_median_exponent_range {ε q : ℝ} {k : ℕ}
    (hRange : q < k / (1 - ε)) : q < (2 * samplingLambda ε) * k := by
  rw [two_mul_samplingLambda]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hRange

theorem uniformEulerMedianSamplingConstant_pos
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T ε q : ℝ}
    {k : ℕ} (bounds : GevreyBounds drift payoff T) (K₀ R₀ : ℝ) (M : NNReal)
    (hε : 0 < ε) (hεHalf : ε < 1 / 2) (hk : 0 < k) (hq : 0 < q)
    (hRange : q < k / (1 - ε)) :
    0 < uniformEulerMedianSamplingConstant bounds K₀ R₀ M ε q k := by
  have hη : 0 < 2 * samplingLambda ε := zero_lt_one.trans_le
    (one_le_two_mul_samplingLambda hε hεHalf)
  exact mul_pos
    (medianPaperPrefactorReal_pos (by omega) hη hk hq
      (uniform_median_exponent_range hRange))
    (uniformEulerSamplingConstant_pos bounds K₀ R₀ M hε hεHalf)

section Single

variable {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
  {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε : ℝ}
  {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ} {x₀ : State stateDim}

/-- The actual single-rule error lies in `L¹`, with the dimension-uniform real bound of
Corollary 3.4. -/
theorem EulerSamplingInputs.single_uniform_real
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    {R₀ : ℝ} (hinitial : ‖x₀‖ ≤ R₀) {M : NNReal}
    (hcolumns : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M) :
    MemLp (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2)
      1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ∧
    lpNorm (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2)
      1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      uniformEulerSamplingConstant bounds K₀ R₀ M ε * (N : ℝ) ^ (-1 + ε) := by
  have hm := (measurable_eulerLatticeError_joint (J := J) (N := N)
    (diffusion := diffusion) bounds x₀
    data.quantile_measurable).aestronglyMeasurable
      (μ := randomizedLatticeMeasure (ι := Index J noiseDim) N)
  have hc : 0 ≤ uniformEulerSamplingConstant bounds K₀ R₀ M ε *
      (N : ℝ) ^ (-1 + ε) := mul_nonneg
    (uniformEulerSamplingConstant_pos bounds K₀ R₀ M
      data.epsilon_pos data.epsilon_lt_half).le
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hbound := data.single_uniform_bound hinitial hcolumns
  constructor
  · simpa using memLp_of_eLpNorm'_le_real (by norm_num : (0 : ℝ) < 1) hm hbound
  · simpa using lpNorm_le_of_eLpNorm'_le_real (by norm_num : (0 : ℝ) < 1) hc hm hbound

end Single

section Median

variable {J stateDim noiseDim N k : ℕ} {drift : Drift stateDim}
  {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε q : ℝ}
  {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ} {x₀ : State stateDim}

/-- Corollary 3.4 for the actual median, with the exact common real constant inside `ofReal`. -/
theorem EulerSamplingInputs.median_uniform_bound
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    {R₀ : ℝ} (hinitial : ‖x₀‖ ≤ R₀) {M : NNReal}
    (hcolumns : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε))
    (medianEstimator :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input, IsOddMedian k
      (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
        (input i).1 (input i).2) (medianEstimator input)) :
    eLpNorm' (fun input ↦ medianEstimator input - eulerGaussianIntegral (J := J)
        drift diffusion payoff T x₀) q
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ≤
      ENNReal.ofReal (uniformEulerMedianSamplingConstant bounds K₀ R₀ M ε q k *
        (N : ℝ) ^ (-1 + ε)) := by
  have hη : 0 < 2 * samplingLambda ε := zero_lt_one.trans_le
    (one_le_two_mul_samplingLambda data.epsilon_pos data.epsilon_lt_half)
  have hq0 : 0 < q := by linarith
  have hqη := uniform_median_exponent_range hRange
  have hpref := medianPaperPrefactorReal_nonneg (R := 2 * k - 1) hη hk hq0 hqη
  have h := corollary3_4_median_lattice bounds data.time_pos data.origin_nonneg x₀
    hinitial hcolumns data.drift_origin data.quantile_measurable data.prime_points
    data.epsilon_pos data.epsilon_lt_half hq hk hRange data.wce_measurable
    data.shift_bound data.random_wce_bound medianEstimator hmedian
  rw [medianPaperPrefactor_eq_ofReal hη hk hq0 hqη,
    ennreal_sampling_rate_eq
      (dimensionUniformLatticeMomentConstant_pos bounds K₀ R₀ M
        (samplingLambda_mem_interval data.epsilon_pos data.epsilon_lt_half).1).le
      (by linarith [data.epsilon_lt_half]) data.prime_points.pos,
    ← ENNReal.ofReal_mul hpref] at h
  have hexp : -(1 - ε) = -1 + ε := by ring
  simpa only [uniformEulerMedianSamplingConstant, uniformEulerSamplingConstant,
    hexp, mul_assoc] using h

/-- The actual median error belongs to `L^q` and satisfies the dimension-uniform real norm
bound in Corollary 3.4. -/
theorem EulerSamplingInputs.median_uniform_real
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    {R₀ : ℝ} (hinitial : ‖x₀‖ ≤ R₀) {M : NNReal}
    (hcolumns : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε))
    (medianEstimator :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input, IsOddMedian k
      (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
        (input i).1 (input i).2) (medianEstimator input)) :
    MemLp (fun input ↦ medianEstimator input - eulerGaussianIntegral (J := J)
        drift diffusion payoff T x₀) (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ∧
    lpNorm (fun input ↦ medianEstimator input - eulerGaussianIntegral (J := J)
        drift diffusion payoff T x₀) (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ≤
      uniformEulerMedianSamplingConstant bounds K₀ R₀ M ε q k *
        (N : ℝ) ^ (-1 + ε) := by
  have hmedianMeas :=
    (measurable_eulerMedian bounds x₀ data.quantile_measurable hk medianEstimator hmedian).sub_const
      (eulerGaussianIntegral (J := J) drift diffusion payoff T x₀)
  have hc : 0 ≤ uniformEulerMedianSamplingConstant bounds K₀ R₀ M ε q k *
      (N : ℝ) ^ (-1 + ε) := mul_nonneg
    (uniformEulerMedianSamplingConstant_pos bounds K₀ R₀ M
      data.epsilon_pos data.epsilon_lt_half hk (by linarith) hRange).le
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hbound := data.median_uniform_bound hinitial hcolumns hk hq hRange medianEstimator hmedian
  exact ⟨memLp_of_eLpNorm'_le_real (by linarith) hmedianMeas.aestronglyMeasurable hbound,
    lpNorm_le_of_eLpNorm'_le_real (by linarith) hc hmedianMeas.aestronglyMeasurable hbound⟩

end Median

end

end TimeDependentLattice.Sampling
