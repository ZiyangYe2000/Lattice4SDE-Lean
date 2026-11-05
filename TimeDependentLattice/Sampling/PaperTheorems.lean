/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.PaperConstants
import TimeDependentLattice.Sampling.RealBounds

/-!
# Real-valued sampling theorems for the paper's Euler integrand

The input record collects Assumption 2.1 and the two quoted lattice-error inequalities.
Its methods give the actual single and median estimators with the constants of (5.10)--(5.11).
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- The model conditions and cited lattice estimates used in Theorem 3.1. -/
structure EulerSamplingInputs
    {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (normalQuantile : ℝ → ℝ)
    (K₀ ε : ℝ) (x₀ : State stateDim) where
  time_pos : 0 < T
  origin_nonneg : 0 ≤ K₀
  drift_origin : ∀ t, 0 ≤ t → t ≤ T → ‖drift t 0‖ ≤ K₀
  quantile_measurable : Measurable normalQuantile
  prime_points : Nat.Prime N
  epsilon_pos : 0 < ε
  epsilon_lt_half : ε < 1 / 2
  wce : LatticeGenerator (Index J noiseDim) N → ℝ≥0∞
  wce_measurable : Measurable wce
  shift_bound :
    let B := eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀
    let γ := auxiliarySubsetWeight (eulerSamplingRho diffusion bounds ε) (samplingLambda ε) B
    ∀ a, (∫⁻ shift,
      ‖eulerLatticeError normalQuantile N drift diffusion payoff T x₀ a shift‖ₑ ^ (2 : ℝ)
        ∂uniformShiftMeasure (Index J noiseDim)) ≤
      ENNReal.ofReal (∑ u ∈ Finset.univ.powerset.filter
        (fun u : Finset (Index J noiseDim) ↦ u.Nonempty), zeroDiv (B u ^ 2) (γ u)) *
          wce a ^ (2 : ℝ)
  random_wce_bound :
    let B := eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀
    let γ := auxiliarySubsetWeight (eulerSamplingRho diffusion bounds ε) (samplingLambda ε) B
    (∫⁻ a, wce a ^ (2 * samplingLambda ε)
      ∂uniformGeneratorMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal (∑ u ∈ Finset.univ.powerset.filter
        (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
        γ u ^ samplingLambda ε * eulerSamplingRho diffusion bounds ε ^ u.card) /
          ((N - 1 : ℕ) : ℝ≥0∞)

/-- The paper's `C_epsilon` in (5.10); it is independent of the number of time steps. -/
def eulerSamplingConstant
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ ε : ℝ) (x₀ : State stateDim) : ℝ :=
  2 ^ (1 - ε) *
    eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀ ^ (1 - ε)

/-- Equation (5.10), with the original paper moment constant from (5.8). -/
theorem eulerSamplingConstant_eq_paper_formula
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim)
    (hε : 0 < ε) (hεHalf : ε < 1 / 2) :
    eulerSamplingConstant diffusion bounds K₀ ε x₀ =
      2 ^ (1 / (2 * samplingLambda ε)) *
        eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀ ^
          (1 / (2 * samplingLambda ε)) := by
  rw [one_div_two_mul_samplingLambda (by linarith : ε < 1)]
  rfl

theorem eulerSamplingConstant_nonneg
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ ε : ℝ) (x₀ : State stateDim) :
    0 ≤ eulerSamplingConstant diffusion bounds K₀ ε x₀ := by
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (eulerPaperLatticeMomentConstant_nonneg diffusion bounds K₀ ε x₀) _)

theorem eulerTransferConstant_pos
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim) :
    0 < eulerTransferConstant diffusion bounds K₀ x₀ := by
  apply Real.sqrt_pos.2
  unfold auxiliaryMomentConstant
  apply mul_pos
  · exact mul_pos (Real.exp_pos _) (zero_lt_one.trans_le
      (one_le_hybridCoordinateMomentBound _ _))
  · exact Real.rpow_pos_of_pos (by norm_num) _

theorem eulerSamplingConstant_pos
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim)
    (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    0 < eulerSamplingConstant diffusion bounds K₀ ε x₀ := by
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos
      (eulerPaperLatticeMomentConstant_pos diffusion bounds K₀ x₀ hεPos hεHalf) _)

private theorem eulerSamplingRate_le_paper
    {stateDim noiseDim N : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim)
    (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε < 1 / 2) (hN : 0 < N) :
    ((2 * ENNReal.ofReal
      (latticeUniformMomentConstant (diffusion := diffusion) bounds
        (eulerSamplingRho diffusion bounds ε) (samplingLambda ε)
        (eulerTransferConstant diffusion bounds K₀ x₀))) / (N : ℝ≥0∞)) ^ (1 - ε) ≤
      ENNReal.ofReal (eulerSamplingConstant diffusion bounds K₀ ε x₀ *
        (N : ℝ) ^ (-1 + ε)) := by
  have hconstant := latticeUniformMomentConstant_le_eulerPaperLatticeMomentConstant
    diffusion bounds K₀ x₀ hT hε hεHalf
  have hbase :
      (2 * ENNReal.ofReal (latticeUniformMomentConstant (diffusion := diffusion) bounds
        (eulerSamplingRho diffusion bounds ε) (samplingLambda ε)
        (eulerTransferConstant diffusion bounds K₀ x₀))) / (N : ℝ≥0∞) ≤
      (2 * ENNReal.ofReal (eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀)) /
        (N : ℝ≥0∞) := by
    exact ENNReal.div_le_div_right
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hconstant) bot_le) _
  refine (ENNReal.rpow_le_rpow hbase (by linarith : 0 ≤ 1 - ε)).trans_eq ?_
  rw [ennreal_sampling_rate_eq
    (eulerPaperLatticeMomentConstant_nonneg diffusion bounds K₀ ε x₀)
    (by linarith : 0 ≤ 1 - ε) hN]
  have hexp : -(1 - ε) = -1 + ε := by ring
  simp only [eulerSamplingConstant, hexp]

/-- Theorem 3.1, single-rule part, with the paper's real constant and displayed `N` rate. -/
theorem EulerSamplingInputs.single_bound
    {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε : ℝ}
    {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ}
    {x₀ : State stateDim}
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀) :
    eLpNorm' (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2)
      1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal (eulerSamplingConstant diffusion bounds K₀ ε x₀ *
        (N : ℝ) ^ (-1 + ε)) := by
  have h := theorem3_1_single_lattice bounds data.time_pos data.origin_nonneg x₀
    data.drift_origin data.quantile_measurable data.prime_points
    data.epsilon_pos data.epsilon_lt_half data.wce_measurable
    data.shift_bound data.random_wce_bound
  exact h.trans (eulerSamplingRate_le_paper diffusion bounds K₀ x₀ data.time_pos
    data.epsilon_pos data.epsilon_lt_half data.prime_points.pos)

/-- The single-rule error is an actual `L¹` random variable and has the rate in Theorem 3.1. -/
theorem EulerSamplingInputs.single_real
    {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε : ℝ}
    {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ}
    {x₀ : State stateDim}
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀) :
    MemLp (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2)
      1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ∧
    lpNorm (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2)
      1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      eulerSamplingConstant diffusion bounds K₀ ε x₀ * (N : ℝ) ^ (-1 + ε) := by
  have hm := (measurable_eulerLatticeError_joint (J := J) (N := N)
    (diffusion := diffusion) bounds x₀
    data.quantile_measurable).aestronglyMeasurable
      (μ := randomizedLatticeMeasure (ι := Index J noiseDim) N)
  have hc : 0 ≤ eulerSamplingConstant diffusion bounds K₀ ε x₀ *
      (N : ℝ) ^ (-1 + ε) := by
    exact mul_nonneg (eulerSamplingConstant_nonneg diffusion bounds K₀ ε x₀)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  constructor
  · simpa using memLp_of_eLpNorm'_le_real (by norm_num : (0 : ℝ) < 1) hm data.single_bound
  · simpa using lpNorm_le_of_eLpNorm'_le_real (by norm_num : (0 : ℝ) < 1)
      hc hm data.single_bound

section Median

variable {J stateDim noiseDim N k : ℕ} {drift : Drift stateDim}
  {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε q : ℝ}
  {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ} {x₀ : State stateDim}

/-- The paper's median constant in (5.11). -/
def eulerMedianSamplingConstant (diffusion : Diffusion stateDim noiseDim)
    (bounds : GevreyBounds drift payoff T) (K₀ ε q : ℝ) (k : ℕ)
    (x₀ : State stateDim) : ℝ :=
  medianPaperPrefactorReal (2 * k - 1) k (2 * samplingLambda ε) q *
    eulerSamplingConstant diffusion bounds K₀ ε x₀

private theorem median_exponent_range (hRange : q < k / (1 - ε)) :
    q < (2 * samplingLambda ε) * k := by
  rw [two_mul_samplingLambda]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hRange

theorem eulerMedianSamplingConstant_pos
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε)) :
    0 < eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ := by
  have hη : 0 < 2 * samplingLambda ε := zero_lt_one.trans_le
    (one_le_two_mul_samplingLambda data.epsilon_pos data.epsilon_lt_half)
  exact mul_pos
    (medianPaperPrefactorReal_pos (by omega) hη hk (by linarith)
      (median_exponent_range hRange))
    (eulerSamplingConstant_pos diffusion bounds K₀ x₀ data.epsilon_pos data.epsilon_lt_half)

/-- Theorem 3.1, median part, with exactly the prefactor in (5.11). -/
theorem EulerSamplingInputs.median_bound
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε))
    (M : RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input, IsOddMedian k
      (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
        (input i).1 (input i).2) (M input)) :
    eLpNorm' (fun input ↦ M input - eulerGaussianIntegral (J := J)
        drift diffusion payoff T x₀) q
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ≤
      ENNReal.ofReal (eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ *
        (N : ℝ) ^ (-1 + ε)) := by
  have hη : 0 < 2 * samplingLambda ε := zero_lt_one.trans_le
    (one_le_two_mul_samplingLambda data.epsilon_pos data.epsilon_lt_half)
  have hq0 : 0 < q := by linarith
  have hqη := median_exponent_range hRange
  have hpref := medianPaperPrefactorReal_nonneg (R := 2 * k - 1) hη hk hq0 hqη
  have h := theorem3_1_median_lattice bounds data.time_pos data.origin_nonneg x₀
    data.drift_origin data.quantile_measurable data.prime_points
    data.epsilon_pos data.epsilon_lt_half hq hk hRange data.wce_measurable
    data.shift_bound data.random_wce_bound M hmedian
  have hpaper := h.trans (mul_le_mul_of_nonneg_left
    (eulerSamplingRate_le_paper diffusion bounds K₀ x₀ data.time_pos
      data.epsilon_pos data.epsilon_lt_half data.prime_points.pos) bot_le)
  rw [medianPaperPrefactor_eq_ofReal hη hk hq0 hqη,
    ← ENNReal.ofReal_mul hpref] at hpaper
  simpa only [eulerMedianSamplingConstant, mul_assoc] using hpaper

/-- The median error belongs to `L^q` and satisfies the real norm form of Theorem 3.1. -/
theorem EulerSamplingInputs.median_real
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    (hk : 0 < k) (hq : 1 ≤ q) (hRange : q < k / (1 - ε))
    (M : RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input, IsOddMedian k
      (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x₀
        (input i).1 (input i).2) (M input)) :
    MemLp (fun input ↦ M input - eulerGaussianIntegral (J := J)
        drift diffusion payoff T x₀) (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ∧
    lpNorm (fun input ↦ M input - eulerGaussianIntegral (J := J)
        drift diffusion payoff T x₀) (ENNReal.ofReal q)
      (repeatedRandomizedLatticeMeasure (ι := Index J noiseDim) N (2 * k - 1)) ≤
      eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ *
        (N : ℝ) ^ (-1 + ε) := by
  have hM := (measurable_eulerMedian bounds x₀ data.quantile_measurable hk M hmedian).sub_const
    (eulerGaussianIntegral (J := J) drift diffusion payoff T x₀)
  have hc : 0 ≤ eulerMedianSamplingConstant diffusion bounds K₀ ε q k x₀ *
      (N : ℝ) ^ (-1 + ε) := mul_nonneg
    (eulerMedianSamplingConstant_pos data hk hq hRange).le
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hbound := data.median_bound hk hq hRange M hmedian
  exact ⟨memLp_of_eLpNorm'_le_real (by linarith) hM.aestronglyMeasurable hbound,
    lpNorm_le_of_eLpNorm'_le_real (by linarith) hc hM.aestronglyMeasurable hbound⟩

end Median

section Uniform

variable {J stateDim noiseDim N : ℕ} {drift : Drift stateDim}
  {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K₀ ε : ℝ}
  {bounds : GevreyBounds drift payoff T} {normalQuantile : ℝ → ℝ} {x₀ : State stateDim}

/-- The dimension-uniform version of the paper's single-rule constant. -/
def uniformEulerSamplingConstant (bounds : GevreyBounds drift payoff T)
    (K₀ R₀ : ℝ) (M : NNReal) (ε : ℝ) : ℝ :=
  2 ^ (1 - ε) * (dimensionUniformLatticeMomentConstant bounds K₀ R₀ M
    (dimensionUniformSamplingRho bounds M ε) (samplingLambda ε)) ^ (1 - ε)

theorem uniformEulerSamplingConstant_pos (bounds : GevreyBounds drift payoff T)
    (K₀ R₀ : ℝ) (M : NNReal) (hε : 0 < ε) (hεHalf : ε < 1 / 2) :
    0 < uniformEulerSamplingConstant bounds K₀ R₀ M ε := by
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (dimensionUniformLatticeMomentConstant_pos bounds K₀ R₀ M
      (samplingLambda_mem_interval hε hεHalf).1) _)

/-- Corollary 3.4, with a constant containing neither finite dimension. -/
theorem EulerSamplingInputs.single_uniform_bound
    (data : EulerSamplingInputs (J := J) (N := N)
      diffusion bounds normalQuantile K₀ ε x₀)
    {R₀ : ℝ} (hinitial : ‖x₀‖ ≤ R₀) {M : NNReal}
    (hcolumns : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M) :
    eLpNorm' (fun input : LatticeGenerator (Index J noiseDim) N ×
        LatticeShift (Index J noiseDim) ↦
      eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2)
      1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal (uniformEulerSamplingConstant bounds K₀ R₀ M ε *
        (N : ℝ) ^ (-1 + ε)) := by
  have h := corollary3_4_single_lattice bounds data.time_pos data.origin_nonneg x₀
    hinitial hcolumns data.drift_origin data.quantile_measurable data.prime_points
    data.epsilon_pos data.epsilon_lt_half data.wce_measurable
    data.shift_bound data.random_wce_bound
  rw [ennreal_sampling_rate_eq
    (dimensionUniformLatticeMomentConstant_pos bounds K₀ R₀ M
      (samplingLambda_mem_interval data.epsilon_pos data.epsilon_lt_half).1).le
    (by linarith [data.epsilon_lt_half]) data.prime_points.pos] at h
  have hexp : -(1 - ε) = -1 + ε := by ring
  simpa only [uniformEulerSamplingConstant, hexp] using h

end Uniform

end

end TimeDependentLattice.Sampling
