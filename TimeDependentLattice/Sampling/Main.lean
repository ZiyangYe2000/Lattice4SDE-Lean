/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.Rate

/-!
# Assembly of the sampling-error proof

This file joins the paper-specific derivative estimate (Theorem 4.1), the transfer estimate
(Lemma 5.2), the optimized random-lattice moment (Proposition 5.3), and the final rate argument.
The cited random-wce estimate is deliberately visible as the hypothesis `hwce`.
-/

namespace TimeDependentLattice.Sampling

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

noncomputable section

/-- An intermediate lattice moment bound retaining the actual intermediate column sum.
`Sampling/PaperConstants.lean` lifts this bound to the paper's constant in (5.8). -/
def latticeUniformMomentConstant
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (ρ lam transferConstant : ℝ) : ℝ :=
  (transferConstant ^ latticeDerivativeExponent lam *
    derivativeSummabilityConstant (diffusion := diffusion) bounds ρ lam) ^ (1 + lam)

/-- The uniform fractional moment obtained by inserting Lemma 5.2 and Theorem 4.1 into
Proposition 5.3. -/
theorem uniform_fractional_moment_of_theorem4_1
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim)
    {Generator Shift : Type*}
    [MeasurableSpace Generator] [MeasurableSpace Shift]
    {μGenerator : Measure Generator} {μShift : Measure Shift}
    [IsProbabilityMeasure μGenerator] [IsProbabilityMeasure μShift]
    {error : Generator → Shift → ℝ} {wce : Generator → ℝ≥0∞}
    (herror : ∀ generator, Measurable (error generator))
    (herrorJoint : Measurable (Function.uncurry error))
    (hwceMeas : Measurable wce)
    {ρ lam transferConstant : ℝ}
    (hρ : 0 < ρ) (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1)
    (htransferConstant : 0 ≤ transferConstant)
    (B : Finset (Index J noiseDim) → ℝ) (hBnonneg : ∀ u, 0 ≤ B u)
    (htransfer : ∀ u, u.Nonempty →
      B u ≤ transferConstant * normalizedDerivativeEnvelope
        drift diffusion payoff T bounds.β x₀ u)
    {denominator : ℝ≥0∞}
    (hshift : ∀ generator,
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 : ℝ) ∂μShift) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter
                (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
              zeroDiv (B u ^ 2) (auxiliarySubsetWeight ρ lam B u)) *
          wce generator ^ (2 : ℝ))
    /- External cited input: paper Lemma 2.5 at the optimized weights. -/
    (hwce : (∫⁻ generator, wce generator ^ (2 * lam) ∂μGenerator) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter
              (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
            auxiliarySubsetWeight ρ lam B u ^ lam * ρ ^ u.card) /
        denominator) :
    (∫⁻ input : Generator × Shift,
      ‖Function.uncurry error input‖ₑ ^ (2 * lam)
        ∂μGenerator.prod μShift) ≤
      ENNReal.ofReal
          (latticeUniformMomentConstant
            (diffusion := diffusion) bounds ρ lam transferConstant) /
        denominator := by
  have hprop := proposition5_3_prod herror herrorJoint hwceMeas
    hρ hlamLower hlamUpper hBnonneg hshift hwce
  have hscale := latticeMomentScale_normalizedDerivativeEnvelope_le
    bounds hT x₀ hρ hlamLower hlamUpper htransferConstant B hBnonneg htransfer
  calc
    (∫⁻ input : Generator × Shift,
        ‖Function.uncurry error input‖ₑ ^ (2 * lam)
          ∂μGenerator.prod μShift) ≤
        ENNReal.ofReal (latticeMomentScale ρ lam B) / denominator := hprop
    _ ≤ ENNReal.ofReal
          (latticeUniformMomentConstant
            (diffusion := diffusion) bounds ρ lam transferConstant) /
        denominator := by
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hscale) denominator

/-- Single-rule part of Theorem 3.1 after the local weighted-norm transfer and the cited
random-wce estimate have been supplied.  Its right-hand side is exactly a constant times
`N^(-1+epsilon)`, written without negative powers. -/
theorem theorem3_1_single_core
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim)
    {Generator Shift : Type*}
    [MeasurableSpace Generator] [MeasurableSpace Shift]
    {μGenerator : Measure Generator} {μShift : Measure Shift}
    [IsProbabilityMeasure μGenerator] [IsProbabilityMeasure μShift]
    {error : Generator → Shift → ℝ} {wce : Generator → ℝ≥0∞}
    (herror : ∀ generator, Measurable (error generator))
    (herrorJoint : Measurable (Function.uncurry error))
    (hwceMeas : Measurable wce)
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    {ρ transferConstant : ℝ} (hρ : 0 < ρ)
    (htransferConstant : 0 ≤ transferConstant)
    (B : Finset (Index J noiseDim) → ℝ) (hBnonneg : ∀ u, 0 ≤ B u)
    (htransfer : ∀ u, u.Nonempty →
      B u ≤ transferConstant * normalizedDerivativeEnvelope
        drift diffusion payoff T bounds.β x₀ u)
    {N : ℕ} (hN : 2 ≤ N)
    (hshift : ∀ generator,
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 : ℝ) ∂μShift) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter
                (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
              zeroDiv (B u ^ 2)
                (auxiliarySubsetWeight ρ (samplingLambda ε) B u)) *
          wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator,
        wce generator ^ (2 * samplingLambda ε) ∂μGenerator) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter
              (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
            auxiliarySubsetWeight ρ (samplingLambda ε) B u ^
                samplingLambda ε * ρ ^ u.card) /
        ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm' (Function.uncurry error) 1 (μGenerator.prod μShift) ≤
      ((2 * ENNReal.ofReal
          (latticeUniformMomentConstant (diffusion := diffusion)
            bounds ρ (samplingLambda ε) transferConstant)) /
        (N : ℝ≥0∞)) ^ (1 - ε) := by
  have hlam := samplingLambda_mem_interval hεPos hεHalf
  have hmoment := uniform_fractional_moment_of_theorem4_1
    bounds hT x₀ herror herrorJoint hwceMeas hρ hlam.1 hlam.2
      htransferConstant B hBnonneg htransfer hshift hwce
  exact single_l1_rate_of_fractional_moment herrorJoint hεPos hεHalf hN hmoment

/-- Median part of Theorem 3.1 once the identical single-copy fractional-moment estimate has
been obtained.  The index type has cardinality `R = 2k - 1`, exactly as in the paper. -/
theorem theorem3_1_median_core
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {value : Fin (2 * k - 1) → Ω → ℝ} {median : Ω → ℝ}
    (hmedian : ∀ ω, IsOddMedian k (fun i ↦ value i ω) (median ω))
    (hmeas : ∀ i, Measurable (value i)) (hindep : iIndepFun value μ)
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    {q : ℝ} (hqOne : 1 ≤ q) (hk : 0 < k) (hqRange : q < k / (1 - ε))
    {C : ℝ≥0∞} {N : ℕ} (hN : 2 ≤ N)
    (hcopyMoment : ∀ i,
      (∫⁻ ω, ‖value i ω‖ₑ ^ (2 * samplingLambda ε) ∂μ) ≤
        C / ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm' median q μ ≤
      ((2 * k - 1).choose k : ℝ≥0∞) ^ (1 / q) *
        ((2 * C) / (N : ℝ≥0∞)) ^ (1 - ε) := by
  simpa using median_lq_rate_of_fractional_moment
    hmedian hmeas hindep hεPos hεHalf (lt_of_lt_of_le zero_lt_one hqOne)
      hk hqRange hN hcopyMoment

end

end TimeDependentLattice.Sampling
