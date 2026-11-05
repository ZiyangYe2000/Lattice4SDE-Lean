/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.EulerTransfer
import TimeDependentLattice.Sampling.Main
import TimeDependentLattice.Sampling.LatticeProbability

/-!
# Sampling theorem for the actual Euler integrand

This file inserts the now-proved Lemma 5.2 into the abstract sampling-error assembly.  As in
`Main.lean`, the random worst-case-error estimate quoted by the paper remains an explicit external
hypothesis.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- The exact transfer constant in the paper: `sqrt C_aux`. -/
def eulerTransferConstant
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim) : ℝ :=
  Real.sqrt
    (auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
      ‖x₀‖ (diffusionThetaOne diffusion))

/-- The value of `ρ_λ` used for the Euler integrand in paper Theorem 3.1.  Its
dependence on `Theta_1` is through the prescribed choice `α = α₀`. -/
def eulerSamplingRho
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (ε : ℝ) : ℝ :=
  samplingRho
    (hybridAlpha bounds.β T bounds.driftLipschitzConstant
      (diffusionThetaOne diffusion)) ε

theorem eulerSamplingRho_pos
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    0 < eulerSamplingRho diffusion bounds ε := by
  exact samplingRho_pos hεPos hεHalf

/-- Measurability of the Euler integrand when it is regarded as a function of raw Gaussian
coordinates. -/
theorem measurable_rawEulerIntegrand
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim) :
    Measurable (fun z : Index J noiseDim → ℝ ↦
      integrand drift diffusion payoff T x₀ (bridgeInput z)) := by
  exact (contDiff_eulerIntegrand (J := J) bounds x₀).continuous.measurable.comp
    (PiLp.continuous_toLp 2 _).measurable

/-- For each generating vector, the actual Euler lattice error is measurable in the shift. -/
theorem measurable_eulerLatticeError_shift
    {J stateDim noiseDim N : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (a : LatticeGenerator (Index J noiseDim) N) :
    Measurable (eulerLatticeError normalQuantile N drift diffusion payoff T x₀ a) := by
  exact (measurable_gaussianLatticeRule_shift hquantile N
    (measurable_rawEulerIntegrand bounds x₀) a).sub measurable_const

/-- The actual Euler lattice error is jointly measurable in the generating vector and shift. -/
theorem measurable_eulerLatticeError_joint
    {J stateDim noiseDim N : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (x₀ : State stateDim)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile) :
    Measurable (fun input :
        LatticeGenerator (Index J noiseDim) N × LatticeShift (Index J noiseDim) ↦
      eulerLatticeError normalQuantile N drift diffusion payoff T x₀ input.1 input.2) := by
  exact (measurable_gaussianLatticeRule_joint hquantile N
    (measurable_rawEulerIntegrand bounds x₀)).sub measurable_const

/-- Single-rule sampling part of Theorem 3.1 for the actual Euler integrand.  Lemma 5.2 and
Theorem 4.1 are no longer hypotheses; only the paper's cited random-wce input remains visible. -/
theorem theorem3_1_single_euler
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖)
    {Generator Shift : Type*}
    [MeasurableSpace Generator] [MeasurableSpace Shift]
    {μGenerator : Measure Generator} {μShift : Measure Shift}
    [IsProbabilityMeasure μGenerator] [IsProbabilityMeasure μShift]
    {error : Generator → Shift → ℝ} {wce : Generator → ℝ≥0∞}
    (herror : ∀ generator, Measurable (error generator))
    (herrorJoint : Measurable (Function.uncurry error))
    (hwceMeas : Measurable wce)
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 2 ≤ N)
    (hshift : ∀ generator,
      (∫⁻ shift, ‖error generator shift‖ₑ ^ (2 : ℝ) ∂μShift) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter
                (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
              zeroDiv
                (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x₀ u ^ 2)
                (auxiliarySubsetWeight ρ (samplingLambda ε)
                  (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x₀) u)) *
          wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator,
        wce generator ^ (2 * samplingLambda ε) ∂μGenerator) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter
              (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
            auxiliarySubsetWeight ρ (samplingLambda ε)
                (eulerGaussianSpaceComponent
                  drift diffusion payoff T bounds x₀) u ^
              samplingLambda ε * ρ ^ u.card) /
        ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm' (Function.uncurry error) 1 (μGenerator.prod μShift) ≤
      ((2 * ENNReal.ofReal
          (latticeUniformMomentConstant (diffusion := diffusion)
            bounds ρ (samplingLambda ε)
              (eulerTransferConstant diffusion bounds K₀ x₀))) /
        (N : ℝ≥0∞)) ^ (1 - ε) := by
  let B : Finset (Index J noiseDim) → ℝ :=
    eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀
  let C := eulerTransferConstant diffusion bounds K₀ x₀
  apply theorem3_1_single_core bounds hT x₀ herror herrorJoint hwceMeas
    hεPos hεHalf hρ (Real.sqrt_nonneg _) B
  · intro support
    exact eulerGaussianSpaceComponent_nonneg
      drift diffusion payoff T bounds x₀ support
  · intro support hsupport
    exact eulerGaussianSpaceComponent_le
      bounds hT hK₀ x₀ hdrift support hsupport
  · exact hN
  · simpa [B] using hshift
  · simpa [B] using hwce

/-- The fractional-moment estimate for the explicitly defined Euler lattice error.  This is the
single-copy estimate used by both parts of paper Theorem 3.1. -/
theorem euler_lattice_fractional_moment
    {J stateDim noiseDim N : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + bounds.driftLipschitzConstant *
          ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (hNprime : Nat.Prime N)
    {ρ lam : ℝ} (hρ : 0 < ρ) (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1)
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
                (auxiliarySubsetWeight ρ lam
                  (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x₀) u)) *
          wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator, wce generator ^ (2 * lam)
          ∂uniformGeneratorMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter
              (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
            auxiliarySubsetWeight ρ lam
                (eulerGaussianSpaceComponent
                  drift diffusion payoff T bounds x₀) u ^ lam * ρ ^ u.card) /
        ((N - 1 : ℕ) : ℝ≥0∞)) :
    (∫⁻ input : LatticeGenerator (Index J noiseDim) N ×
          LatticeShift (Index J noiseDim),
        ‖eulerLatticeError normalQuantile N drift diffusion payoff T x₀
            input.1 input.2‖ₑ ^ (2 * lam)
        ∂randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal
          (latticeUniformMomentConstant (diffusion := diffusion)
            bounds ρ lam (eulerTransferConstant diffusion bounds K₀ x₀)) /
        ((N - 1 : ℕ) : ℝ≥0∞) := by
  letI : Nonempty (LatticeGenerator (Index J noiseDim) N) :=
    latticeGenerator_nonempty hNprime.two_le
  let B : Finset (Index J noiseDim) → ℝ :=
    eulerGaussianSpaceComponent drift diffusion payoff T bounds x₀
  have h := uniform_fractional_moment_of_theorem4_1
    bounds hT x₀
    (μGenerator := uniformGeneratorMeasure (ι := Index J noiseDim) N)
    (μShift := uniformShiftMeasure (Index J noiseDim))
    (error := eulerLatticeError normalQuantile N drift diffusion payoff T x₀)
    (wce := wce)
    (measurable_eulerLatticeError_shift bounds x₀ hquantile)
    (measurable_eulerLatticeError_joint bounds x₀ hquantile)
    hwceMeas hρ hlamLower hlamUpper
    (Real.sqrt_nonneg _) B
    (fun support ↦ eulerGaussianSpaceComponent_nonneg
      drift diffusion payoff T bounds x₀ support)
    (fun support hsupport ↦ eulerGaussianSpaceComponent_le
      bounds hT hK₀ x₀ hdrift support hsupport)
    (denominator := ((N - 1 : ℕ) : ℝ≥0∞))
    (by simpa [B] using hshift) (by simpa [B] using hwce)
  simpa [randomizedLatticeMeasure, Function.uncurry_def,
    eulerTransferConstant] using h

/-- The single-rule part of paper Theorem 3.1 for the explicitly defined estimator
`Q_{A,Delta}^{N,m} - I_m`.  The two hypotheses involving `wce` are exactly the deterministic
shift-averaged worst-case-error bound and the cited random-wce moment estimate. -/
theorem theorem3_1_single_lattice
    {J stateDim noiseDim N : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K₀ : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK₀ : 0 ≤ K₀)
    (x₀ : State stateDim)
    (horigin : ∀ t, 0 ≤ t → t ≤ T → ‖drift t 0‖ ≤ K₀)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (hNprime : Nat.Prime N)
    {ε : ℝ} (hεPos : 0 < ε) (hεHalf : ε < 1 / 2)
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
        ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm'
        (fun input : LatticeGenerator (Index J noiseDim) N ×
            LatticeShift (Index J noiseDim) ↦
          eulerLatticeError normalQuantile N drift diffusion payoff T x₀
            input.1 input.2)
        1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
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
  have h := theorem3_1_single_euler bounds hT hK₀ x₀ hdrift
    (μGenerator := uniformGeneratorMeasure (ι := Index J noiseDim) N)
    (μShift := uniformShiftMeasure (Index J noiseDim))
    (error := eulerLatticeError normalQuantile N drift diffusion payoff T x₀)
    (wce := wce)
    (measurable_eulerLatticeError_shift bounds x₀ hquantile)
    (measurable_eulerLatticeError_joint bounds x₀ hquantile)
    hwceMeas hεPos hεHalf hρ hNprime.two_le hshift hwce
  simpa [randomizedLatticeMeasure, Function.uncurry_def] using h

end

end TimeDependentLattice.Sampling
