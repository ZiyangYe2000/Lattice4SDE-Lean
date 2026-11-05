/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.UniformOn
import TimeDependentLattice.Euler.State
import TimeDependentLattice.Sampling.PathMajorant

/-!
# Randomly shifted rank-one lattice estimators

This file records the estimator from paper Equation (2.24).  A coordinate of a generating vector
is represented by `Fin (N - 1)` and shifted by one, so its numerical value lies in
`{1, ..., N - 1}`.  The inverse standard-normal distribution function is kept as an explicit
function because Mathlib currently supplies the Gaussian measure but no standard-normal quantile
API.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler

/-- Generating vectors with coordinates in `{1, ..., N - 1}`.  The stored `Fin (N - 1)`
coordinate is converted to its paper value by adding one. -/
abbrev LatticeGenerator (ι : Type*) (N : ℕ) := ι → Fin (N - 1)

/-- The integer value in `{1, ..., N - 1}` represented by one stored generator coordinate. -/
def generatorValue {ι : Type*} {N : ℕ} (a : LatticeGenerator ι N) (j : ι) : ℕ :=
  (a j).val + 1

/-- Random shifts are real coordinate vectors.  Their probability law is specified separately. -/
abbrev LatticeShift (ι : Type*) := ι → ℝ

/-- The componentwise fractional-part lattice point
`{n a / N + Delta}` from paper Equation (2.23). -/
def latticePoint {ι : Type*} (N : ℕ) (a : LatticeGenerator ι N)
    (shift : LatticeShift ι) (n : Fin N) : ι → ℝ :=
  fun j ↦ Int.fract (((n.val : ℝ) * generatorValue a j) / N + shift j)

/-- For a fixed generating vector, every lattice point is measurable in the random shift. -/
theorem measurable_latticePoint_shift
    {ι : Type*} [Fintype ι] (N : ℕ) (a : LatticeGenerator ι N) (n : Fin N) :
    Measurable (fun shift : LatticeShift ι ↦ latticePoint N a shift n) := by
  apply Measurable.of_eval
  intro j
  exact (measurable_const.add (measurable_pi_apply j)).fract

/-- A lattice point is jointly measurable in its finite generating vector and its shift. -/
theorem measurable_latticePoint_joint
    {ι : Type*} [Fintype ι] (N : ℕ) (n : Fin N) :
    Measurable (fun input : LatticeGenerator ι N × LatticeShift ι ↦
      latticePoint N input.1 input.2 n) := by
  apply Measurable.of_eval
  intro j
  have hgenerator : Measurable (fun input : LatticeGenerator ι N × LatticeShift ι ↦
      (((n.val : ℝ) * generatorValue input.1 j) / N)) :=
    (measurable_of_finite fun a : LatticeGenerator ι N ↦
      (((n.val : ℝ) * generatorValue a j) / N)).comp measurable_fst
  have hshift : Measurable (fun input : LatticeGenerator ι N × LatticeShift ι ↦ input.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact (hgenerator.add hshift).fract

/-- A randomly shifted rank-one lattice rule applied to a cube integrand. -/
def rankOneLatticeRule {ι : Type*} [Fintype ι]
    (N : ℕ) (cubeIntegrand : (ι → ℝ) → ℝ)
    (a : LatticeGenerator ι N) (shift : LatticeShift ι) : ℝ :=
  (1 / (N : ℝ)) * ∑ n : Fin N, cubeIntegrand (latticePoint N a shift n)

/-- A lattice rule is measurable in its shift whenever the cube integrand is measurable. -/
theorem measurable_rankOneLatticeRule_shift
    {ι : Type*} [Fintype ι]
    (N : ℕ) {cubeIntegrand : (ι → ℝ) → ℝ} (hcube : Measurable cubeIntegrand)
    (a : LatticeGenerator ι N) :
    Measurable (fun shift ↦ rankOneLatticeRule N cubeIntegrand a shift) := by
  unfold rankOneLatticeRule
  exact measurable_const.mul
    (Finset.measurable_sum Finset.univ fun n _ ↦
      hcube.comp (measurable_latticePoint_shift N a n))

/-- A lattice rule is jointly measurable in the finite generating vector and random shift. -/
theorem measurable_rankOneLatticeRule_joint
    {ι : Type*} [Fintype ι]
    (N : ℕ) {cubeIntegrand : (ι → ℝ) → ℝ} (hcube : Measurable cubeIntegrand) :
    Measurable (fun input : LatticeGenerator ι N × LatticeShift ι ↦
      rankOneLatticeRule N cubeIntegrand input.1 input.2) := by
  unfold rankOneLatticeRule
  exact measurable_const.mul
    (Finset.measurable_sum Finset.univ fun n _ ↦
      hcube.comp (measurable_latticePoint_joint N n))

/-- The Gaussian lattice rule `Q_{a,Delta}(F)`: apply a chosen standard-normal quantile
coordinatewise to every lattice point before evaluating `F`. -/
def gaussianLatticeRule {ι : Type*} [Fintype ι]
    (normalQuantile : ℝ → ℝ) (N : ℕ) (F : (ι → ℝ) → ℝ)
    (a : LatticeGenerator ι N) (shift : LatticeShift ι) : ℝ :=
  rankOneLatticeRule N (fun u ↦ F (fun j ↦ normalQuantile (u j))) a shift

/-- A Gaussian lattice rule is measurable in the random shift. -/
theorem measurable_gaussianLatticeRule_shift
    {ι : Type*} [Fintype ι]
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (N : ℕ) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    (a : LatticeGenerator ι N) :
    Measurable (fun shift ↦ gaussianLatticeRule normalQuantile N F a shift) := by
  apply measurable_rankOneLatticeRule_shift
  exact hF.comp (Measurable.of_eval fun j ↦ hquantile.comp (measurable_pi_apply j))

/-- A Gaussian lattice rule is jointly measurable in its random generating vector and shift. -/
theorem measurable_gaussianLatticeRule_joint
    {ι : Type*} [Fintype ι]
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (N : ℕ) {F : (ι → ℝ) → ℝ} (hF : Measurable F) :
    Measurable (fun input : LatticeGenerator ι N × LatticeShift ι ↦
      gaussianLatticeRule normalQuantile N F input.1 input.2) := by
  apply measurable_rankOneLatticeRule_joint
  exact hF.comp (Measurable.of_eval fun j ↦ hquantile.comp (measurable_pi_apply j))

/-- The Euler lattice estimator `Q_{a,Delta}^{N,m}` from paper Equation (2.24), with
`m = 2^J`. -/
def eulerLatticeRule
    {J stateDim noiseDim : ℕ}
    (normalQuantile : ℝ → ℝ) (N : ℕ)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T : ℝ) (x₀ : State stateDim)
    (a : LatticeGenerator (Index J noiseDim) N)
    (shift : LatticeShift (Index J noiseDim)) : ℝ :=
  gaussianLatticeRule normalQuantile N
    (fun z ↦ integrand drift diffusion payoff T x₀ (bridgeInput z)) a shift

/-- The Euler Gaussian integral `I_m`, expressed using the product standard-Gaussian law of the
Brownian-bridge coordinates. -/
def eulerGaussianIntegral
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T : ℝ) (x₀ : State stateDim) : ℝ :=
  ∫ z : Index J noiseDim → ℝ,
    integrand drift diffusion payoff T x₀ (bridgeInput z)
      ∂Measure.pi (fun _ : Index J noiseDim ↦ gaussianReal 0 1)

/-- The paper's single-rule sampling error
`Q_{a,Delta}^{N,m} - I_m`. -/
def eulerLatticeError
    {J stateDim noiseDim : ℕ}
    (normalQuantile : ℝ → ℝ) (N : ℕ)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T : ℝ) (x₀ : State stateDim)
    (a : LatticeGenerator (Index J noiseDim) N)
    (shift : LatticeShift (Index J noiseDim)) : ℝ :=
  eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ a shift -
    eulerGaussianIntegral (J := J) drift diffusion payoff T x₀

@[simp]
theorem eulerLatticeError_apply
    {J stateDim noiseDim : ℕ}
    (normalQuantile : ℝ → ℝ) (N : ℕ)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T : ℝ) (x₀ : State stateDim)
    (a : LatticeGenerator (Index J noiseDim) N)
    (shift : LatticeShift (Index J noiseDim)) :
    eulerLatticeError normalQuantile N drift diffusion payoff T x₀ a shift =
      eulerLatticeRule normalQuantile N drift diffusion payoff T x₀ a shift -
        eulerGaussianIntegral (J := J) drift diffusion payoff T x₀ := rfl

end

end TimeDependentLattice.Sampling
