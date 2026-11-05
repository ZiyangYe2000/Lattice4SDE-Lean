/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import TimeDependentLattice.Euler.Growth

/-!
# The hybrid exponential moment in Lemma 5.1

This file records the parameter choices and the deterministic-to-probabilistic part of paper
Lemma 5.1. `HybridMomentAssembly.lean` proves the exponential moment bound on the path
majorant and assembles Lemma 5.1 from the hybrid product distribution.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped ENNReal
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
open MeasureTheory ProbabilityTheory Set

/-- The common factor in the paper's choices of `α₀` and `λ₀`. -/
def hybridMomentScale (β T L Θ₁ : ℝ) : ℝ :=
  β * Real.exp (L * T) * √T * Θ₁ * (2 + 1 / √2)

/-- Equation (5.2): the parameter in the auxiliary weight `ψ(t) = exp (-α₀ |t|)`. -/
def hybridAlpha (β T L Θ₁ : ℝ) : ℝ :=
  1 + hybridMomentScale β T L Θ₁

/-- The exponent `λ₀` introduced in the proof of Lemma 5.1. -/
def hybridLambda (β T L Θ₁ : ℝ) : ℝ :=
  2 * hybridMomentScale β T L Θ₁

theorem hybridMomentScale_nonneg
    {β T L Θ₁ : ℝ} (hβ : 0 ≤ β) (hΘ₁ : 0 ≤ Θ₁) :
    0 ≤ hybridMomentScale β T L Θ₁ := by
  unfold hybridMomentScale
  have hsqrtTwo : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  positivity

theorem one_le_hybridAlpha
    {β T L Θ₁ : ℝ} (hβ : 0 ≤ β) (hΘ₁ : 0 ≤ Θ₁) :
    1 ≤ hybridAlpha β T L Θ₁ := by
  unfold hybridAlpha
  exact le_add_of_nonneg_right (hybridMomentScale_nonneg hβ hΘ₁)

theorem hybridAlpha_pos
    {β T L Θ₁ : ℝ} (hβ : 0 ≤ β) (hΘ₁ : 0 ≤ Θ₁) :
    0 < hybridAlpha β T L Θ₁ :=
  lt_of_lt_of_le zero_lt_one (one_le_hybridAlpha hβ hΘ₁)

theorem hybridLambda_lt_two_mul_hybridAlpha (β T L Θ₁ : ℝ) :
    hybridLambda β T L Θ₁ < 2 * hybridAlpha β T L Θ₁ := by
  unfold hybridLambda hybridAlpha
  linarith

/-- The choice (5.2) leaves the fixed margin `2α₀ - λ₀ = 2`; no continuity argument is
needed for the Laplace-coordinate moment. -/
theorem two_mul_hybridAlpha_sub_hybridLambda (β T L Θ₁ : ℝ) :
    2 * hybridAlpha β T L Θ₁ - hybridLambda β T L Θ₁ = 2 := by
  simp only [hybridAlpha, hybridLambda]
  ring

/-- The uniform one-coordinate exponential-moment majorant used in Lemma 5.1. -/
def hybridCoordinateMomentBound (α lam : ℝ) : ℝ :=
  max (2 * Real.exp (lam ^ 2 / 2)) (2 * α / (2 * α - lam))

theorem one_le_hybridCoordinateMomentBound (α lam : ℝ) :
    1 ≤ hybridCoordinateMomentBound α lam := by
  apply le_trans _ (le_max_left _ _)
  have hexp : 1 ≤ Real.exp (lam ^ 2 / 2) :=
    Real.one_le_exp (div_nonneg (sq_nonneg lam) (by norm_num))
  nlinarith

/-- At the paper's specialized parameter choice, the Laplace entry of the maximum is `α₀`. -/
theorem hybridCoordinateMomentBound_specialized (β T L Θ₁ : ℝ) :
    hybridCoordinateMomentBound (hybridAlpha β T L Θ₁) (hybridLambda β T L Θ₁) =
      max (2 * Real.exp ((hybridLambda β T L Θ₁) ^ 2 / 2))
        (hybridAlpha β T L Θ₁) := by
  unfold hybridCoordinateMomentBound
  rw [two_mul_hybridAlpha_sub_hybridLambda]
  ring_nf

/-- Equation (D.3), with exactly the explicit constant used in the paper. -/
def auxiliaryMomentConstant (β T K₀ L initialNorm Θ₁ : ℝ) : ℝ :=
  Real.exp (2 * β * Real.exp (L * T) * (initialNorm + K₀ * T)) *
    hybridCoordinateMomentBound (hybridAlpha β T L Θ₁) (hybridLambda β T L Θ₁) *
      (2 : ℝ) ^ ((4 + 3 * √2) / (4 + √2) : ℝ)

/-! ## The two one-dimensional coordinate laws -/

/-- Integrability of the two-sided exponential density. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi]
  have hleft : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [abs_of_nonpos hx]
    congr 1
    ring
  have hright : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_pos hx]
  exact hleft.union hright

/-- Elementary integral used to normalize the two-sided exponential law. -/
theorem integral_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-a * |x|) = 2 / a := by
  change (∫ x : ℝ, (fun y : ℝ => Real.exp (-a * y)) |x|) = _
  rw [integral_comp_abs (f := fun y : ℝ => Real.exp (-a * y))]
  rw [integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  norm_num
  field_simp

/-- `ℝ≥0∞` form of the preceding integral, used by product-moment estimates. -/
theorem lintegral_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-a * |x|)) ∂volume) =
      ENNReal.ofReal (2 / a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_abs ha)
    (ae_of_all _ fun x => (Real.exp_pos _).le)]
  rw [integral_exp_neg_mul_abs ha]

/-- For a standard Gaussian coordinate, splitting at zero and using the Gaussian mgf gives
the first entry of `K_{α₀}(λ₀)`. -/
theorem standardGaussian_abs_exp_lintegral_le (lam : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (lam * |x|)) ∂gaussianReal 0 1) ≤
      ENNReal.ofReal (2 * Real.exp (lam ^ 2 / 2)) := by
  have hplus :
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (lam * x)) ∂gaussianReal 0 1) =
        ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) lam)
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
    change ENNReal.ofReal (mgf id (gaussianReal 0 1) lam) = _
    rw [mgf_id_gaussianReal]
    norm_num
  have hminus :
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp ((-lam) * x)) ∂gaussianReal 0 1) =
        ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-lam))
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
    change ENNReal.ofReal (mgf id (gaussianReal 0 1) (-lam)) = _
    rw [mgf_id_gaussianReal]
    norm_num
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (lam * |x|)) ∂gaussianReal 0 1) ≤
        ∫⁻ x : ℝ, (ENNReal.ofReal (Real.exp (lam * x)) +
          ENNReal.ofReal (Real.exp ((-lam) * x))) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (Real.exp (lam * |x|)) ≤
        ENNReal.ofReal (Real.exp (lam * x)) + ENNReal.ofReal (Real.exp (-lam * x))
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge hx)]
        have heq : lam * -x = -lam * x := by ring
        rw [heq]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) +
        ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) := by
      rw [lintegral_add_left]
      · rw [hplus, hminus]
      · fun_prop
    _ = ENNReal.ofReal (2 * Real.exp (lam ^ 2 / 2)) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring

/-- The two-sided exponential probability measure with paper density
`α exp (-2 α |x|)`. -/
def laplaceCoordinateMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity
    (fun x => ENNReal.ofReal (α * Real.exp (-2 * α * |x|)))

/-- Exact exponential moment of a coordinate with density `α exp (-2 α |x|)`. -/
theorem laplaceCoordinate_abs_exp_lintegral
    {α lam : ℝ} (hα : 0 < α) (hlam : lam < 2 * α) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (lam * |x|))
        ∂laplaceCoordinateMeasure α) =
      ENNReal.ofReal (2 * α / (2 * α - lam)) := by
  unfold laplaceCoordinateMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) (by fun_prop)]
  have hdecay : 0 < 2 * α - lam := by linarith
  have hpoint : ∀ x : ℝ,
      ENNReal.ofReal (α * Real.exp (-2 * α * |x|)) *
          ENNReal.ofReal (Real.exp (lam * |x|)) =
        ENNReal.ofReal α *
          ENNReal.ofReal (Real.exp (-(2 * α - lam) * |x|)) := by
    intro x
    rw [ENNReal.ofReal_mul hα.le]
    rw [mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply congrArg ENNReal.ofReal
    rw [← Real.exp_add]
    ring_nf
  simp_rw [Pi.mul_apply, hpoint]
  rw [lintegral_const_mul (ENNReal.ofReal α) (by fun_prop)]
  rw [lintegral_exp_neg_mul_abs hdecay]
  rw [← ENNReal.ofReal_mul hα.le]
  congr 1
  field_simp

/-- The density used for coordinates in `u` is normalized. -/
theorem laplaceCoordinateMeasure_isProbability {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (laplaceCoordinateMeasure α) := by
  constructor
  have hmoment := laplaceCoordinate_abs_exp_lintegral hα (by linarith : 0 < 2 * α)
  have hfrac : 2 * α / (2 * α) = 1 := by
    field_simp
  simpa [hfrac] using hmoment

/-- Both one-dimensional laws in Lemma 5.1 obey the common maximum bound. -/
theorem standardGaussian_abs_exp_lintegral_le_coordinateBound (α lam : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (lam * |x|)) ∂gaussianReal 0 1) ≤
      ENNReal.ofReal (hybridCoordinateMomentBound α lam) := by
  exact (standardGaussian_abs_exp_lintegral_le lam).trans
    (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- The same common bound for a coordinate using the two-sided exponential density. -/
theorem laplaceCoordinate_abs_exp_lintegral_le_coordinateBound
    {α lam : ℝ} (hα : 0 < α) (hlam : lam < 2 * α) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (lam * |x|))
        ∂laplaceCoordinateMeasure α) ≤
      ENNReal.ofReal (hybridCoordinateMomentBound α lam) := by
  rw [laplaceCoordinate_abs_exp_lintegral hα hlam]
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-! ## The finite hybrid product distribution -/

/-- Coordinate law of `ζ^(u)`: two-sided exponential on `u`, standard Gaussian off `u`. -/
def hybridCoordinateMeasure {ι : Type*} [DecidableEq ι]
    (u : Finset ι) (α : ℝ) (j : ι) : Measure ℝ :=
  if j ∈ u then laplaceCoordinateMeasure α else gaussianReal 0 1

/-- The product law of the hybrid vector in paper Lemma 5.1. -/
def hybridProductMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Finset ι) (α : ℝ) : Measure (ι → ℝ) :=
  Measure.pi (hybridCoordinateMeasure u α)

/-- Each hybrid coordinate law is a probability measure. -/
theorem hybridCoordinateMeasure_isProbability
    {ι : Type*} [DecidableEq ι] (u : Finset ι) {α : ℝ} (hα : 0 < α) (j : ι) :
    IsProbabilityMeasure (hybridCoordinateMeasure u α j) := by
  unfold hybridCoordinateMeasure
  split
  · exact laplaceCoordinateMeasure_isProbability hα
  · infer_instance

/-- Consequently, the hybrid product law is a probability measure. -/
theorem hybridProductMeasure_isProbability
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Finset ι) {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (hybridProductMeasure u α) := by
  letI (j : ι) : IsProbabilityMeasure (hybridCoordinateMeasure u α j) :=
    hybridCoordinateMeasure_isProbability u hα j
  unfold hybridProductMeasure
  infer_instance

/-- The coordinate projections under the hybrid product law are mutually independent. -/
theorem hybridProductMeasure_iIndepFun
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Finset ι) {α : ℝ} (hα : 0 < α) :
    iIndepFun (fun j (z : ι → ℝ) => z j) (hybridProductMeasure u α) := by
  letI (j : ι) : IsProbabilityMeasure (hybridCoordinateMeasure u α j) :=
    hybridCoordinateMeasure_isProbability u hα j
  unfold hybridProductMeasure
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Every coordinate under the hybrid product law satisfies the common exponential-moment
bound `K_α(lam)`. -/
theorem hybridProductMeasure_coordinate_abs_exp_lintegral_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Finset ι) {α lam : ℝ} (hα : 0 < α) (hlam : lam < 2 * α) (j : ι) :
    (∫⁻ z : ι → ℝ, ENNReal.ofReal (Real.exp (lam * |z j|))
        ∂hybridProductMeasure u α) ≤
      ENNReal.ofReal (hybridCoordinateMomentBound α lam) := by
  letI (k : ι) : IsProbabilityMeasure (hybridCoordinateMeasure u α k) :=
    hybridCoordinateMeasure_isProbability u hα k
  have hpres : MeasurePreserving (Function.eval j)
      (hybridProductMeasure u α) (hybridCoordinateMeasure u α j) := by
    simpa [hybridProductMeasure] using
      (measurePreserving_eval (hybridCoordinateMeasure u α) j)
  have hcoordinate := hpres.lintegral_comp
    (f := fun x : ℝ => ENNReal.ofReal (Real.exp (lam * |x|))) (by fun_prop)
  rw [hcoordinate]
  unfold hybridCoordinateMeasure
  split
  · exact laplaceCoordinate_abs_exp_lintegral_le_coordinateBound hα hlam
  · exact standardGaussian_abs_exp_lintegral_le_coordinateBound α lam

/-! ## Maxima within one Brownian-bridge level and component -/

/-- Raw coordinate belonging to location `k`, level `level`, and component `r`. -/
def detailLevelCoordinate {J noiseDim : ℕ} (z : Index J noiseDim → ℝ)
    (level : Fin J) (r : Fin noiseDim) (k : Fin (2 ^ level.val)) : ℝ :=
  z (Sum.inr ⟨level, (k, r)⟩)

/-- Paper notation `M_{ℓ,r}` for a raw finite coordinate vector. -/
def detailLevelMaxAbs {J noiseDim : ℕ} (z : Index J noiseDim → ℝ)
    (level : Fin J) (r : Fin noiseDim) : ℝ :=
  let values := (Finset.univ : Finset (Fin (2 ^ level.val))).image
    (fun k => |detailLevelCoordinate z level r k|)
  values.max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The finite maximum `M_{ℓ,r}` is attained by one detail coordinate. -/
theorem exists_detailLevelCoordinate_eq_maxAbs
    {J noiseDim : ℕ} (z : Index J noiseDim → ℝ)
    (level : Fin J) (r : Fin noiseDim) :
    ∃ k : Fin (2 ^ level.val),
      detailLevelMaxAbs z level r = |detailLevelCoordinate z level r k| := by
  let values := (Finset.univ : Finset (Fin (2 ^ level.val))).image
    (fun k => |detailLevelCoordinate z level r k|)
  have hnonempty : values.Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  have hmem := Finset.max'_mem values hnonempty
  rcases Finset.mem_image.mp hmem with ⟨k, hk, heq⟩
  exact ⟨k, by simpa [detailLevelMaxAbs, values] using heq.symm⟩

/-- Every coordinate at a fixed level and component is bounded by the corresponding finite
maximum. -/
theorem abs_detailLevelCoordinate_le_maxAbs
    {J noiseDim : ℕ} (z : Index J noiseDim → ℝ)
    (level : Fin J) (r : Fin noiseDim) (k : Fin (2 ^ level.val)) :
    |detailLevelCoordinate z level r k| ≤ detailLevelMaxAbs z level r := by
  let values := (Finset.univ : Finset (Fin (2 ^ level.val))).image
    (fun q => |detailLevelCoordinate z level r q|)
  have hmem : |detailLevelCoordinate z level r k| ∈ values :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  exact Finset.le_max' values _ hmem

/-- Exponentiating a level maximum is bounded by the sum over all locations. -/
theorem exp_detailLevelMaxAbs_le_sum
    {J noiseDim : ℕ} (z : Index J noiseDim → ℝ)
    (level : Fin J) (r : Fin noiseDim) (lam : ℝ) :
    ENNReal.ofReal (Real.exp (lam * detailLevelMaxAbs z level r)) ≤
      ∑ k : Fin (2 ^ level.val),
        ENNReal.ofReal (Real.exp (lam * |detailLevelCoordinate z level r k|)) := by
  obtain ⟨k, hk⟩ := exists_detailLevelCoordinate_eq_maxAbs z level r
  rw [hk]
  refine Finset.single_le_sum
    (f := fun q : Fin (2 ^ level.val) =>
      ENNReal.ofReal (Real.exp (lam * |detailLevelCoordinate z level r q|))) ?_
    (Finset.mem_univ k)
  intro q hq
  exact bot_le

/-- The paper's estimate
`E exp (lam M_{ℓ,r}) ≤ 2^ℓ K_α(lam)` under the hybrid product law. -/
theorem hybridProductMeasure_detailLevelMaxAbs_lintegral_le
    {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    {α lam : ℝ} (hα : 0 < α) (hlam : lam < 2 * α)
    (level : Fin J) (r : Fin noiseDim) :
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp (lam * detailLevelMaxAbs z level r))
          ∂hybridProductMeasure u α) ≤
      ((2 ^ level.val : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (hybridCoordinateMomentBound α lam) := by
  calc
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp (lam * detailLevelMaxAbs z level r))
          ∂hybridProductMeasure u α) ≤
        ∫⁻ z : Index J noiseDim → ℝ,
          ∑ k : Fin (2 ^ level.val),
            ENNReal.ofReal
              (Real.exp (lam * |detailLevelCoordinate z level r k|))
            ∂hybridProductMeasure u α := by
      apply lintegral_mono
      exact fun z => exp_detailLevelMaxAbs_le_sum z level r lam
    _ = ∑ k : Fin (2 ^ level.val),
          ∫⁻ z : Index J noiseDim → ℝ,
            ENNReal.ofReal
              (Real.exp (lam * |detailLevelCoordinate z level r k|))
            ∂hybridProductMeasure u α := by
      rw [lintegral_finsetSum]
      intro k hk
      let j : Index J noiseDim := Sum.inr ⟨level, (k, r)⟩
      have hj : Measurable (fun z : Index J noiseDim → ℝ => z j) :=
        measurable_pi_apply j
      exact Measurable.ennreal_ofReal
        (Measurable.exp (Measurable.const_mul (Measurable.abs hj) lam))
    _ ≤ ∑ _k : Fin (2 ^ level.val),
          ENNReal.ofReal (hybridCoordinateMomentBound α lam) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hybridProductMeasure_coordinate_abs_exp_lintegral_le
        u hα hlam (Sum.inr ⟨level, (k, r)⟩)
    _ = ((2 ^ level.val : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (hybridCoordinateMomentBound α lam) := by
      simp

/-- Pointwise deterministic part of Lemma 5.1: an exponential state bound follows from
the Euler Gronwall estimate and any nonnegative path majorant `P`. -/
theorem exp_stateNat_norm_le_exp_pathMajorant
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) {T K₀ L P β : ℝ}
    (x₀ : State stateDim) (z : Input J noiseDim)
    (hT : 0 ≤ T) (hK₀ : 0 ≤ K₀) (hL : 0 ≤ L) (hP : 0 ≤ P) (hβ : 0 ≤ β)
    (hdrift : ∀ i < numSteps J,
      ‖drift (gridTime T J i) (stateNat drift diffusion T x₀ z i)‖ ≤
        K₀ + L * ‖stateNat drift diffusion T x₀ z i‖)
    (hpath : ∀ i ≤ numSteps J,
      ‖diffusedPath diffusion T z (gridTime T J i)‖ ≤ P)
    {i : ℕ} (hi : i ≤ numSteps J) :
    Real.exp (2 * β * ‖stateNat drift diffusion T x₀ z i‖) ≤
      Real.exp (2 * β * Real.exp (L * T) * (‖x₀‖ + K₀ * T)) *
        Real.exp (2 * β * Real.exp (L * T) * P) := by
  have hstate := stateNat_norm_le_exp_of_linearGrowth drift diffusion x₀ z
    hT hK₀ hL hP hdrift hpath hi
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hscale : 0 ≤ 2 * β := mul_nonneg (by norm_num) hβ
  calc
    2 * β * ‖stateNat drift diffusion T x₀ z i‖ ≤
        2 * β * ((‖x₀‖ + K₀ * T + P) * Real.exp (L * T)) :=
      mul_le_mul_of_nonneg_left hstate hscale
    _ = 2 * β * Real.exp (L * T) * (‖x₀‖ + K₀ * T) +
        2 * β * Real.exp (L * T) * P := by ring

/-- Probabilistic wrapper for the preceding deterministic estimate.  Once the hybrid
Brownian-bridge path majorant has the stated exponential moment, the same bound transfers to
the Euler state. -/
theorem exp_stateNat_norm_lintegral_le_of_pathMoment
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) {T K₀ L β pathMoment : ℝ}
    (x₀ : State stateDim) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → Input J noiseDim) (P : Ω → ℝ)
    (hT : 0 ≤ T) (hK₀ : 0 ≤ K₀) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hP : ∀ ω, 0 ≤ P ω)
    (hdrift : ∀ ω i, i < numSteps J →
      ‖drift (gridTime T J i) (stateNat drift diffusion T x₀ (Z ω) i)‖ ≤
        K₀ + L * ‖stateNat drift diffusion T x₀ (Z ω) i‖)
    (hpath : ∀ ω i, i ≤ numSteps J →
      ‖diffusedPath diffusion T (Z ω) (gridTime T J i)‖ ≤ P ω)
    (hpathMoment :
      (∫⁻ ω, ENNReal.ofReal
        (Real.exp (2 * β * Real.exp (L * T) * P ω)) ∂μ) ≤
          ENNReal.ofReal pathMoment)
    {i : ℕ} (hi : i ≤ numSteps J) :
    (∫⁻ ω, ENNReal.ofReal
      (Real.exp (2 * β * ‖stateNat drift diffusion T x₀ (Z ω) i‖)) ∂μ) ≤
        ENNReal.ofReal
          (Real.exp (2 * β * Real.exp (L * T) * (‖x₀‖ + K₀ * T))) *
            ENNReal.ofReal pathMoment := by
  let C : ℝ := Real.exp (2 * β * Real.exp (L * T) * (‖x₀‖ + K₀ * T))
  let f : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (2 * β * Real.exp (L * T) * P ω))
  calc
    (∫⁻ ω, ENNReal.ofReal
        (Real.exp (2 * β * ‖stateNat drift diffusion T x₀ (Z ω) i‖)) ∂μ) ≤
        ∫⁻ ω, ENNReal.ofReal C * f ω ∂μ := by
      apply lintegral_mono
      intro ω
      dsimp only [C, f]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal
        (exp_stateNat_norm_le_exp_pathMajorant drift diffusion x₀ (Z ω)
          hT hK₀ hL (hP ω) hβ (hdrift ω) (hpath ω) hi)
    _ = ENNReal.ofReal C * ∫⁻ ω, f ω ∂μ := by
      exact lintegral_const_mul' _ _ (by simp [C])
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal pathMoment := by
      exact mul_le_mul_right hpathMoment _

end

end TimeDependentLattice.Sampling
