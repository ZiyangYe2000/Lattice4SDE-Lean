/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.HybridWeights

/-!
# Assembly of the hybrid Brownian-bridge moment

This file applies the finite weighted Hölder inequality to the endpoint coordinates and the
level/component detail groups from paper Lemma 5.1.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity

/-- The individual Hölder factor.  For details we use the sum of coordinate exponentials,
which measurably dominates the exponential of the level maximum. -/
def hybridHolderFactor {J noiseDim : ℕ} (lam : ℝ)
    (j : HybridHolderIndex J noiseDim) (z : Index J noiseDim → ℝ) : ℝ≥0∞ :=
  match j with
  | Sum.inl r => ENNReal.ofReal (Real.exp (lam * |z (Sum.inl r)|))
  | Sum.inr pair =>
      ∑ k : Fin (2 ^ pair.1.val),
        ENNReal.ofReal
          (Real.exp (lam * |detailLevelCoordinate z pair.1 pair.2 k|))

theorem measurable_hybridHolderFactor {J noiseDim : ℕ} (lam : ℝ)
    (j : HybridHolderIndex J noiseDim) :
    Measurable (hybridHolderFactor (J := J) (noiseDim := noiseDim) lam j) := by
  cases j with
  | inl r =>
      unfold hybridHolderFactor
      fun_prop
  | inr pair =>
      unfold hybridHolderFactor
      apply Finset.measurable_fun_sum
      intro k hk
      unfold detailLevelCoordinate
      fun_prop

/-- The factorwise moment bound: `K` for endpoints and `2^ℓ K` for detail groups. -/
def hybridHolderMomentBound {J noiseDim : ℕ} (K : ℝ≥0∞) :
    HybridHolderIndex J noiseDim → ℝ≥0∞
  | Sum.inl _ => K
  | Sum.inr pair => ((2 ^ pair.1.val : ℕ) : ℝ≥0∞) * K

theorem hybridHolderMomentBound_eq {J noiseDim : ℕ} (K : ℝ≥0∞)
    (j : HybridHolderIndex J noiseDim) :
    hybridHolderMomentBound K j =
      K * (2 : ℝ≥0∞) ^ hybridHolderLevel j := by
  cases j with
  | inl r => simp [hybridHolderMomentBound, hybridHolderLevel]
  | inr pair =>
      simp [hybridHolderMomentBound, hybridHolderLevel, ENNReal.rpow_natCast,
        mul_comm]

theorem hybridHolderFactor_lintegral_le
    {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    {α lam : ℝ} (hα : 0 < α) (hlam : lam < 2 * α)
    (j : HybridHolderIndex J noiseDim) :
    (∫⁻ z : Index J noiseDim → ℝ,
        hybridHolderFactor lam j z ∂hybridProductMeasure u α) ≤
      hybridHolderMomentBound
        (ENNReal.ofReal (hybridCoordinateMomentBound α lam)) j := by
  cases j with
  | inl r =>
      exact hybridProductMeasure_coordinate_abs_exp_lintegral_le
        u hα hlam (Sum.inl r)
  | inr pair =>
      rw [show hybridHolderFactor lam (Sum.inr pair) =
          fun z : Index J noiseDim → ℝ =>
            ∑ k : Fin (2 ^ pair.1.val),
              ENNReal.ofReal
                (Real.exp (lam * |detailLevelCoordinate z pair.1 pair.2 k|)) by rfl]
      rw [lintegral_finsetSum]
      · calc
          (∑ k : Fin (2 ^ pair.1.val),
              ∫⁻ z : Index J noiseDim → ℝ,
                ENNReal.ofReal
                  (Real.exp (lam * |detailLevelCoordinate z pair.1 pair.2 k|))
                ∂hybridProductMeasure u α) ≤
              ∑ _k : Fin (2 ^ pair.1.val),
                ENNReal.ofReal (hybridCoordinateMomentBound α lam) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hybridProductMeasure_coordinate_abs_exp_lintegral_le
              u hα hlam (Sum.inr ⟨pair.1, (k, pair.2)⟩)
          _ = hybridHolderMomentBound
                (ENNReal.ofReal (hybridCoordinateMomentBound α lam))
                (Sum.inr pair) := by simp [hybridHolderMomentBound]
      · intro k hk
        unfold detailLevelCoordinate
        fun_prop

/-- Each endpoint factor is exact, while each detail factor dominates the exponential of
`M_{ℓ,r}`. -/
theorem exp_hybridHolderObservable_le_factor
    {J noiseDim : ℕ} (lam : ℝ) (z : Index J noiseDim → ℝ)
    (j : HybridHolderIndex J noiseDim) :
    ENNReal.ofReal (Real.exp (lam * hybridHolderObservable z j)) ≤
      hybridHolderFactor lam j z := by
  cases j with
  | inl r => exact le_rfl
  | inr pair =>
      exact exp_detailLevelMaxAbs_le_sum z pair.1 pair.2 lam

/-- Pointwise domination of the exponential path factor by the weighted Hölder product. -/
theorem exp_weightedObservableSum_le_holderProduct
    {J noiseDim : ℕ} (sigma : Fin noiseDim → ℝ)
    (hsigma : ∀ r, 0 ≤ sigma r) (lam : ℝ) (z : Index J noiseDim → ℝ) :
    ENNReal.ofReal (Real.exp
        (lam * ∑ j : HybridHolderIndex J noiseDim,
          hybridHolderWeight sigma j * hybridHolderObservable z j)) ≤
      ∏ j : HybridHolderIndex J noiseDim,
        hybridHolderFactor lam j z ^ hybridHolderWeight sigma j := by
  apply ofReal_exp_weightedSum_le_prod Finset.univ
  · intro j hj
    exact hybridHolderWeight_nonneg hsigma j
  · intro j hj
    exact exp_hybridHolderObservable_le_factor lam z j

/-- Generalized Hölder plus the coordinate moment estimates.  The remaining right-hand side is
a finite deterministic product of the paper's moment bounds. -/
theorem hybridWeightedObservable_lintegral_le_momentProduct
    {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    {α lam : ℝ} (hα : 0 < α) (hlam : lam < 2 * α)
    (sigma : Fin noiseDim → ℝ) (hsigma : ∀ r, 0 ≤ sigma r)
    (htheta : 0 < ∑ r, sigma r) :
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (lam * ∑ j : HybridHolderIndex J noiseDim,
            hybridHolderWeight sigma j * hybridHolderObservable z j))
        ∂hybridProductMeasure u α) ≤
      ∏ j : HybridHolderIndex J noiseDim,
        hybridHolderMomentBound
            (ENNReal.ofReal (hybridCoordinateMomentBound α lam)) j ^
          hybridHolderWeight sigma j := by
  letI : IsProbabilityMeasure (hybridProductMeasure u α) :=
    hybridProductMeasure_isProbability u hα
  calc
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (lam * ∑ j : HybridHolderIndex J noiseDim,
            hybridHolderWeight sigma j * hybridHolderObservable z j))
        ∂hybridProductMeasure u α) ≤
        ∫⁻ z : Index J noiseDim → ℝ,
          ∏ j : HybridHolderIndex J noiseDim,
            hybridHolderFactor lam j z ^ hybridHolderWeight sigma j
          ∂hybridProductMeasure u α := by
      apply lintegral_mono
      intro z
      exact exp_weightedObservableSum_le_holderProduct sigma hsigma lam z
    _ ≤ _ := by
      apply lintegral_weightedProduct_le_of_momentBounds Finset.univ
      · intro j hj
        exact (measurable_hybridHolderFactor lam j).aemeasurable
      · intro j hj
        exact hybridHolderWeight_nonneg hsigma j
      · exact sum_hybridHolderWeight_le_one htheta
      · intro j hj
        exact hybridHolderFactor_lintegral_le u hα hlam j

/-- Evaluation of the deterministic moment product.  This is the exact source of the residual
power `2^((4+3√2)/(4+√2))` in the paper. -/
theorem hybridHolderMomentProduct_le
    {J noiseDim : ℕ} {α lam : ℝ} (sigma : Fin noiseDim → ℝ)
    (hsigma : ∀ r, 0 ≤ sigma r) (htheta : 0 < ∑ r, sigma r) :
    (∏ j : HybridHolderIndex J noiseDim,
        hybridHolderMomentBound
            (ENNReal.ofReal (hybridCoordinateMomentBound α lam)) j ^
          hybridHolderWeight sigma j) ≤
      ENNReal.ofReal (hybridCoordinateMomentBound α lam) *
        (2 : ℝ≥0∞) ^ ((4 + 3 * √2) / (4 + √2) : ℝ) := by
  let K : ℝ≥0∞ := ENNReal.ofReal (hybridCoordinateMomentBound α lam)
  have hKone : 1 ≤ K :=
    ENNReal.one_le_ofReal.mpr (one_le_hybridCoordinateMomentBound α lam)
  have hKzero : K ≠ 0 := ne_of_gt (zero_lt_one.trans_le hKone)
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have htwoZero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have htwoTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hweight : ∀ j ∈ (Finset.univ : Finset (HybridHolderIndex J noiseDim)),
      0 ≤ hybridHolderWeight sigma j := by
    intro j hj
    exact hybridHolderWeight_nonneg hsigma j
  calc
    (∏ j : HybridHolderIndex J noiseDim,
        hybridHolderMomentBound K j ^ hybridHolderWeight sigma j) =
        ∏ j : HybridHolderIndex J noiseDim,
          (K * (2 : ℝ≥0∞) ^ hybridHolderLevel j) ^
            hybridHolderWeight sigma j := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hybridHolderMomentBound_eq]
    _ = K ^ (∑ j : HybridHolderIndex J noiseDim,
            hybridHolderWeight sigma j) *
          (2 : ℝ≥0∞) ^
            (∑ j : HybridHolderIndex J noiseDim,
              hybridHolderLevel j * hybridHolderWeight sigma j) :=
      prod_mul_rpow_weight_eq Finset.univ K 2
        (hybridHolderWeight sigma) hybridHolderLevel hweight
        hKzero hKtop htwoZero htwoTop
    _ ≤ K ^ (1 : ℝ) *
          (2 : ℝ≥0∞) ^ ((4 + 3 * √2) / (4 + √2) : ℝ) := by
      apply mul_le_mul
      · exact ENNReal.rpow_le_rpow_of_exponent_le hKone
          (sum_hybridHolderWeight_le_one htheta)
      · exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          (sum_hybridHolderLevel_mul_weight_le htheta)
      · exact bot_le
      · exact bot_le
    _ = K * (2 : ℝ≥0∞) ^ ((4 + 3 * √2) / (4 + √2) : ℝ) := by simp

/-- The Brownian-path part of paper Lemma 5.1 for `Θ₁ > 0`, after the specialized choices
`α = α₀` and `λ = λ₀`. -/
theorem hybridPathMajorant_lintegral_le
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (u : Finset (Index J noiseDim)) {β T L : ℝ}
    (hβ : 0 ≤ β) (htheta : 0 < diffusionThetaOne diffusion) :
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (2 * β * Real.exp (L * T) * brownianPathMajorant diffusion T z))
        ∂hybridProductMeasure u
          (hybridAlpha β T L (diffusionThetaOne diffusion))) ≤
      ENNReal.ofReal
          (hybridCoordinateMomentBound
            (hybridAlpha β T L (diffusionThetaOne diffusion))
            (hybridLambda β T L (diffusionThetaOne diffusion))) *
        (2 : ℝ≥0∞) ^ ((4 + 3 * √2) / (4 + √2) : ℝ) := by
  let sigma := diffusionSigma diffusion
  let theta := diffusionThetaOne diffusion
  let α₀ := hybridAlpha β T L theta
  let lam₀ := hybridLambda β T L theta
  have hsigma : ∀ r, 0 ≤ sigma r := fun r => diffusionSigma_nonneg diffusion r
  have hthetaSum : 0 < ∑ r, sigma r := by
    simpa [sigma, theta, diffusionThetaOne] using htheta
  have hα₀ : 0 < α₀ := hybridAlpha_pos hβ htheta.le
  have hlam₀ : lam₀ < 2 * α₀ := hybridLambda_lt_two_mul_hybridAlpha β T L theta
  calc
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (2 * β * Real.exp (L * T) * brownianPathMajorant diffusion T z))
        ∂hybridProductMeasure u α₀) =
        ∫⁻ z : Index J noiseDim → ℝ,
          ENNReal.ofReal (Real.exp
            (lam₀ * ∑ j : HybridHolderIndex J noiseDim,
              hybridHolderWeight sigma j * hybridHolderObservable z j))
          ∂hybridProductMeasure u α₀ := by
      apply lintegral_congr
      intro z
      congr 2
      exact (hybridLambda_mul_weightedObservableSum_eq diffusion htheta β T L z).symm
    _ ≤ ∏ j : HybridHolderIndex J noiseDim,
          hybridHolderMomentBound
              (ENNReal.ofReal (hybridCoordinateMomentBound α₀ lam₀)) j ^
            hybridHolderWeight sigma j :=
      hybridWeightedObservable_lintegral_le_momentProduct
        u hα₀ hlam₀ sigma hsigma hthetaSum
    _ ≤ ENNReal.ofReal (hybridCoordinateMomentBound α₀ lam₀) *
          (2 : ℝ≥0∞) ^ ((4 + 3 * √2) / (4 + √2) : ℝ) :=
      hybridHolderMomentProduct_le sigma hsigma hthetaSum

/-- Paper Lemma 5.1 in the nondegenerate case `Θ₁ > 0`: the Euler terminal exponential
moment is bounded by the explicit constant `C_aux` from Equation (D.3). -/
theorem hybridEulerTerminalMoment_le_auxiliaryMomentConstant_of_theta_pos
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (u : Finset (Index J noiseDim)) {β T K₀ L : ℝ}
    (hT : 0 < T) (hK₀ : 0 ≤ K₀) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (htheta : 0 < diffusionThetaOne diffusion)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + L * ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖) :
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (2 * β * ‖stateNat drift diffusion T x₀ (bridgeInput z)
            (numSteps J)‖))
        ∂hybridProductMeasure u
          (hybridAlpha β T L (diffusionThetaOne diffusion))) ≤
      ENNReal.ofReal
        (auxiliaryMomentConstant β T K₀ L ‖x₀‖
          (diffusionThetaOne diffusion)) := by
  let theta := diffusionThetaOne diffusion
  let α₀ := hybridAlpha β T L theta
  let lam₀ := hybridLambda β T L theta
  let K := hybridCoordinateMomentBound α₀ lam₀
  let residual : ℝ := (4 + 3 * √2) / (4 + √2)
  let pathMoment : ℝ := K * (2 : ℝ) ^ residual
  have hK : 0 ≤ K := (one_le_hybridCoordinateMomentBound α₀ lam₀).trans' zero_le_one
  have hresidual : 0 ≤ residual := by
    dsimp [residual]
    positivity
  have hpow : 0 ≤ (2 : ℝ) ^ residual := Real.rpow_nonneg (by norm_num) _
  have hpathMomentNonneg : 0 ≤ pathMoment := mul_nonneg hK hpow
  have hpathMoment :
      (∫⁻ z : Index J noiseDim → ℝ,
          ENNReal.ofReal (Real.exp
            (2 * β * Real.exp (L * T) * brownianPathMajorant diffusion T z))
          ∂hybridProductMeasure u α₀) ≤ ENNReal.ofReal pathMoment := by
    have hmain := hybridPathMajorant_lintegral_le diffusion u
      (T := T) (L := L) hβ htheta
    change _ ≤ ENNReal.ofReal K *
      (2 : ℝ≥0∞) ^ residual at hmain
    calc
      (∫⁻ z : Index J noiseDim → ℝ,
          ENNReal.ofReal (Real.exp
            (2 * β * Real.exp (L * T) * brownianPathMajorant diffusion T z))
          ∂hybridProductMeasure u α₀) ≤
          ENNReal.ofReal K * (2 : ℝ≥0∞) ^ residual := hmain
      _ = ENNReal.ofReal pathMoment := by
        unfold pathMoment
        rw [ENNReal.ofReal_mul hK]
        congr 1
        simpa using
          (ENNReal.ofReal_rpow_of_nonneg (x := (2 : ℝ))
            (by norm_num) hresidual)
  have hstate := exp_stateNat_norm_lintegral_le_of_pathMoment
    drift diffusion x₀
    (μ := hybridProductMeasure u α₀)
    (Z := bridgeInput) (P := brownianPathMajorant diffusion T)
    hT.le hK₀ hL hβ
    (fun z => brownianPathMajorant_nonneg diffusion T z)
    hdrift
    (fun z i hi => norm_diffusedPath_grid_le_brownianPathMajorant
      diffusion hT z i hi)
    hpathMoment (i := numSteps J) (le_refl _)
  calc
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (2 * β * ‖stateNat drift diffusion T x₀ (bridgeInput z)
            (numSteps J)‖))
        ∂hybridProductMeasure u α₀) ≤
        ENNReal.ofReal
            (Real.exp (2 * β * Real.exp (L * T) * (‖x₀‖ + K₀ * T))) *
          ENNReal.ofReal pathMoment := hstate
    _ = ENNReal.ofReal (auxiliaryMomentConstant β T K₀ L ‖x₀‖ theta) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      unfold auxiliaryMomentConstant pathMoment K α₀ lam₀ residual
      ring

/-- The paper quantity `Θ₁` is nonnegative. -/
theorem diffusionThetaOne_nonneg {stateDim noiseDim : ℕ}
    (diffusion : Diffusion stateDim noiseDim) :
    0 ≤ diffusionThetaOne diffusion := by
  unfold diffusionThetaOne
  exact Finset.sum_nonneg (fun r _ => diffusionSigma_nonneg diffusion r)

/-- If `Θ₁ = 0`, every diffusion-column norm vanishes. -/
theorem diffusionSigma_eq_zero_of_thetaOne_eq_zero
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (htheta : diffusionThetaOne diffusion = 0) (r : Fin noiseDim) :
    diffusionSigma diffusion r = 0 := by
  have hall : (fun q : Fin noiseDim => diffusionSigma diffusion q) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun q : Fin noiseDim => diffusionSigma_nonneg diffusion q)).mp (by
        simpa [diffusionThetaOne] using htheta)
  exact congrFun hall r

/-- In the degenerate case `Θ₁ = 0`, the Brownian path majorant is identically zero. -/
theorem brownianPathMajorant_eq_zero_of_thetaOne_eq_zero
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (htheta : diffusionThetaOne diffusion = 0)
    (z : Index J noiseDim → ℝ) :
    brownianPathMajorant diffusion T z = 0 := by
  have hcolumn (r : Fin noiseDim) :
      Regularity.columnNorm diffusion r = 0 := by
    exact diffusionSigma_eq_zero_of_thetaOne_eq_zero diffusion htheta r
  unfold brownianPathMajorant endpointFactor detailHeightFactor
  simp [hcolumn]

/-- Paper Lemma 5.1 in the degenerate case `Θ₁ = 0`. -/
theorem hybridEulerTerminalMoment_le_auxiliaryMomentConstant_of_theta_zero
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (u : Finset (Index J noiseDim)) {β T K₀ L : ℝ}
    (hT : 0 < T) (hK₀ : 0 ≤ K₀) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (htheta : diffusionThetaOne diffusion = 0)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + L * ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖) :
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (2 * β * ‖stateNat drift diffusion T x₀ (bridgeInput z)
            (numSteps J)‖))
        ∂hybridProductMeasure u
          (hybridAlpha β T L (diffusionThetaOne diffusion))) ≤
      ENNReal.ofReal
        (auxiliaryMomentConstant β T K₀ L ‖x₀‖
          (diffusionThetaOne diffusion)) := by
  let α₀ := hybridAlpha β T L (diffusionThetaOne diffusion)
  let A := Real.exp (2 * β * Real.exp (L * T) * (‖x₀‖ + K₀ * T))
  let residual : ℝ := (4 + 3 * √2) / (4 + √2)
  have hthetaNonneg : 0 ≤ diffusionThetaOne diffusion :=
    diffusionThetaOne_nonneg diffusion
  have hα₀ : 0 < α₀ := hybridAlpha_pos hβ hthetaNonneg
  letI : IsProbabilityMeasure (hybridProductMeasure u α₀) :=
    hybridProductMeasure_isProbability u hα₀
  have hpoint (z : Index J noiseDim → ℝ) :
      Real.exp (2 * β * ‖stateNat drift diffusion T x₀ (bridgeInput z)
          (numSteps J)‖) ≤ A := by
    have hmain := exp_stateNat_norm_le_exp_pathMajorant
      drift diffusion x₀ (bridgeInput z) hT.le hK₀ hL
      (P := 0) (by norm_num) hβ (hdrift z)
      (fun i hi => by
        rw [← brownianPathMajorant_eq_zero_of_thetaOne_eq_zero
          diffusion T htheta z]
        exact norm_diffusedPath_grid_le_brownianPathMajorant
          diffusion hT z i hi)
      (i := numSteps J) (le_refl _)
    simpa [A] using hmain
  have hresidual : 0 ≤ residual := by
    dsimp [residual]
    positivity
  have hpowOne : 1 ≤ (2 : ℝ) ^ residual :=
    Real.one_le_rpow (by norm_num) hresidual
  have hKOne :
      1 ≤ hybridCoordinateMomentBound
        (hybridAlpha β T L (diffusionThetaOne diffusion))
        (hybridLambda β T L (diffusionThetaOne diffusion)) :=
    one_le_hybridCoordinateMomentBound _ _
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hA_le_aux :
      A ≤ auxiliaryMomentConstant β T K₀ L ‖x₀‖
        (diffusionThetaOne diffusion) := by
    unfold auxiliaryMomentConstant
    change A ≤ A *
      hybridCoordinateMomentBound
        (hybridAlpha β T L (diffusionThetaOne diffusion))
        (hybridLambda β T L (diffusionThetaOne diffusion)) *
      (2 : ℝ) ^ residual
    calc
      A = A * 1 * 1 := by ring
      _ ≤ A *
          hybridCoordinateMomentBound
            (hybridAlpha β T L (diffusionThetaOne diffusion))
            (hybridLambda β T L (diffusionThetaOne diffusion)) *
          (2 : ℝ) ^ residual := by gcongr
  calc
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (2 * β * ‖stateNat drift diffusion T x₀ (bridgeInput z)
            (numSteps J)‖))
        ∂hybridProductMeasure u α₀) ≤
        ∫⁻ _z : Index J noiseDim → ℝ, ENNReal.ofReal A
          ∂hybridProductMeasure u α₀ := by
      apply lintegral_mono
      intro z
      exact ENNReal.ofReal_le_ofReal (hpoint z)
    _ = ENNReal.ofReal A := by simp
    _ ≤ ENNReal.ofReal
        (auxiliaryMomentConstant β T K₀ L ‖x₀‖
          (diffusionThetaOne diffusion)) :=
      ENNReal.ofReal_le_ofReal hA_le_aux

/-- Paper Lemma 5.1, including both the nondegenerate and degenerate diffusion cases. -/
theorem hybridEulerTerminalMoment_le_auxiliaryMomentConstant
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (u : Finset (Index J noiseDim)) {β T K₀ L : ℝ}
    (hT : 0 < T) (hK₀ : 0 ≤ K₀) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hdrift : ∀ z : Index J noiseDim → ℝ, ∀ i < numSteps J,
      ‖drift (gridTime T J i)
          (stateNat drift diffusion T x₀ (bridgeInput z) i)‖ ≤
        K₀ + L * ‖stateNat drift diffusion T x₀ (bridgeInput z) i‖) :
    (∫⁻ z : Index J noiseDim → ℝ,
        ENNReal.ofReal (Real.exp
          (2 * β * ‖stateNat drift diffusion T x₀ (bridgeInput z)
            (numSteps J)‖))
        ∂hybridProductMeasure u
          (hybridAlpha β T L (diffusionThetaOne diffusion))) ≤
      ENNReal.ofReal
        (auxiliaryMomentConstant β T K₀ L ‖x₀‖
          (diffusionThetaOne diffusion)) := by
  rcases (diffusionThetaOne_nonneg diffusion).eq_or_lt with htheta | htheta
  · exact hybridEulerTerminalMoment_le_auxiliaryMomentConstant_of_theta_zero
      drift diffusion x₀ u hT hK₀ hL hβ htheta.symm hdrift
  · exact hybridEulerTerminalMoment_le_auxiliaryMomentConstant_of_theta_pos
      drift diffusion x₀ u hT hK₀ hL hβ htheta hdrift

end

end TimeDependentLattice.Sampling
