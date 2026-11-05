/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.FiniteDimension
import TimeDependentLattice.Sampling.EulerMedian
import TimeDependentLattice.Regularity.PaperSummability

/-!
# Dimension-uniform sampling constants

This file formalizes paper Corollary 3.4.  It first connects the `NNReal` column sums used in
Assumption 2.3 with the real-valued sums used by the regularity and sampling estimates.  The
remaining definitions replace the actual column sum by an upper bound, so the final sampling
constant no longer contains either finite dimension.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- The two representations of the paper's diffusion-column sum agree after coercion to `ℝ`. -/
theorem coe_columnSum_eq_columnRhoSum
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (p : ℝ) :
    (TimeDependentLattice.columnSum diffusion p : ℝ) =
      Regularity.columnRhoSum diffusion p := by
  simp only [TimeDependentLattice.columnSum, Regularity.columnRhoSum,
    TimeDependentLattice.columnNorm, Regularity.columnNorm, NNReal.coe_sum,
    NNReal.coe_rpow, coe_nnnorm]

/-- The `Theta_1` used in Lemma 5.1 is the real coercion of the column sum from Assumption 2.3. -/
theorem diffusionThetaOne_eq_coe_columnSum
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) :
    diffusionThetaOne diffusion =
      (TimeDependentLattice.columnSum diffusion 1 : ℝ) := by
  simp only [diffusionThetaOne, diffusionSigma, Regularity.columnNorm,
    TimeDependentLattice.columnSum, TimeDependentLattice.columnNorm,
    NNReal.coe_sum, NNReal.coe_rpow, Real.rpow_one, coe_nnnorm]

/-- Assumption 2.3 implies the paper's bound `Theta_1 <= M_(2/3)^(3/2)`. -/
theorem diffusionThetaOne_le_of_twoThirds_le
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) {M : NNReal}
    (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M) :
    diffusionThetaOne diffusion ≤ (M : ℝ) ^ (3 / 2 : ℝ) := by
  rw [diffusionThetaOne_eq_coe_columnSum]
  have h := TimeDependentLattice.columnSum_le_of_twoThirds_le
    diffusion hM (v := (1 : ℝ)) (by norm_num)
  exact_mod_cast h

/-- The same uniform assumption controls every intermediate exponent used in Theorem 4.1. -/
theorem columnRhoSum_le_of_twoThirds_le
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) {M : NNReal}
    {p : ℝ} (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
    (hp : 2 / 3 ≤ p) :
    Regularity.columnRhoSum diffusion p ≤ (M : ℝ) ^ (3 * p / 2) := by
  rw [← coe_columnSum_eq_columnRhoSum]
  have h := TimeDependentLattice.columnSum_le_of_twoThirds_le diffusion hM hp
  exact_mod_cast h

/-! ## Scalar versions of the tree-summability constants -/

/-- The endpoint-series base with the column sum exposed as a scalar argument. -/
def endpointSeriesBaseAt (T A p theta : ℝ) : ℝ :=
  1 + A * (√T) ^ p * theta

/-- The endpoint-series constant with the column sum exposed as a scalar argument. -/
def endpointSeriesConstantAt (T A p tau theta : ℝ) : ℝ :=
  factorialDecaySeries (endpointSeriesBaseAt T A p theta) (tau * p)

/-- The detail-series base with the column sum exposed as a scalar argument. -/
def detailSeriesBaseAt (T A p theta : ℝ) : ℝ :=
  1 + 2 * A * detailSummabilityConstant T p * theta

/-- The detail-series constant with the column sum exposed as a scalar argument. -/
def detailSeriesConstantAt (T A p tau theta : ℝ) : ℝ :=
  factorialDecaySeries (detailSeriesBaseAt T A p theta) (tau * p)

/-- The all-subset constant from Lemma 4.5, now depending only on a scalar column-sum bound. -/
def allSubsetSeriesConstantAt (T A p tau theta : ℝ) : ℝ :=
  let A' := (2 : ℝ) ^ (tau * p) * A
  endpointSeriesConstantAt T A' p tau theta *
      detailSeriesConstantAt T A' p tau theta +
    T ^ p * endpointSeriesConstantAt T A' p tau theta

/-- The common tree-subset constant with the column sum exposed as a scalar argument. -/
def treeSubsetConstantAt (T A p tau theta : ℝ) : ℝ :=
  max 1 (paperTimeFactorConstant T A p tau theta)

/-- On the paper's parameter range this is exactly its chosen `C_H`. -/
theorem treeSubsetConstantAt_eq_paperTimeFactorConstant {T A p tau theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hp : 2 / 3 < p) (htheta : 0 ≤ theta)
    (htaup : tau * p < 1) :
    treeSubsetConstantAt T A p tau theta = paperTimeFactorConstant T A p tau theta := by
  exact max_eq_right (one_le_paperTimeFactorConstant hT hA htheta hp htaup)

@[simp] theorem endpointSeriesBase_eq_at
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A p : ℝ) :
    endpointSeriesBase diffusion T A p =
      endpointSeriesBaseAt T A p (columnRhoSum diffusion p) := rfl

@[simp] theorem endpointSeriesConstant_eq_at
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A p tau : ℝ) :
    endpointSeriesConstant diffusion T A p tau =
      endpointSeriesConstantAt T A p tau (columnRhoSum diffusion p) := rfl

@[simp] theorem detailSeriesBase_eq_at
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A p : ℝ) :
    detailSeriesBase diffusion T A p =
      detailSeriesBaseAt T A p (columnRhoSum diffusion p) := rfl

@[simp] theorem detailSeriesConstant_eq_at
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A p tau : ℝ) :
    detailSeriesConstant diffusion T A p tau =
      detailSeriesConstantAt T A p tau (columnRhoSum diffusion p) := rfl

@[simp] theorem allSubsetSeriesConstant_eq_at
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A p tau : ℝ) :
    allSubsetSeriesConstant diffusion T A p tau =
      allSubsetSeriesConstantAt T A p tau (columnRhoSum diffusion p) := rfl

@[simp] theorem treeSubsetConstant_eq_at
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A p tau : ℝ) :
    treeSubsetConstant diffusion T A p tau =
      treeSubsetConstantAt T A p tau (columnRhoSum diffusion p) := rfl

/-- Monotonicity of the convergent factorial-decay series in its positive geometric base. -/
theorem factorialDecaySeries_mono {A B q : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hq : q < 1) :
    factorialDecaySeries A q ≤ factorialDecaySeries B q := by
  unfold factorialDecaySeries
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hA.le hAB n)
      (Real.rpow_nonneg (by positivity) _)
  · exact summable_factorialDecaySeries hA hq
  · exact summable_factorialDecaySeries (hA.trans_le hAB) hq

theorem endpointSeriesBaseAt_pos {T A p theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (htheta : 0 ≤ theta) :
    0 < endpointSeriesBaseAt T A p theta := by
  unfold endpointSeriesBaseAt
  have : 0 ≤ A * (√T) ^ p * theta := by positivity
  linarith

theorem detailSeriesBaseAt_pos {T A p theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hp : 2 / 3 < p) (htheta : 0 ≤ theta) :
    0 < detailSeriesBaseAt T A p theta := by
  unfold detailSeriesBaseAt
  have hC := detailSummabilityConstant_nonneg hT hp
  have : 0 ≤ 2 * A * detailSummabilityConstant T p * theta := by positivity
  linarith

theorem endpointSeriesConstantAt_nonneg {T A p tau theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (htheta : 0 ≤ theta) :
    0 ≤ endpointSeriesConstantAt T A p tau theta := by
  unfold endpointSeriesConstantAt factorialDecaySeries
  exact tsum_nonneg fun n => mul_nonneg
    (pow_nonneg (endpointSeriesBaseAt_pos hT hA htheta).le n)
    (Real.rpow_nonneg (by positivity) _)

theorem detailSeriesConstantAt_nonneg {T A p tau theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hp : 2 / 3 < p) (htheta : 0 ≤ theta) :
    0 ≤ detailSeriesConstantAt T A p tau theta := by
  unfold detailSeriesConstantAt factorialDecaySeries
  exact tsum_nonneg fun n => mul_nonneg
    (pow_nonneg (detailSeriesBaseAt_pos hT hA hp htheta).le n)
    (Real.rpow_nonneg (by positivity) _)

theorem endpointSeriesConstantAt_mono {T A p tau theta theta' : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ theta') (htaup : tau * p < 1) :
    endpointSeriesConstantAt T A p tau theta ≤
      endpointSeriesConstantAt T A p tau theta' := by
  apply factorialDecaySeries_mono (endpointSeriesBaseAt_pos hT hA htheta) _ htaup
  unfold endpointSeriesBaseAt
  gcongr

theorem detailSeriesConstantAt_mono {T A p tau theta theta' : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hp : 2 / 3 < p) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ theta') (htaup : tau * p < 1) :
    detailSeriesConstantAt T A p tau theta ≤
      detailSeriesConstantAt T A p tau theta' := by
  apply factorialDecaySeries_mono (detailSeriesBaseAt_pos hT hA hp htheta) _ htaup
  unfold detailSeriesBaseAt
  have hC := detailSummabilityConstant_nonneg hT hp
  gcongr

theorem allSubsetSeriesConstantAt_mono {T A p tau theta theta' : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hp : 2 / 3 < p) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ theta') (htaup : tau * p < 1) :
    allSubsetSeriesConstantAt T A p tau theta ≤
      allSubsetSeriesConstantAt T A p tau theta' := by
  let A' := (2 : ℝ) ^ (tau * p) * A
  have hA' : 0 ≤ A' := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hA
  have hE := endpointSeriesConstantAt_mono hT hA' htheta htheta' htaup
  have hD := detailSeriesConstantAt_mono hT hA' hp htheta htheta' htaup
  have hE0 := endpointSeriesConstantAt_nonneg
    (p := p) (tau := tau) hT hA' htheta
  have hD0 := detailSeriesConstantAt_nonneg
    (tau := tau) hT hA' hp htheta
  change
    endpointSeriesConstantAt T A' p tau theta *
          detailSeriesConstantAt T A' p tau theta +
        T ^ p * endpointSeriesConstantAt T A' p tau theta ≤
      endpointSeriesConstantAt T A' p tau theta' *
          detailSeriesConstantAt T A' p tau theta' +
        T ^ p * endpointSeriesConstantAt T A' p tau theta'
  exact add_le_add (mul_le_mul hE hD hD0
    (hE0.trans hE)) (mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hT p))

theorem treeSubsetConstantAt_mono {T A p tau theta theta' : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hp : 2 / 3 < p) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ theta') (htaup : tau * p < 1) :
    treeSubsetConstantAt T A p tau theta ≤
      treeSubsetConstantAt T A p tau theta' := by
  unfold treeSubsetConstantAt
  exact max_le_max le_rfl
    (paperTimeFactorConstant_mono hT hA le_rfl htheta htheta' hp htaup)

theorem endpointSeriesConstantAt_mono_base {T A A' p tau theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hAA' : A ≤ A') (htheta : 0 ≤ theta)
    (htaup : tau * p < 1) :
    endpointSeriesConstantAt T A p tau theta ≤
      endpointSeriesConstantAt T A' p tau theta := by
  apply factorialDecaySeries_mono (endpointSeriesBaseAt_pos hT hA htheta) _ htaup
  unfold endpointSeriesBaseAt
  gcongr

theorem detailSeriesConstantAt_mono_base {T A A' p tau theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hAA' : A ≤ A')
    (hp : 2 / 3 < p) (htheta : 0 ≤ theta) (htaup : tau * p < 1) :
    detailSeriesConstantAt T A p tau theta ≤
      detailSeriesConstantAt T A' p tau theta := by
  apply factorialDecaySeries_mono (detailSeriesBaseAt_pos hT hA hp htheta) _ htaup
  unfold detailSeriesBaseAt
  have hC := detailSummabilityConstant_nonneg hT hp
  gcongr

theorem allSubsetSeriesConstantAt_mono_base {T A A' p tau theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hAA' : A ≤ A')
    (hp : 2 / 3 < p) (htheta : 0 ≤ theta) (htaup : tau * p < 1) :
    allSubsetSeriesConstantAt T A p tau theta ≤
      allSubsetSeriesConstantAt T A' p tau theta := by
  let B := (2 : ℝ) ^ (tau * p) * A
  let B' := (2 : ℝ) ^ (tau * p) * A'
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hA
  have hBB' : B ≤ B' := by
    dsimp [B, B']
    gcongr
  have hE := endpointSeriesConstantAt_mono_base hT hB hBB' htheta htaup
  have hD := detailSeriesConstantAt_mono_base hT hB hBB' hp htheta htaup
  have hE0 := endpointSeriesConstantAt_nonneg
    (p := p) (tau := tau) hT hB htheta
  have hD0 := detailSeriesConstantAt_nonneg
    (tau := tau) hT hB hp htheta
  change
    endpointSeriesConstantAt T B p tau theta *
          detailSeriesConstantAt T B p tau theta +
        T ^ p * endpointSeriesConstantAt T B p tau theta ≤
      endpointSeriesConstantAt T B' p tau theta *
          detailSeriesConstantAt T B' p tau theta +
        T ^ p * endpointSeriesConstantAt T B' p tau theta
  exact add_le_add (mul_le_mul hE hD hD0 (hE0.trans hE))
    (mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hT p))

theorem treeSubsetConstantAt_mono_base {T A A' p tau theta : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hAA' : A ≤ A')
    (hp : 2 / 3 < p) (htheta : 0 ≤ theta) (htaup : tau * p < 1) :
    treeSubsetConstantAt T A p tau theta ≤
      treeSubsetConstantAt T A' p tau theta := by
  unfold treeSubsetConstantAt
  exact max_le_max le_rfl
    (paperTimeFactorConstant_mono hT hA hAA' htheta le_rfl hp htaup)

theorem treeSubsetConstantAt_pos (T A p tau theta : ℝ) :
    0 < treeSubsetConstantAt T A p tau theta := by
  exact zero_lt_one.trans_le (le_max_left 1 _)

/-- A scalar-column-sum version of the Theorem 4.1 constant. -/
def derivativeSummabilityConstantAt
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (weightBase lam theta : ℝ) : ℝ :=
  let p := latticeDerivativeExponent lam
  let kappa := latticeSubsetBase weightBase lam
  let pIntermediate := intermediateExponent bounds.τ p
  let kappaIntermediate := kappa ^ (pIntermediate / p)
  let A := kappaIntermediate * bounds.majorantConstant ^ pIntermediate
  let H := treeSubsetConstantAt T A pIntermediate bounds.τ theta
  derivativeRhoConstant H bounds.majorantConstant bounds.τ pIntermediate ^
    (p / pIntermediate)

@[simp] theorem derivativeSummabilityConstant_eq_at
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (weightBase lam : ℝ) :
    derivativeSummabilityConstant (diffusion := diffusion) bounds weightBase lam =
      derivativeSummabilityConstantAt bounds weightBase lam
        (columnRhoSum diffusion
          (intermediateExponent bounds.τ (latticeDerivativeExponent lam))) := rfl

theorem factorialDecaySeries_nonneg {A : ℝ} (hA : 0 ≤ A) (q : ℝ) :
    0 ≤ factorialDecaySeries A q := by
  unfold factorialDecaySeries
  exact tsum_nonneg fun n => mul_nonneg (pow_nonneg (by positivity) n)
    (Real.rpow_nonneg (by positivity) _)

/-- The zeroth term of the convergent factorial series is one. -/
theorem one_le_factorialDecaySeries {A q : ℝ} (hA : 0 < A) (hq : q < 1) :
    1 ≤ factorialDecaySeries A q := by
  simpa [factorialDecaySeries] using
    (summable_factorialDecaySeries hA hq).sum_le_tsum ({0} : Finset ℕ)
      (fun n _ ↦ by positivity)

theorem derivativeRhoConstant_pos {H Cmaj tau p : ℝ}
    (hH : 0 < H) (hCmaj : 0 < Cmaj) (htaup : tau * p < 1) :
    0 < derivativeRhoConstant H Cmaj tau p := by
  apply mul_pos hH
  exact zero_lt_one.trans_le (one_le_factorialDecaySeries
    (mul_pos (Real.rpow_pos_of_pos hCmaj p) hH) htaup)

/-- The `rho`-summability constant is nondecreasing in the tree-subset bound. -/
theorem derivativeRhoConstant_mono {H H' Cmaj tau p : ℝ}
    (hH : 0 < H) (hHH' : H ≤ H') (hCmaj : 0 < Cmaj) (htaup : tau * p < 1) :
    derivativeRhoConstant H Cmaj tau p ≤
      derivativeRhoConstant H' Cmaj tau p := by
  have hbase : 0 < Cmaj ^ p * H :=
    mul_pos (Real.rpow_pos_of_pos hCmaj p) hH
  have hbaseLe : Cmaj ^ p * H ≤ Cmaj ^ p * H' := by
    gcongr
  have hseries := factorialDecaySeries_mono hbase hbaseLe htaup
  unfold derivativeRhoConstant
  exact mul_le_mul hHH' hseries
    (factorialDecaySeries_nonneg hbase.le (tau * p))
    (hH.trans_le hHH').le

/-- The constant `C_D(kappa,p;Theta_(2/3))` in paper Theorem 4.1. -/
def paperDerivativeConstant
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (κ p thetaTwoThirds : ℝ) : ℝ :=
  let ρ := intermediateExponent bounds.τ p
  let κρ := κ ^ (ρ / p)
  let A := κρ * bounds.majorantConstant ^ ρ
  let thetaρ := thetaTwoThirds ^ (3 * ρ / 2)
  let H := treeSubsetConstantAt T A ρ bounds.τ thetaρ
  derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ ^ (p / ρ)

/-- The exact Theorem 4.1 constant is strictly positive, including zero diffusion. -/
theorem paperDerivativeConstant_pos
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) {κ p theta : ℝ} (hp : 2 / 3 < p) :
    0 < paperDerivativeConstant bounds κ p theta := by
  let ρ := intermediateExponent bounds.τ p
  have hspec := intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp
  have htau : 0 < bounds.τ := zero_lt_one.trans_le bounds.τ_mem.1
  have htauρ : bounds.τ * ρ < 1 := by
    have h := hspec.2.2.1
    rw [lt_div_iff₀ htau] at h
    simpa [ρ, mul_comm] using h
  unfold paperDerivativeConstant
  dsimp only
  exact Real.rpow_pos_of_pos
    (derivativeRhoConstant_pos (treeSubsetConstantAt_pos _ _ _ _ _)
      (zero_lt_one.trans_le bounds.one_le_majorantConstant) htauρ) _

/-- On the paper's parameter domain the named derivative constant uses its original
`C_H` series, with no enlargement from the totalizing `max 1`. -/
theorem paperDerivativeConstant_eq_paper_formula
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) {κ p theta : ℝ}
    (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hp : 2 / 3 < p) (htheta : 0 ≤ theta) :
    paperDerivativeConstant bounds κ p theta =
      let ρ := intermediateExponent bounds.τ p
      let A := κ ^ (ρ / p) * bounds.majorantConstant ^ ρ
      let H := paperTimeFactorConstant T A ρ bounds.τ (theta ^ (3 * ρ / 2))
      derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ ^ (p / ρ) := by
  let ρ := intermediateExponent bounds.τ p
  let A := κ ^ (ρ / p) * bounds.majorantConstant ^ ρ
  have hspec := intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp
  have hρ : 2 / 3 < ρ := hspec.1
  have htau : 0 < bounds.τ := zero_lt_one.trans_le bounds.τ_mem.1
  have htauρ : bounds.τ * ρ < 1 := by
    have h := hspec.2.2.1
    rw [lt_div_iff₀ htau] at h
    simpa [ρ, mul_comm] using h
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg hκ _)
    (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
  change derivativeRhoConstant
      (treeSubsetConstantAt T A ρ bounds.τ (theta ^ (3 * ρ / 2)))
      bounds.majorantConstant bounds.τ ρ ^ (p / ρ) = _
  rw [treeSubsetConstantAt_eq_paperTimeFactorConstant hT hA hρ
    (Real.rpow_nonneg htheta _) htauρ]

/-- Strict positivity of the scalar-column version of the sampling derivative constant. -/
theorem derivativeSummabilityConstantAt_pos
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) {weightBase lam theta : ℝ}
    (hlamLower : 1 / 2 < lam) :
    0 < derivativeSummabilityConstantAt bounds weightBase lam theta := by
  let p := latticeDerivativeExponent lam
  have hp : 2 / 3 < p := by
    dsimp [p, latticeDerivativeExponent]
    apply (lt_div_iff₀ (by linarith : 0 < 1 + lam)).2
    nlinarith
  have hspec := intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp
  have htau : 0 < bounds.τ := zero_lt_one.trans_le bounds.τ_mem.1
  have htauρ : bounds.τ * intermediateExponent bounds.τ p < 1 := by
    have h := hspec.2.2.1
    rw [lt_div_iff₀ htau] at h
    simpa [mul_comm] using h
  unfold derivativeSummabilityConstantAt
  dsimp only
  exact Real.rpow_pos_of_pos
    (derivativeRhoConstant_pos (treeSubsetConstantAt_pos _ _ _ _ _)
      (zero_lt_one.trans_le bounds.one_le_majorantConstant) htauρ) _

/-- Strict positivity of the actual sampling derivative constant. -/
theorem derivativeSummabilityConstant_pos
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) {weightBase lam : ℝ}
    (hlamLower : 1 / 2 < lam) :
    0 < derivativeSummabilityConstant (diffusion := diffusion) bounds weightBase lam := by
  rw [derivativeSummabilityConstant_eq_at]
  exact derivativeSummabilityConstantAt_pos bounds hlamLower

/-- A positive transfer constant gives a strictly positive lattice moment constant. -/
theorem latticeUniformMomentConstant_pos
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) {weightBase lam transferConstant : ℝ}
    (hlamLower : 1 / 2 < lam) (htransferConstant : 0 < transferConstant) :
    0 < latticeUniformMomentConstant (diffusion := diffusion)
      bounds weightBase lam transferConstant := by
  exact Real.rpow_pos_of_pos
    (mul_pos (Real.rpow_pos_of_pos htransferConstant _)
      (derivativeSummabilityConstant_pos bounds hlamLower)) _

/-- The explicit Theorem 4.1 constant is simultaneously nondecreasing in `kappa` and
`Theta_(2/3)`. -/
theorem paperDerivativeConstant_mono
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T)
    {κ κ' p theta theta' : ℝ} (hT : 0 ≤ T) (hκ : 0 < κ) (hκκ' : κ ≤ κ')
    (hp : 2 / 3 < p) (htheta : 0 ≤ theta) (hthetaTheta : theta ≤ theta') :
    paperDerivativeConstant bounds κ p theta ≤
      paperDerivativeConstant bounds κ' p theta' := by
  let ρ := intermediateExponent bounds.τ p
  let A := κ ^ (ρ / p) * bounds.majorantConstant ^ ρ
  let A' := κ' ^ (ρ / p) * bounds.majorantConstant ^ ρ
  let thetaρ := theta ^ (3 * ρ / 2)
  let thetaρ' := theta' ^ (3 * ρ / 2)
  let H := treeSubsetConstantAt T A ρ bounds.τ thetaρ
  let H' := treeSubsetConstantAt T A' ρ bounds.τ thetaρ'
  have hspec := intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp
  have hρcritical : 2 / 3 < ρ := by simpa [ρ] using hspec.1
  have hρp : ρ < p := by simpa [ρ] using hspec.2.1
  have hρ0 : 0 < ρ := by simpa [ρ] using hspec.2.2.2
  have hp0 : 0 < p := hρ0.trans hρp
  have htauρ : bounds.τ * ρ < 1 := by
    have htauPos : 0 < bounds.τ := zero_lt_one.trans_le bounds.τ_mem.1
    have h := hspec.2.2.1
    rw [lt_div_iff₀ htauPos] at h
    simpa [mul_comm, ρ] using h
  have hκ' : 0 < κ' := hκ.trans_le hκκ'
  have hExponent : 0 ≤ ρ / p := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg hκ.le _)
      (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
  have hAA' : A ≤ A' := by
    dsimp [A, A']
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hκ.le hκκ' hExponent)
      (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) ρ)
  have hthetaρ : 0 ≤ thetaρ := by
    dsimp [thetaρ]
    positivity
  have hthetaρLe : thetaρ ≤ thetaρ' := by
    dsimp [thetaρ, thetaρ']
    exact Real.rpow_le_rpow htheta hthetaTheta (by positivity)
  have hHH' : H ≤ H' := by
    exact (treeSubsetConstantAt_mono_base hT hA hAA' hρcritical
      hthetaρ htauρ).trans
        (treeSubsetConstantAt_mono hT (hA.trans hAA') hρcritical
          hthetaρ hthetaρLe htauρ)
  have hH : 0 < H := treeSubsetConstantAt_pos _ _ _ _ _
  have hRho := derivativeRhoConstant_mono hH hHH'
    (zero_lt_one.trans_le bounds.one_le_majorantConstant) htauρ
  have hOuter : 0 ≤ p / ρ := by positivity
  unfold paperDerivativeConstant
  dsimp only
  exact Real.rpow_le_rpow
    (mul_nonneg hH.le
      (factorialDecaySeries_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
          hH.le)
        (bounds.τ * ρ))) hRho hOuter

/-- Paper Theorem 4.1 with the constant named as
`C_D(kappa,p;Theta_(2/3))`. -/
theorem theorem4_1_with_paper_constant
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {κ p : ℝ} (hκ : 0 < κ) (hp : 2 / 3 < p)
    {M : NNReal} (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M) :
    weightedDerivativeSum κ p
        (normalizedDerivativeEnvelope (J := J)
          drift diffusion payoff T bounds.β x₀) ≤
      paperDerivativeConstant bounds κ p M := by
  let ρ := intermediateExponent bounds.τ p
  let A := κ ^ (ρ / p) * bounds.majorantConstant ^ ρ
  let thetaActual := columnRhoSum diffusion ρ
  let thetaBound := (M : ℝ) ^ (3 * ρ / 2)
  let H := treeSubsetConstantAt T A ρ bounds.τ thetaActual
  let H' := treeSubsetConstantAt T A ρ bounds.τ thetaBound
  have hspec := intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp
  have hρcritical : 2 / 3 < ρ := by simpa [ρ] using hspec.1
  have hρp : ρ < p := by simpa [ρ] using hspec.2.1
  have hρ0 : 0 < ρ := by simpa [ρ] using hspec.2.2.2
  have hp0 : 0 < p := hρ0.trans hρp
  have htauρ : bounds.τ * ρ < 1 := by
    have htauPos : 0 < bounds.τ := zero_lt_one.trans_le bounds.τ_mem.1
    have h := hspec.2.2.1
    rw [lt_div_iff₀ htauPos] at h
    simpa [mul_comm, ρ] using h
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg hκ.le _)
      (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
  have hthetaActual : 0 ≤ thetaActual := columnRhoSum_nonneg diffusion ρ
  have htheta : thetaActual ≤ thetaBound := by
    dsimp [thetaActual, thetaBound]
    exact columnRhoSum_le_of_twoThirds_le diffusion hM hρcritical.le
  have hHH' : H ≤ H' :=
    treeSubsetConstantAt_mono hT.le hA hρcritical hthetaActual htheta htauρ
  have hH : 0 < H := treeSubsetConstantAt_pos _ _ _ _ _
  have hRho := derivativeRhoConstant_mono hH hHH'
    (zero_lt_one.trans_le bounds.one_le_majorantConstant) htauρ
  have hOuter : 0 ≤ p / ρ := by positivity
  have hmain := theorem4_1 (diffusion := diffusion) bounds hT x₀ hκ hp J
  have hbound :
      derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ ^ (p / ρ) ≤
        derivativeRhoConstant H' bounds.majorantConstant bounds.τ ρ ^ (p / ρ) :=
    Real.rpow_le_rpow
      (mul_nonneg hH.le
        (factorialDecaySeries_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
            hH.le)
          (bounds.τ * ρ))) hRho hOuter
  exact hmain.trans (by
    simpa [paperDerivativeConstant, ρ, A, thetaActual, thetaBound, H, H'] using hbound)

/-- Theorem 4.1 in the paper's existence form, with one strictly positive constant for
every Brownian-bridge level `J`. Its chosen witness is the named paper constant. -/
theorem theorem4_1_exists_pos_uniform
    {stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {κ p : ℝ} (hκ : 0 < κ) (hp : 2 / 3 < p)
    {M : NNReal} (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℕ,
      weightedDerivativeSum κ p
        (normalizedDerivativeEnvelope (J := J)
          drift diffusion payoff T bounds.β x₀) ≤ C := by
  refine ⟨paperDerivativeConstant bounds κ p M, paperDerivativeConstant_pos bounds hp, ?_⟩
  intro J
  exact theorem4_1_with_paper_constant bounds hT x₀ hκ hp hM

/-- The explicit Theorem 4.1 constant is nondecreasing in the scalar column-sum bound. -/
theorem derivativeSummabilityConstantAt_mono
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T)
    {weightBase lam theta theta' : ℝ}
    (hT : 0 ≤ T) (hweightBase : 0 < weightBase)
    (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1)
    (htheta : 0 ≤ theta) (htheta' : theta ≤ theta') :
    derivativeSummabilityConstantAt bounds weightBase lam theta ≤
      derivativeSummabilityConstantAt bounds weightBase lam theta' := by
  let p := latticeDerivativeExponent lam
  let kappa := latticeSubsetBase weightBase lam
  let pIntermediate := intermediateExponent bounds.τ p
  let kappaIntermediate := kappa ^ (pIntermediate / p)
  let A := kappaIntermediate * bounds.majorantConstant ^ pIntermediate
  let H := treeSubsetConstantAt T A pIntermediate bounds.τ theta
  let H' := treeSubsetConstantAt T A pIntermediate bounds.τ theta'
  have hp : 2 / 3 < p := by
    dsimp [p, latticeDerivativeExponent]
    apply (lt_div_iff₀ (by linarith : 0 < 1 + lam)).2
    nlinarith
  have hspec := intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp
  have hpIntermediate : 2 / 3 < pIntermediate := by
    simpa [pIntermediate] using hspec.1
  have htauIntermediate : bounds.τ * pIntermediate < 1 := by
    have htauPos : 0 < bounds.τ := zero_lt_one.trans_le bounds.τ_mem.1
    have h := hspec.2.2.1
    rw [lt_div_iff₀ htauPos] at h
    simpa [mul_comm, pIntermediate] using h
  have hkappa : 0 < kappa := by
    exact Real.rpow_pos_of_pos hweightBase _
  have hA : 0 ≤ A := by
    dsimp [A, kappaIntermediate]
    exact mul_nonneg (Real.rpow_nonneg hkappa.le _)
      (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
  have hH : 0 < H := by
    exact treeSubsetConstantAt_pos _ _ _ _ _
  have hHH' : H ≤ H' := by
    exact treeSubsetConstantAt_mono hT hA hpIntermediate htheta htheta'
      htauIntermediate
  have hRho := derivativeRhoConstant_mono hH hHH'
    (zero_lt_one.trans_le bounds.one_le_majorantConstant) htauIntermediate
  have hexponent : 0 ≤ p / pIntermediate := by positivity
  unfold derivativeSummabilityConstantAt
  dsimp only
  exact Real.rpow_le_rpow
    (mul_nonneg hH.le
      (factorialDecaySeries_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
          hH.le)
        (bounds.τ * pIntermediate))) hRho hexponent

/-- Assumption 2.3 replaces the dimension-specific derivative constant by one evaluated at
the common bound `M_(2/3)^(3 pIntermediate / 2)`. -/
theorem derivativeSummabilityConstant_le_of_twoThirds_le
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    {weightBase lam : ℝ} (hweightBase : 0 < weightBase)
    (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1)
    {M : NNReal} (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M) :
    derivativeSummabilityConstant (diffusion := diffusion) bounds weightBase lam ≤
      derivativeSummabilityConstantAt bounds weightBase lam
        ((M : ℝ) ^
          (3 * intermediateExponent bounds.τ (latticeDerivativeExponent lam) / 2)) := by
  rw [derivativeSummabilityConstant_eq_at]
  have hp : 2 / 3 < latticeDerivativeExponent lam := by
    unfold latticeDerivativeExponent
    apply (lt_div_iff₀ (by linarith : 0 < 1 + lam)).2
    nlinarith
  have hIntermediate :=
    (intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp).1.le
  exact derivativeSummabilityConstantAt_mono bounds hT.le hweightBase
    hlamLower hlamUpper (columnRhoSum_nonneg diffusion _) <|
      columnRhoSum_le_of_twoThirds_le diffusion hM hIntermediate

/-! ## Monotonicity of the Lemma 5.1 transfer constant -/

theorem hybridMomentScale_mono_theta {beta T L theta theta' : ℝ}
    (hbeta : 0 ≤ beta) (hT : 0 ≤ T) (htheta : theta ≤ theta') :
    hybridMomentScale beta T L theta ≤ hybridMomentScale beta T L theta' := by
  unfold hybridMomentScale
  have hsqrt : 0 ≤ √T := Real.sqrt_nonneg T
  have hfactor : 0 ≤ 2 + 1 / √2 := by positivity
  gcongr

theorem hybridAlpha_mono_theta {beta T L theta theta' : ℝ}
    (hbeta : 0 ≤ beta) (hT : 0 ≤ T) (htheta : theta ≤ theta') :
    hybridAlpha beta T L theta ≤ hybridAlpha beta T L theta' := by
  unfold hybridAlpha
  linarith [hybridMomentScale_mono_theta (L := L) hbeta hT htheta]

theorem hybridLambda_mono_theta {beta T L theta theta' : ℝ}
    (hbeta : 0 ≤ beta) (hT : 0 ≤ T) (htheta : theta ≤ theta') :
    hybridLambda beta T L theta ≤ hybridLambda beta T L theta' := by
  unfold hybridLambda
  gcongr
  exact hybridMomentScale_mono_theta hbeta hT htheta

/-- At the specialized choice (5.2), the one-coordinate moment bound is nondecreasing in
`Theta_1`. -/
theorem hybridCoordinateMomentBound_specialized_mono
    {beta T L theta theta' : ℝ}
    (hbeta : 0 ≤ beta) (hT : 0 ≤ T) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ theta') :
    hybridCoordinateMomentBound (hybridAlpha beta T L theta)
        (hybridLambda beta T L theta) ≤
      hybridCoordinateMomentBound (hybridAlpha beta T L theta')
        (hybridLambda beta T L theta') := by
  rw [hybridCoordinateMomentBound_specialized,
    hybridCoordinateMomentBound_specialized]
  have hlambda0 : 0 ≤ hybridLambda beta T L theta := by
    unfold hybridLambda
    exact mul_nonneg (by norm_num) (hybridMomentScale_nonneg hbeta htheta)
  have htheta'0 : 0 ≤ theta' := htheta.trans htheta'
  have hlambda0' : 0 ≤ hybridLambda beta T L theta' := by
    unfold hybridLambda
    exact mul_nonneg (by norm_num) (hybridMomentScale_nonneg hbeta htheta'0)
  have hlambda := hybridLambda_mono_theta (L := L) hbeta hT htheta'
  apply max_le_max
  · gcongr
  · exact hybridAlpha_mono_theta hbeta hT htheta'

theorem auxiliaryMomentConstant_pos (beta T K0 L initialNorm theta : ℝ) :
    0 < auxiliaryMomentConstant beta T K0 L initialNorm theta := by
  unfold auxiliaryMomentConstant
  exact mul_pos
    (mul_pos (Real.exp_pos _)
      (lt_of_lt_of_le zero_lt_one
        (one_le_hybridCoordinateMomentBound
          (hybridAlpha beta T L theta) (hybridLambda beta T L theta))))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The explicit constant in Lemma 5.1 is nondecreasing separately in the initial norm and
`Theta_1`. -/
theorem auxiliaryMomentConstant_mono
    {beta T K0 L initialNorm initialNorm' theta theta' : ℝ}
    (hbeta : 0 ≤ beta) (hT : 0 ≤ T)
    (hinitial : initialNorm ≤ initialNorm')
    (htheta : 0 ≤ theta) (htheta' : theta ≤ theta') :
    auxiliaryMomentConstant beta T K0 L initialNorm theta ≤
      auxiliaryMomentConstant beta T K0 L initialNorm' theta' := by
  have hexp :
      Real.exp (2 * beta * Real.exp (L * T) * (initialNorm + K0 * T)) ≤
        Real.exp (2 * beta * Real.exp (L * T) * (initialNorm' + K0 * T)) := by
    apply Real.exp_le_exp.mpr
    gcongr
  have hcoordinate := hybridCoordinateMomentBound_specialized_mono
    (L := L) hbeta hT htheta htheta'
  unfold auxiliaryMomentConstant
  have hcoordinate0 : 0 ≤
      hybridCoordinateMomentBound (hybridAlpha beta T L theta)
        (hybridLambda beta T L theta) :=
    zero_le_one.trans (one_le_hybridCoordinateMomentBound _ _)
  have hexp0 : 0 ≤ Real.exp
      (2 * beta * Real.exp (L * T) * (initialNorm + K0 * T)) :=
    (Real.exp_pos _).le
  have hlast : 0 ≤ (2 : ℝ) ^ ((4 + 3 * √2) / (4 + √2) : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hexp hcoordinate hcoordinate0
      ((Real.exp_pos _).le.trans hexp)) hlast

/-- Consequently, the square-root transfer constant from Lemma 5.2 has the same
monotonicities. -/
theorem eulerTransferConstant_le
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T K0 : ℝ}
    (bounds : GevreyBounds drift payoff T) (x0 : State stateDim)
    {initialBound thetaBound : ℝ}
    (hT : 0 ≤ T) (hinitial : ‖x0‖ ≤ initialBound)
    (htheta : diffusionThetaOne diffusion ≤ thetaBound) :
    eulerTransferConstant diffusion bounds K0 x0 ≤
      Real.sqrt (auxiliaryMomentConstant bounds.β T K0
        bounds.driftLipschitzConstant initialBound thetaBound) := by
  unfold eulerTransferConstant
  apply Real.sqrt_le_sqrt
  exact auxiliaryMomentConstant_mono bounds.β_pos.le hT hinitial
    (diffusionThetaOne_nonneg diffusion) htheta

/-- The dimension-uniform upper choice of `ρ_λ`, obtained by replacing `Theta_1`
with `M_(2/3)^(3/2)`. -/
def dimensionUniformSamplingRho
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (M : NNReal) (ε : ℝ) : ℝ :=
  samplingRho
    (hybridAlpha bounds.β T bounds.driftLipschitzConstant
      ((M : ℝ) ^ (3 / 2 : ℝ))) ε

theorem eulerSamplingRho_le_dimensionUniform
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    {M : NNReal} (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
    (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    eulerSamplingRho diffusion bounds ε ≤
      dimensionUniformSamplingRho bounds M ε := by
  have htheta := diffusionThetaOne_le_of_twoThirds_le diffusion hM
  have halpha := hybridAlpha_mono_theta
    (L := bounds.driftLipschitzConstant) bounds.β_pos.le hT.le htheta
  unfold eulerSamplingRho dimensionUniformSamplingRho
  exact samplingRho_mono_alpha hεPos hεHalf
    (zero_le_one.trans (one_le_hybridAlpha bounds.β_pos.le
      (diffusionThetaOne_nonneg diffusion))) halpha

theorem dimensionUniformSamplingRho_pos
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (M : NNReal)
    (hεPos : 0 < ε) (hεHalf : ε < 1 / 2) :
    0 < dimensionUniformSamplingRho bounds M ε :=
  samplingRho_pos hεPos hεHalf

/-! ## The named dimension-uniform lattice constant -/

/-- The paper's `C_lat` evaluated at the common bounds `R_0` and `M_(2/3)`.

The first occurrence of `M` controls `Theta_1`; the second controls the intermediate
`Theta_p` used inside Theorem 4.1.  Thus this definition contains no state or noise dimension. -/
def dimensionUniformLatticeMomentConstant
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K0 R0 : ℝ) (M : NNReal)
    (weightBase lam : ℝ) : ℝ :=
  let p := latticeDerivativeExponent lam
  let pIntermediate := intermediateExponent bounds.τ p
  let transfer := Real.sqrt
    (auxiliaryMomentConstant bounds.β T K0 bounds.driftLipschitzConstant
      R0 ((M : ℝ) ^ (3 / 2 : ℝ)))
  let derivative := derivativeSummabilityConstantAt bounds weightBase lam
    ((M : ℝ) ^ (3 * pIntermediate / 2))
  (transfer ^ p * derivative) ^ (1 + lam)

/-- The named dimension-uniform lattice constant is strictly positive. -/
theorem dimensionUniformLatticeMomentConstant_pos
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K0 R0 : ℝ) (M : NNReal)
    {weightBase lam : ℝ} (hlamLower : 1 / 2 < lam) :
    0 < dimensionUniformLatticeMomentConstant bounds K0 R0 M weightBase lam := by
  apply Real.rpow_pos_of_pos
  apply mul_pos
  · exact Real.rpow_pos_of_pos
      (Real.sqrt_pos.2 (auxiliaryMomentConstant_pos _ _ _ _ _ _)) _
  · exact derivativeSummabilityConstantAt_pos bounds hlamLower

theorem dimensionUniformLatticeMomentConstant_mono_weightBase
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T K0 R0 : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 ≤ T) (M : NNReal)
    {weightBase weightBase' lam : ℝ}
    (hweight : 0 < weightBase) (hweightLe : weightBase ≤ weightBase')
    (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1) :
    dimensionUniformLatticeMomentConstant bounds K0 R0 M weightBase lam ≤
      dimensionUniformLatticeMomentConstant bounds K0 R0 M weightBase' lam := by
  let p := latticeDerivativeExponent lam
  let ρ := intermediateExponent bounds.τ p
  let transfer := Real.sqrt
    (auxiliaryMomentConstant bounds.β T K0 bounds.driftLipschitzConstant
      R0 ((M : ℝ) ^ (3 / 2 : ℝ)))
  have hp : 2 / 3 < p := by
    dsimp [p, latticeDerivativeExponent]
    apply (lt_div_iff₀ (by linarith : 0 < 1 + lam)).2
    nlinarith
  have hsubset : latticeSubsetBase weightBase lam ≤
      latticeSubsetBase weightBase' lam := by
    unfold latticeSubsetBase
    exact Real.rpow_le_rpow hweight.le hweightLe (by positivity)
  have hsubsetPos : 0 < latticeSubsetBase weightBase lam :=
    Real.rpow_pos_of_pos hweight _
  have hderivative :
      derivativeSummabilityConstantAt bounds weightBase lam
          ((M : ℝ) ^ (3 * ρ / 2)) ≤
        derivativeSummabilityConstantAt bounds weightBase' lam
          ((M : ℝ) ^ (3 * ρ / 2)) := by
    change paperDerivativeConstant bounds (latticeSubsetBase weightBase lam) p M ≤
      paperDerivativeConstant bounds (latticeSubsetBase weightBase' lam) p M
    exact paperDerivativeConstant_mono bounds hT hsubsetPos hsubset hp
      (by positivity) le_rfl
  have htransfer : 0 ≤ transfer ^ p := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hderivative0 : 0 ≤
      derivativeSummabilityConstantAt bounds weightBase lam
        ((M : ℝ) ^ (3 * ρ / 2)) := by
    change 0 ≤ paperDerivativeConstant bounds (latticeSubsetBase weightBase lam) p M
    unfold paperDerivativeConstant
    dsimp only
    apply Real.rpow_nonneg
    apply mul_nonneg
    · exact (treeSubsetConstantAt_pos _ _ _ _ _).le
    · apply factorialDecaySeries_nonneg
      exact mul_nonneg
        (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
        (treeSubsetConstantAt_pos _ _ _ _ _).le
  unfold dimensionUniformLatticeMomentConstant
  dsimp only
  exact Real.rpow_le_rpow (mul_nonneg htransfer hderivative0)
    (mul_le_mul_of_nonneg_left hderivative htransfer) (by linarith)

/-- The actual moment constant in Theorem 3.1 is bounded by the named common constant from
Corollary 3.4. -/
theorem latticeUniformMomentConstant_le_dimensionUniform
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    {diffusion : Diffusion stateDim noiseDim} {payoff : Payoff stateDim} {T K0 R0 : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (x0 : State stateDim)
    {M : NNReal} (hinitial : ‖x0‖ ≤ R0)
    (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
    {weightBase lam : ℝ} (hweightBase : 0 < weightBase)
    (hlamLower : 1 / 2 < lam) (hlamUpper : lam < 1) :
    latticeUniformMomentConstant (diffusion := diffusion) bounds weightBase lam
        (eulerTransferConstant diffusion bounds K0 x0) ≤
      dimensionUniformLatticeMomentConstant bounds K0 R0 M weightBase lam := by
  let p := latticeDerivativeExponent lam
  let pIntermediate := intermediateExponent bounds.τ p
  let transferBound := Real.sqrt
    (auxiliaryMomentConstant bounds.β T K0 bounds.driftLipschitzConstant
      R0 ((M : ℝ) ^ (3 / 2 : ℝ)))
  let derivativeBound := derivativeSummabilityConstantAt bounds weightBase lam
    ((M : ℝ) ^ (3 * pIntermediate / 2))
  have hthetaOne := diffusionThetaOne_le_of_twoThirds_le diffusion hM
  have htransfer : eulerTransferConstant diffusion bounds K0 x0 ≤ transferBound := by
    exact eulerTransferConstant_le diffusion bounds x0 hT.le hinitial hthetaOne
  have hderivative :
      derivativeSummabilityConstant (diffusion := diffusion) bounds weightBase lam ≤
        derivativeBound := by
    exact derivativeSummabilityConstant_le_of_twoThirds_le bounds hT
      hweightBase hlamLower hlamUpper hM
  have hp : 0 ≤ p := by
    dsimp [p, latticeDerivativeExponent]
    positivity
  have htransfer0 : 0 ≤ eulerTransferConstant diffusion bounds K0 x0 :=
    Real.sqrt_nonneg _
  have hderivative0 : 0 ≤
      derivativeSummabilityConstant (diffusion := diffusion) bounds weightBase lam := by
    rw [derivativeSummabilityConstant_eq_at]
    unfold derivativeSummabilityConstantAt
    dsimp only
    let pActual := intermediateExponent bounds.τ (latticeDerivativeExponent lam)
    let AActual := latticeSubsetBase weightBase lam ^
        (pActual / latticeDerivativeExponent lam) *
      bounds.majorantConstant ^ pActual
    let HActual := treeSubsetConstantAt T AActual pActual bounds.τ
      (columnRhoSum diffusion pActual)
    have hHActual : 0 ≤ HActual :=
      (treeSubsetConstantAt_pos T AActual pActual bounds.τ
        (columnRhoSum diffusion pActual)).le
    exact Real.rpow_nonneg
      (mul_nonneg hHActual
        (factorialDecaySeries_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _)
            hHActual) _)) _
  have hinner :
      eulerTransferConstant diffusion bounds K0 x0 ^ p *
          derivativeSummabilityConstant (diffusion := diffusion) bounds weightBase lam ≤
        transferBound ^ p * derivativeBound := by
    exact mul_le_mul (Real.rpow_le_rpow htransfer0 htransfer hp)
      hderivative hderivative0 (Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  unfold latticeUniformMomentConstant dimensionUniformLatticeMomentConstant
  dsimp only
  exact Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg htransfer0 p) hderivative0)
    hinner (by linarith)

/-! ## Corollary 3.4 -/

/-- Single-rule part of paper Corollary 3.4.  Its right-hand side depends on the common bounds
`R0` and `M`, and contains neither `stateDim` nor `noiseDim`. -/
theorem corollary3_4_single_lattice
    {J stateDim noiseDim N : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K0 R0 : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK0 : 0 ≤ K0)
    (x0 : State stateDim) (hinitial : ‖x0‖ ≤ R0)
    {M : NNReal} (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
    (horigin : ∀ t, 0 ≤ t → t ≤ T → ‖drift t 0‖ ≤ K0)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (hNprime : Nat.Prime N)
    {epsilon : ℝ} (hepsilonPos : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    {wce : LatticeGenerator (Index J noiseDim) N → ℝ≥0∞}
    (hwceMeas : Measurable wce)
    (hshift : ∀ generator,
      (∫⁻ shift,
          ‖eulerLatticeError normalQuantile N drift diffusion payoff T x0
              generator shift‖ₑ ^ (2 : ℝ)
          ∂uniformShiftMeasure (Index J noiseDim)) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter
                (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
              zeroDiv
                (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x0 u ^ 2)
                (auxiliarySubsetWeight (eulerSamplingRho diffusion bounds epsilon)
                  (samplingLambda epsilon)
                  (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x0) u)) *
          wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator,
        wce generator ^ (2 * samplingLambda epsilon)
          ∂uniformGeneratorMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter
              (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
            auxiliarySubsetWeight (eulerSamplingRho diffusion bounds epsilon)
                (samplingLambda epsilon)
                (eulerGaussianSpaceComponent
                  drift diffusion payoff T bounds x0) u ^
              samplingLambda epsilon *
                eulerSamplingRho diffusion bounds epsilon ^ u.card) /
        ((N - 1 : ℕ) : ℝ≥0∞)) :
    eLpNorm'
        (fun input : LatticeGenerator (Index J noiseDim) N ×
            LatticeShift (Index J noiseDim) ↦
          eulerLatticeError normalQuantile N drift diffusion payoff T x0
            input.1 input.2)
        1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      ((2 * ENNReal.ofReal
          (dimensionUniformLatticeMomentConstant bounds K0 R0 M
            (dimensionUniformSamplingRho bounds M epsilon) (samplingLambda epsilon))) /
        (N : ℝ≥0∞)) ^ (1 - epsilon) := by
  have hmain := theorem3_1_single_lattice bounds hT hK0 x0 horigin
    hquantile hNprime hepsilonPos hepsilonHalf hwceMeas hshift hwce
  have hactualPos : 0 < eulerSamplingRho diffusion bounds epsilon :=
    eulerSamplingRho_pos bounds hepsilonPos hepsilonHalf
  have hconstant := latticeUniformMomentConstant_le_dimensionUniform
    (K0 := K0) bounds hT x0 hinitial hM hactualPos
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).1
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).2
  have hweightLe := eulerSamplingRho_le_dimensionUniform
    bounds hT hM hepsilonPos hepsilonHalf
  have hcommon := dimensionUniformLatticeMomentConstant_mono_weightBase
    (K0 := K0) (R0 := R0) bounds hT.le M hactualPos hweightLe
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).1
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).2
  have hconstant' := hconstant.trans hcommon
  calc
    eLpNorm'
        (fun input : LatticeGenerator (Index J noiseDim) N ×
            LatticeShift (Index J noiseDim) ↦
          eulerLatticeError normalQuantile N drift diffusion payoff T x0
            input.1 input.2)
        1 (randomizedLatticeMeasure (ι := Index J noiseDim) N) ≤
      ((2 * ENNReal.ofReal
          (latticeUniformMomentConstant (diffusion := diffusion)
            bounds (eulerSamplingRho diffusion bounds epsilon) (samplingLambda epsilon)
              (eulerTransferConstant diffusion bounds K0 x0))) /
        (N : ℝ≥0∞)) ^ (1 - epsilon) := hmain
    _ ≤ ((2 * ENNReal.ofReal
          (dimensionUniformLatticeMomentConstant bounds K0 R0 M
            (dimensionUniformSamplingRho bounds M epsilon) (samplingLambda epsilon))) /
        (N : ℝ≥0∞)) ^ (1 - epsilon) := by
      apply ENNReal.rpow_le_rpow _ (by linarith)
      apply ENNReal.div_le_div_right
      simpa [mul_comm] using mul_le_mul_right
        (ENNReal.ofReal_le_ofReal hconstant') (2 : ℝ≥0∞)

/-- Median part of paper Corollary 3.4, with the same dimension-free lattice constant. -/
theorem corollary3_4_median_lattice
    {J stateDim noiseDim N k : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T K0 R0 : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T) (hK0 : 0 ≤ K0)
    (x0 : State stateDim) (hinitial : ‖x0‖ ≤ R0)
    {M : NNReal} (hM : TimeDependentLattice.columnSum diffusion (2 / 3) ≤ M)
    (horigin : ∀ t, 0 ≤ t → t ≤ T → ‖drift t 0‖ ≤ K0)
    {normalQuantile : ℝ → ℝ} (hquantile : Measurable normalQuantile)
    (hNprime : Nat.Prime N)
    {epsilon q : ℝ} (hepsilonPos : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hqOne : 1 ≤ q) (hk : 0 < k) (hqRange : q < k / (1 - epsilon))
    {wce : LatticeGenerator (Index J noiseDim) N → ℝ≥0∞}
    (hwceMeas : Measurable wce)
    (hshift : ∀ generator,
      (∫⁻ shift,
          ‖eulerLatticeError normalQuantile N drift diffusion payoff T x0
              generator shift‖ₑ ^ (2 : ℝ)
          ∂uniformShiftMeasure (Index J noiseDim)) ≤
        ENNReal.ofReal
            (∑ u ∈ Finset.univ.powerset.filter
                (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
              zeroDiv
                (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x0 u ^ 2)
                (auxiliarySubsetWeight (eulerSamplingRho diffusion bounds epsilon)
                  (samplingLambda epsilon)
                  (eulerGaussianSpaceComponent
                    drift diffusion payoff T bounds x0) u)) *
          wce generator ^ (2 : ℝ))
    (hwce : (∫⁻ generator,
        wce generator ^ (2 * samplingLambda epsilon)
          ∂uniformGeneratorMeasure (ι := Index J noiseDim) N) ≤
      ENNReal.ofReal
          (∑ u ∈ Finset.univ.powerset.filter
              (fun u : Finset (Index J noiseDim) ↦ u.Nonempty),
            auxiliarySubsetWeight (eulerSamplingRho diffusion bounds epsilon)
                (samplingLambda epsilon)
                (eulerGaussianSpaceComponent
                  drift diffusion payoff T bounds x0) u ^
              samplingLambda epsilon *
                eulerSamplingRho diffusion bounds epsilon ^ u.card) /
        ((N - 1 : ℕ) : ℝ≥0∞))
    (medianEstimator :
      RepeatedRandomizedLatticeInput (Index J noiseDim) N (2 * k - 1) → ℝ)
    (hmedian : ∀ input,
      IsOddMedian k
        (fun i ↦ eulerLatticeRule normalQuantile N drift diffusion payoff T x0
          (input i).1 (input i).2)
        (medianEstimator input)) :
    eLpNorm'
        (fun input ↦ medianEstimator input -
          eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
        q (repeatedRandomizedLatticeMeasure
          (ι := Index J noiseDim) N (2 * k - 1)) ≤
      medianPaperPrefactor (2 * k - 1) k (2 * samplingLambda epsilon) q *
        ((2 * ENNReal.ofReal
          (dimensionUniformLatticeMomentConstant bounds K0 R0 M
            (dimensionUniformSamplingRho bounds M epsilon) (samplingLambda epsilon))) /
          (N : ℝ≥0∞)) ^ (1 - epsilon) := by
  have hmain := theorem3_1_median_lattice bounds hT hK0 x0 horigin hquantile
    hNprime hepsilonPos hepsilonHalf hqOne hk hqRange hwceMeas
    hshift hwce medianEstimator hmedian
  have hactualPos : 0 < eulerSamplingRho diffusion bounds epsilon :=
    eulerSamplingRho_pos bounds hepsilonPos hepsilonHalf
  have hconstant := latticeUniformMomentConstant_le_dimensionUniform
    (K0 := K0) bounds hT x0 hinitial hM hactualPos
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).1
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).2
  have hweightLe := eulerSamplingRho_le_dimensionUniform
    bounds hT hM hepsilonPos hepsilonHalf
  have hcommon := dimensionUniformLatticeMomentConstant_mono_weightBase
    (K0 := K0) (R0 := R0) bounds hT.le M hactualPos hweightLe
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).1
    (samplingLambda_mem_interval hepsilonPos hepsilonHalf).2
  have hconstant' := hconstant.trans hcommon
  calc
    eLpNorm'
        (fun input ↦ medianEstimator input -
          eulerGaussianIntegral (J := J) drift diffusion payoff T x0)
        q (repeatedRandomizedLatticeMeasure
          (ι := Index J noiseDim) N (2 * k - 1)) ≤
      medianPaperPrefactor (2 * k - 1) k (2 * samplingLambda epsilon) q *
        ((2 * ENNReal.ofReal
          (latticeUniformMomentConstant (diffusion := diffusion)
            bounds (eulerSamplingRho diffusion bounds epsilon) (samplingLambda epsilon)
              (eulerTransferConstant diffusion bounds K0 x0))) /
          (N : ℝ≥0∞)) ^ (1 - epsilon) := hmain
    _ ≤ medianPaperPrefactor (2 * k - 1) k (2 * samplingLambda epsilon) q *
        ((2 * ENNReal.ofReal
          (dimensionUniformLatticeMomentConstant bounds K0 R0 M
            (dimensionUniformSamplingRho bounds M epsilon) (samplingLambda epsilon))) /
          (N : ℝ≥0∞)) ^ (1 - epsilon) := by
      apply mul_le_mul_right
      apply ENNReal.rpow_le_rpow _ (by linarith)
      apply ENNReal.div_le_div_right
      simpa [mul_comm] using mul_le_mul_right
        (ENNReal.ofReal_le_ofReal hconstant') (2 : ℝ≥0∞)

end

end TimeDependentLattice.Sampling
