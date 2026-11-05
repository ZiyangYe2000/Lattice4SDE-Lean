/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.DimensionUniform

/-!
# The sampling constant chosen in the paper

Equation (5.8) evaluates the derivative constant at the actual `Theta_(2/3)`.
The earlier estimates retain the finer intermediate column sum. The comparison below
enlarges only that derivative constant: `alpha` and `rho_lambda` retain the actual `Theta_1`.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open TimeDependentLattice.BrownianBridge TimeDependentLattice.Euler
  TimeDependentLattice.Regularity TimeDependentLattice.Trees

/-- The exact `C_lat` in equation (5.8) of the paper. -/
def eulerPaperLatticeMomentConstant
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ ε : ℝ) (x₀ : State stateDim) : ℝ :=
  let lam := samplingLambda ε
  auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
      ‖x₀‖ (diffusionThetaOne diffusion) ^ lam *
    paperDerivativeConstant bounds (latticeSubsetBase (eulerSamplingRho diffusion bounds ε) lam)
      (latticeDerivativeExponent lam) (TimeDependentLattice.columnSum diffusion (2 / 3) : ℝ) ^
        (1 + lam)

/-- Equation (5.8), exposing the paper's choices of `kappa` and `p`. -/
theorem eulerPaperLatticeMomentConstant_eq_paper_formula
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ ε : ℝ) (x₀ : State stateDim) :
    eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀ =
      let lam := samplingLambda ε
      auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
          ‖x₀‖ (diffusionThetaOne diffusion) ^ lam *
        paperDerivativeConstant bounds (eulerSamplingRho diffusion bounds ε ^ (1 / (1 + lam)))
          (2 * lam / (1 + lam)) (TimeDependentLattice.columnSum diffusion (2 / 3) : ℝ) ^
            (1 + lam) := rfl

private theorem paperDerivativeConstant_nonneg_all
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (κ p theta : ℝ) :
    0 ≤ paperDerivativeConstant bounds κ p theta := by
  let ρ := intermediateExponent bounds.τ p
  let A := κ ^ (ρ / p) * bounds.majorantConstant ^ ρ
  let H := treeSubsetConstantAt T A ρ bounds.τ (theta ^ (3 * ρ / 2))
  have hH : 0 ≤ H := (treeSubsetConstantAt_pos _ _ _ _ _).le
  change 0 ≤ derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ ^ (p / ρ)
  apply Real.rpow_nonneg
  unfold derivativeRhoConstant
  exact mul_nonneg hH (factorialDecaySeries_nonneg
    (mul_nonneg (Real.rpow_nonneg
      (zero_le_one.trans bounds.one_le_majorantConstant) _) hH) _)

theorem eulerPaperLatticeMomentConstant_nonneg
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ ε : ℝ) (x₀ : State stateDim) :
    0 ≤ eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀ := by
  unfold eulerPaperLatticeMomentConstant
  dsimp only
  exact mul_nonneg (Real.rpow_nonneg (auxiliaryMomentConstant_pos _ _ _ _ _ _).le _)
    (Real.rpow_nonneg (paperDerivativeConstant_nonneg_all bounds _ _ _) _)

theorem eulerPaperLatticeMomentConstant_pos
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim)
    (hε : 0 < ε) (hεHalf : ε < 1 / 2) :
    0 < eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀ := by
  have hlam := samplingLambda_mem_interval hε hεHalf
  have hp : 2 / 3 < latticeDerivativeExponent (samplingLambda ε) := by
    unfold latticeDerivativeExponent
    apply (lt_div_iff₀ (by linarith : 0 < 1 + samplingLambda ε)).2
    nlinarith [hlam.1]
  unfold eulerPaperLatticeMomentConstant
  dsimp only
  exact mul_pos (Real.rpow_pos_of_pos (auxiliaryMomentConstant_pos _ _ _ _ _ _) _)
    (Real.rpow_pos_of_pos (paperDerivativeConstant_pos bounds hp) _)

/-- The transfer-power form used by the lower-level moment estimate is algebraically equal
to the paper's `C_aux^lambda` formula. -/
theorem eulerPaperLatticeMomentConstant_eq_transfer_power
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim)
    (hε : 0 < ε) (hεHalf : ε < 1 / 2) :
    eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀ =
      (eulerTransferConstant diffusion bounds K₀ x₀ ^ latticeDerivativeExponent (samplingLambda ε) *
        paperDerivativeConstant bounds
          (latticeSubsetBase (eulerSamplingRho diffusion bounds ε) (samplingLambda ε))
          (latticeDerivativeExponent (samplingLambda ε))
          (TimeDependentLattice.columnSum diffusion (2 / 3) : ℝ)) ^ (1 + samplingLambda ε) := by
  let lam := samplingLambda ε
  let p := latticeDerivativeExponent lam
  let aux := auxiliaryMomentConstant bounds.β T K₀ bounds.driftLipschitzConstant
    ‖x₀‖ (diffusionThetaOne diffusion)
  let D := paperDerivativeConstant bounds
    (latticeSubsetBase (eulerSamplingRho diffusion bounds ε) lam) p
    (TimeDependentLattice.columnSum diffusion (2 / 3) : ℝ)
  have haux : 0 ≤ aux := (auxiliaryMomentConstant_pos _ _ _ _ _ _).le
  have hD : 0 ≤ D := paperDerivativeConstant_nonneg_all bounds _ _ _
  have hden : 1 + lam ≠ 0 := by
    have := (samplingLambda_mem_interval hε hεHalf).1
    dsimp [lam]
    linarith
  have hpower : (eulerTransferConstant diffusion bounds K₀ x₀ ^ p) ^ (1 + lam) =
      aux ^ lam := by
    change ((Real.sqrt aux) ^ p) ^ (1 + lam) = aux ^ lam
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul haux, ← Real.rpow_mul haux]
    congr 1
    dsimp [p, latticeDerivativeExponent]
    field_simp [hden]
  change aux ^ lam * D ^ (1 + lam) =
    (eulerTransferConstant diffusion bounds K₀ x₀ ^ p * D) ^ (1 + lam)
  rw [Real.mul_rpow
    (Real.rpow_nonneg
      (show 0 ≤ eulerTransferConstant diffusion bounds K₀ x₀ from Real.sqrt_nonneg _) p) hD,
    hpower]

/-- The earlier intermediate-column estimate is bounded by the exact paper constant.
Only `Theta_rho` is replaced by `Theta_(2/3)^(3 rho/2)`; no bound replaces `Theta_1`. -/
theorem latticeUniformMomentConstant_le_eulerPaperLatticeMomentConstant
    {stateDim noiseDim : ℕ} {drift : Drift stateDim}
    (diffusion : Diffusion stateDim noiseDim) {payoff : Payoff stateDim} {T ε : ℝ}
    (bounds : GevreyBounds drift payoff T) (K₀ : ℝ) (x₀ : State stateDim)
    (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε < 1 / 2) :
    latticeUniformMomentConstant (diffusion := diffusion) bounds
        (eulerSamplingRho diffusion bounds ε) (samplingLambda ε)
        (eulerTransferConstant diffusion bounds K₀ x₀) ≤
      eulerPaperLatticeMomentConstant diffusion bounds K₀ ε x₀ := by
  have hlam := samplingLambda_mem_interval hε hεHalf
  have hderivative := derivativeSummabilityConstant_le_of_twoThirds_le
    (diffusion := diffusion) bounds hT
    (eulerSamplingRho_pos (diffusion := diffusion) bounds hε hεHalf) hlam.1 hlam.2
    (M := TimeDependentLattice.columnSum diffusion (2 / 3)) le_rfl
  change derivativeSummabilityConstant (diffusion := diffusion) bounds
      (eulerSamplingRho diffusion bounds ε) (samplingLambda ε) ≤
    paperDerivativeConstant bounds
      (latticeSubsetBase (eulerSamplingRho diffusion bounds ε) (samplingLambda ε))
      (latticeDerivativeExponent (samplingLambda ε))
      (TimeDependentLattice.columnSum diffusion (2 / 3) : ℝ) at hderivative
  rw [eulerPaperLatticeMomentConstant_eq_transfer_power diffusion bounds K₀ x₀ hε hεHalf]
  unfold latticeUniformMomentConstant
  apply Real.rpow_le_rpow
  · exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (derivativeSummabilityConstant_pos bounds hlam.1).le
  · exact mul_le_mul_of_nonneg_left hderivative (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  · linarith [hlam.1]

end

end TimeDependentLattice.Sampling
