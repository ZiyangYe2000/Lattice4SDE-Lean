/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.MajorantAssembly

/-!
# The displayed tree constant of the paper

The root-only payoff term in the paper's maximum is already absorbed by the
tree coefficient constant. Thus the simplified implementation is exactly the
paper's displayed constant, rather than a different admissible upper bound.
-/

namespace TimeDependentLattice.Trees

open TimeDependentLattice.Euler

/-- The implementation of `C_maj` equals the full maximum displayed in the paper. -/
theorem GevreyBounds.majorantConstant_eq_paper_formula
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    bounds.majorantConstant =
      max (64 * bounds.coefficientBase ^ 6 * max 1 T)
        (bounds.G₁ * max 1 bounds.G₀) := by
  have hK : bounds.coefficientBase ≤ bounds.coefficientBase ^ 6 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ bounds.one_le_coefficientBase (by norm_num : 1 ≤ 6))
  have hcount : bounds.coefficientCountBase ≤ bounds.majorantConstant := by
    have hnonneg : 0 ≤ bounds.coefficientCountBase :=
      pow_nonneg (zero_le_one.trans bounds.one_le_coefficientBase) _
    have hfactor : 1 ≤ 64 * max 1 T := by
      nlinarith [show (1 : ℝ) ≤ max 1 T from le_max_left _ _]
    calc
      bounds.coefficientCountBase ≤ bounds.coefficientCountBase * (64 * max 1 T) :=
        le_mul_of_one_le_right hnonneg hfactor
      _ = bounds.majorantConstant := by
        unfold GevreyBounds.majorantConstant
        ring
  have hG₁ : bounds.G₁ ≤ bounds.majorantConstant :=
    bounds.G₁_le_coefficientBase.trans (hK.trans hcount)
  have hG₀G₁ : bounds.G₀ * bounds.G₁ ≤ bounds.majorantConstant := by
    simpa only [pow_one] using bounds.rootCoefficient_le_majorantConstant_pow 1 zero_lt_one
  have hroot : bounds.G₁ * max 1 bounds.G₀ ≤ bounds.majorantConstant := by
    rw [mul_max_of_nonneg _ _ bounds.G₁_pos.le]
    simpa only [mul_one, mul_comm] using max_le hG₁ hG₀G₁
  change bounds.majorantConstant = max bounds.majorantConstant (bounds.G₁ * max 1 bounds.G₀)
  exact (max_eq_left hroot).symm

end TimeDependentLattice.Trees
