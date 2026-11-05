/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.AnalyticBound

/-!
# Explicit constants for the Euler-bias branch

The paper makes the constants in Appendix E explicit.  The definitions below reproduce
those choices for the deductions after the standard continuous-time stochastic estimates have
been supplied through explicit interfaces.

No optimality is claimed.  The formulas are chosen because their dependence on the initial-state
norm and the Hilbert--Schmidt bound is manifestly monotone.
-/

namespace TimeDependentLattice.Bias

noncomputable section

/-- The right-hand side of the paper's `L²` state moment estimate (Lemma E.2), evaluated at the
initial state used by the two Euler convergence theorems. -/
def stateMomentConstant (T K0 L initialNorm sigmaHS : ℝ) : ℝ :=
  Real.exp (L * T) * (initialNorm + K0 * T + 2 * Real.sqrt T * sigmaHS)

/-- The prefactor `C_exp` in the exponential state-moment estimate.

The factor `10` comes from the reflection-principle estimate in Lemma E.1 and the two state
processes appearing in Lemma E.2. -/
def stateExponentialPrefactor (v T K0 L sigmaHS : ℝ) : ℝ :=
  10 * Real.exp
    (v * Real.exp (L * T) * K0 * T +
      v ^ 2 * Real.exp (2 * L * T) * T * (1 + sigmaHS ^ 2))

/-- The constant in the payoff-transfer estimate `|I_m - I| ≤ C_pay ‖X_T^h - X_T‖₂`. -/
def payoffDifferenceConstant
    (G0 G1 beta T K0 L initialNorm sigmaHS : ℝ) : ℝ :=
  G0 * G1 *
    Real.sqrt (2 * stateExponentialPrefactor (2 * beta) T K0 L sigmaHS) *
      Real.exp (beta * Real.exp (L * T) * initialNorm)

/-- The explicit `L²` time-increment constant used in the proof of paper Theorem 3.7. -/
def incrementConstant (T K0 L initialNorm sigmaHS : ℝ) : ℝ :=
  Real.sqrt T * (K0 + L * stateMomentConstant T K0 L initialNorm sigmaHS) + sigmaHS

/-- The strong half-order constant in paper Theorem 3.7. -/
def strongHalfConstant
    (T K0 L Ht initialNorm sigmaHS : ℝ) : ℝ :=
  (2 / 3 : ℝ) * Real.exp (L * T) * T * Real.sqrt T *
    (L * incrementConstant T K0 L initialNorm sigmaHS +
      Ht * (1 + stateMomentConstant T K0 L initialNorm sigmaHS))

/-- The half-order Euler bias constant obtained from the strong estimate and payoff transfer. -/
def biasHalfConstant
    (G0 G1 beta T K0 L Ht initialNorm sigmaHS : ℝ) : ℝ :=
  payoffDifferenceConstant G0 G1 beta T K0 L initialNorm sigmaHS *
    strongHalfConstant T K0 L Ht initialNorm sigmaHS

/-- The `L²` drift-remainder constant used in the proof of paper Theorem 3.8. -/
def driftRemainderConstant
    (T K0 L B2 Lt initialNorm sigmaHS : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Lt + L * K0 + (1 / 2 : ℝ) * B2 * sigmaHS ^ 2) +
    (1 / 2 : ℝ) * (Lt + L ^ 2) *
      stateMomentConstant T K0 L initialNorm sigmaHS

/-- The auxiliary strong first-order constant used in the proof of paper Theorem 3.8. -/
def strongOneConstant
    (T K0 L B2 Lt initialNorm sigmaHS : ℝ) : ℝ :=
  Real.exp (L * T) *
    (T * driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS +
      2 * L * sigmaHS * Real.sqrt (T / 3))

/-- The first-order Euler bias constant in paper Theorem 3.8. -/
def biasOneConstant
    (G0 G1 beta T K0 L B2 Lt initialNorm sigmaHS : ℝ) : ℝ :=
  T * payoffDifferenceConstant G0 G1 beta T K0 L initialNorm sigmaHS *
    strongOneConstant T K0 L B2 Lt initialNorm sigmaHS

/-- The Hilbert--Schmidt upper bound obtained from the common `M_(2/3)` bound. -/
def sigmaBoundFromTwoThirds (M : NNReal) : ℝ :=
  (M : ℝ) ^ (3 / 2 : ℝ)

/-- Dimension-uniform half-order bias constant. -/
def uniformBiasHalfConstant
    (G0 G1 beta T K0 L Ht R0 : ℝ) (M : NNReal) : ℝ :=
  biasHalfConstant G0 G1 beta T K0 L Ht R0 (sigmaBoundFromTwoThirds M)

/-- Dimension-uniform first-order bias constant. -/
def uniformBiasOneConstant
    (G0 G1 beta T K0 L B2 Lt R0 : ℝ) (M : NNReal) : ℝ :=
  biasOneConstant G0 G1 beta T K0 L B2 Lt R0 (sigmaBoundFromTwoThirds M)

theorem stateMomentConstant_nonneg
    {T K0 L initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS) :
    0 ≤ stateMomentConstant T K0 L initialNorm sigmaHS := by
  unfold stateMomentConstant
  positivity

theorem stateExponentialPrefactor_pos (v T K0 L sigmaHS : ℝ) :
    0 < stateExponentialPrefactor v T K0 L sigmaHS := by
  unfold stateExponentialPrefactor
  positivity

theorem payoffDifferenceConstant_nonneg
    {G0 G1 beta T K0 L initialNorm sigmaHS : ℝ}
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) :
    0 ≤ payoffDifferenceConstant G0 G1 beta T K0 L initialNorm sigmaHS := by
  unfold payoffDifferenceConstant
  positivity

theorem incrementConstant_nonneg
    {T K0 L initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS) :
    0 ≤ incrementConstant T K0 L initialNorm sigmaHS := by
  unfold incrementConstant
  positivity [stateMomentConstant_nonneg (L := L) hT hK0 hinitial hsigma]

theorem strongHalfConstant_nonneg
    {T K0 L Ht initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS) :
    0 ≤ strongHalfConstant T K0 L Ht initialNorm sigmaHS := by
  unfold strongHalfConstant
  positivity [stateMomentConstant_nonneg (L := L) hT hK0 hinitial hsigma,
    incrementConstant_nonneg hT hK0 hL hinitial hsigma]

theorem driftRemainderConstant_nonneg
    {T K0 L B2 Lt initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hLt : 0 ≤ Lt) (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS) :
    0 ≤ driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS := by
  unfold driftRemainderConstant
  positivity [stateMomentConstant_nonneg (L := L) hT hK0 hinitial hsigma]

theorem strongOneConstant_nonneg
    {T K0 L B2 Lt initialNorm sigmaHS : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hLt : 0 ≤ Lt) (hinitial : 0 ≤ initialNorm) (hsigma : 0 ≤ sigmaHS) :
    0 ≤ strongOneConstant T K0 L B2 Lt initialNorm sigmaHS := by
  unfold strongOneConstant
  positivity [driftRemainderConstant_nonneg hT hK0 hL hB2 hLt hinitial hsigma]

theorem stateMomentConstant_mono
    {T K0 L initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hinitial : initialNorm ≤ initialBound) (hsigma : sigmaHS ≤ sigmaBound) :
    stateMomentConstant T K0 L initialNorm sigmaHS ≤
      stateMomentConstant T K0 L initialBound sigmaBound := by
  unfold stateMomentConstant
  gcongr

theorem stateExponentialPrefactor_mono
    {v T K0 L sigmaHS sigmaBound : ℝ}
    (hT : 0 ≤ T) (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBound) :
    stateExponentialPrefactor v T K0 L sigmaHS ≤
      stateExponentialPrefactor v T K0 L sigmaBound := by
  unfold stateExponentialPrefactor
  have hsquare : sigmaHS ^ 2 ≤ sigmaBound ^ 2 := by
    nlinarith
  gcongr

theorem payoffDifferenceConstant_mono
    {G0 G1 beta T K0 L initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hT : 0 ≤ T) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hbeta : 0 ≤ beta)
    (hinitial : initialNorm ≤ initialBound)
    (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBound) :
    payoffDifferenceConstant G0 G1 beta T K0 L initialNorm sigmaHS ≤
      payoffDifferenceConstant G0 G1 beta T K0 L initialBound sigmaBound := by
  unfold payoffDifferenceConstant
  have hprefactor := stateExponentialPrefactor_mono
    (v := 2 * beta) (T := T) (K0 := K0) (L := L)
    hT hsigma0 hsigma
  have hexponent :
      beta * Real.exp (L * T) * initialNorm ≤
        beta * Real.exp (L * T) * initialBound := by
    gcongr
  gcongr

theorem incrementConstant_mono
    {T K0 L initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hL : 0 ≤ L) (hinitial : initialNorm ≤ initialBound)
    (hsigma : sigmaHS ≤ sigmaBound) :
    incrementConstant T K0 L initialNorm sigmaHS ≤
      incrementConstant T K0 L initialBound sigmaBound := by
  unfold incrementConstant
  have hstate := stateMomentConstant_mono
    (T := T) (K0 := K0) (L := L) hinitial hsigma
  gcongr

theorem strongHalfConstant_mono
    {T K0 L Ht initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hinitial : initialNorm ≤ initialBound) (hsigma : sigmaHS ≤ sigmaBound) :
    strongHalfConstant T K0 L Ht initialNorm sigmaHS ≤
      strongHalfConstant T K0 L Ht initialBound sigmaBound := by
  unfold strongHalfConstant
  have hstate := stateMomentConstant_mono
    (T := T) (K0 := K0) (L := L) hinitial hsigma
  have hincrement := incrementConstant_mono
    (T := T) (K0 := K0) (L := L) hL hinitial hsigma
  gcongr

theorem driftRemainderConstant_mono
    {T K0 L B2 Lt initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hB2 : 0 ≤ B2) (hLt : 0 ≤ Lt)
    (hinitial : initialNorm ≤ initialBound)
    (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBound) :
    driftRemainderConstant T K0 L B2 Lt initialNorm sigmaHS ≤
      driftRemainderConstant T K0 L B2 Lt initialBound sigmaBound := by
  unfold driftRemainderConstant
  have hstate := stateMomentConstant_mono
    (T := T) (K0 := K0) (L := L) hinitial hsigma
  have hsquare : sigmaHS ^ 2 ≤ sigmaBound ^ 2 := by
    nlinarith
  gcongr

theorem strongOneConstant_mono
    {T K0 L B2 Lt initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hB2 : 0 ≤ B2) (hLt : 0 ≤ Lt)
    (hinitial : initialNorm ≤ initialBound)
    (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBound) :
    strongOneConstant T K0 L B2 Lt initialNorm sigmaHS ≤
      strongOneConstant T K0 L B2 Lt initialBound sigmaBound := by
  unfold strongOneConstant
  have hdrift := driftRemainderConstant_mono
    (T := T) (K0 := K0) (L := L) hB2 hLt hinitial hsigma0 hsigma
  gcongr

theorem biasHalfConstant_mono
    {G0 G1 beta T K0 L Ht initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hbeta : 0 ≤ beta)
    (hinitial0 : 0 ≤ initialNorm) (hinitial : initialNorm ≤ initialBound)
    (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBound) :
    biasHalfConstant G0 G1 beta T K0 L Ht initialNorm sigmaHS ≤
      biasHalfConstant G0 G1 beta T K0 L Ht initialBound sigmaBound := by
  unfold biasHalfConstant
  exact mul_le_mul
    (payoffDifferenceConstant_mono hT hG0 hG1 hbeta hinitial hsigma0 hsigma)
    (strongHalfConstant_mono hT hL hHt hinitial hsigma)
    (strongHalfConstant_nonneg hT hK0 hL hHt hinitial0 hsigma0)
    (payoffDifferenceConstant_nonneg hG0 hG1)

theorem biasOneConstant_mono
    {G0 G1 beta T K0 L B2 Lt initialNorm initialBound sigmaHS sigmaBound : ℝ}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hLt : 0 ≤ Lt) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hbeta : 0 ≤ beta)
    (hinitial0 : 0 ≤ initialNorm) (hinitial : initialNorm ≤ initialBound)
    (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBound) :
    biasOneConstant G0 G1 beta T K0 L B2 Lt initialNorm sigmaHS ≤
      biasOneConstant G0 G1 beta T K0 L B2 Lt initialBound sigmaBound := by
  unfold biasOneConstant
  have hpayoff := payoffDifferenceConstant_mono
    (K0 := K0) (L := L) hT hG0 hG1 hbeta hinitial hsigma0 hsigma
  have hstrong := strongOneConstant_mono
    (K0 := K0) hT hL hB2 hLt hinitial hsigma0 hsigma
  have hproduct :
      payoffDifferenceConstant G0 G1 beta T K0 L initialNorm sigmaHS *
          strongOneConstant T K0 L B2 Lt initialNorm sigmaHS ≤
        payoffDifferenceConstant G0 G1 beta T K0 L initialBound sigmaBound *
          strongOneConstant T K0 L B2 Lt initialBound sigmaBound :=
    mul_le_mul hpayoff hstrong
      (strongOneConstant_nonneg hT hK0 hL hB2 hLt hinitial0 hsigma0)
      (payoffDifferenceConstant_nonneg hG0 hG1)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hT

theorem biasHalfConstant_le_uniform
    {G0 G1 beta T K0 L Ht initialNorm R0 sigmaHS : ℝ} {M : NNReal}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hHt : 0 ≤ Ht)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hbeta : 0 ≤ beta)
    (hinitial0 : 0 ≤ initialNorm) (hinitial : initialNorm ≤ R0)
    (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBoundFromTwoThirds M) :
    biasHalfConstant G0 G1 beta T K0 L Ht initialNorm sigmaHS ≤
      uniformBiasHalfConstant G0 G1 beta T K0 L Ht R0 M := by
  exact biasHalfConstant_mono hT hK0 hL hHt hG0 hG1 hbeta
    hinitial0 hinitial hsigma0 hsigma

theorem biasOneConstant_le_uniform
    {G0 G1 beta T K0 L B2 Lt initialNorm R0 sigmaHS : ℝ} {M : NNReal}
    (hT : 0 ≤ T) (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hB2 : 0 ≤ B2)
    (hLt : 0 ≤ Lt) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hbeta : 0 ≤ beta)
    (hinitial0 : 0 ≤ initialNorm) (hinitial : initialNorm ≤ R0)
    (hsigma0 : 0 ≤ sigmaHS) (hsigma : sigmaHS ≤ sigmaBoundFromTwoThirds M) :
    biasOneConstant G0 G1 beta T K0 L B2 Lt initialNorm sigmaHS ≤
      uniformBiasOneConstant G0 G1 beta T K0 L B2 Lt R0 M := by
  exact biasOneConstant_mono hT hK0 hL hB2 hLt hG0 hG1 hbeta
    hinitial0 hinitial hsigma0 hsigma

end

end TimeDependentLattice.Bias
