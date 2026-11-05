/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.MajorantAssembly
import TimeDependentLattice.Regularity.Summability

/-!
# Normalized mixed-derivative envelope

This is Equation (4.1) of the paper, for the dyadic Euler level `m = 2^J`.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open TimeDependentLattice
open TimeDependentLattice.Analysis
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Euler
open TimeDependentLattice.Trees

/-- The pointwise normalized absolute mixed derivative. -/
def normalizedMixedDerivativeAt
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T β : ℝ) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim)) (z : Input J noiseDim) : ℝ :=
  |mixedDerivative (integrand drift diffusion payoff T x₀) support z| /
    Real.exp (β * ‖terminalState drift diffusion T x₀ z‖)

/-- Equation (4.1): supremum of the normalized derivative over all Gaussian inputs. -/
def normalizedDerivativeEnvelope
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T β : ℝ) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim)) : ℝ :=
  sSup (Set.range
    (normalizedMixedDerivativeAt drift diffusion payoff T β x₀ support))

theorem normalizedMixedDerivativeAt_nonneg
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T β : ℝ) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim)) (z : Input J noiseDim) :
    0 ≤ normalizedMixedDerivativeAt drift diffusion payoff T β x₀ support z := by
  unfold normalizedMixedDerivativeAt
  positivity

/-- Every pointwise normalized derivative is below the envelope whenever the range is bounded,
as supplied later by Proposition 4.3. -/
theorem normalizedMixedDerivativeAt_le_envelope
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T β : ℝ) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim))
    (hbounded : BddAbove (Set.range
      (normalizedMixedDerivativeAt drift diffusion payoff T β x₀ support)))
    (z : Input J noiseDim) :
    normalizedMixedDerivativeAt drift diffusion payoff T β x₀ support z ≤
      normalizedDerivativeEnvelope drift diffusion payoff T β x₀ support := by
  unfold normalizedDerivativeEnvelope
  exact le_csSup hbounded ⟨z, rfl⟩

/-- The normalized envelope is nonnegative once Proposition 4.3 supplies boundedness. -/
theorem normalizedDerivativeEnvelope_nonneg
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T β : ℝ) (x₀ : State stateDim)
    (support : Finset (Index J noiseDim))
    (hbounded : BddAbove (Set.range
      (normalizedMixedDerivativeAt drift diffusion payoff T β x₀ support))) :
    0 ≤ normalizedDerivativeEnvelope drift diffusion payoff T β x₀ support := by
  let z : Input J noiseDim := 0
  exact (normalizedMixedDerivativeAt_nonneg drift diffusion payoff T β x₀ support z).trans
    (normalizedMixedDerivativeAt_le_envelope drift diffusion payoff T β x₀ support hbounded z)

/-- Proposition 4.3 in the canonical finite-key presentation used by the Lean proof.  Its keys
are exactly the paper pairs `(E, π)`. -/
theorem normalizedDerivativeEnvelope_le_keyMajorantSum
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty) :
    normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ≤
      ∑ key : MajorantKey support, keyMajorant bounds diffusion key := by
  let upper : ℝ := ∑ key : MajorantKey support, keyMajorant bounds diffusion key
  have hpoint (z : Input J noiseDim) :
      normalizedMixedDerivativeAt drift diffusion payoff T bounds.β x₀ support z ≤ upper := by
    have htree := normalized_mixedDerivative_le_keyMajorantSum
      bounds hT diffusion x₀ z support hsupport
    unfold normalizedMixedDerivativeAt
    have hexp : Real.exp (bounds.β * ‖terminalState drift diffusion T x₀ z‖) ≠ 0 :=
      (Real.exp_pos _).ne'
    calc
      |mixedDerivative (integrand drift diffusion payoff T x₀) support z| /
          Real.exp (bounds.β * ‖terminalState drift diffusion T x₀ z‖) =
        Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
          |mixedDerivative (integrand drift diffusion payoff T x₀) support z| := by
            rw [div_eq_mul_inv, ← Real.exp_neg]
            ring_nf
      _ ≤ upper := htree
  unfold normalizedDerivativeEnvelope
  apply csSup_le
  · exact ⟨normalizedMixedDerivativeAt
      drift diffusion payoff T bounds.β x₀ support 0, ⟨0, rfl⟩⟩
  · rintro value ⟨z, rfl⟩
    exact hpoint z

/-- Proposition 4.3 also supplies the boundedness needed by the supremum definition. -/
theorem normalizedMixedDerivativeAt_bddAbove
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty) :
    BddAbove (Set.range
      (normalizedMixedDerivativeAt drift diffusion payoff T bounds.β x₀ support)) := by
  refine ⟨∑ key : MajorantKey support, keyMajorant bounds diffusion key, ?_⟩
  rintro value ⟨z, rfl⟩
  have htree := normalized_mixedDerivative_le_keyMajorantSum
    bounds hT diffusion x₀ z support hsupport
  unfold normalizedMixedDerivativeAt
  calc
    |mixedDerivative (integrand drift diffusion payoff T x₀) support z| /
        Real.exp (bounds.β * ‖terminalState drift diffusion T x₀ z‖) =
      Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
        |mixedDerivative (integrand drift diffusion payoff T x₀) support z| := by
          rw [div_eq_mul_inv, ← Real.exp_neg]
          ring_nf
    _ ≤ _ := htree

/-- Theorem 4.1 specialized to the actual Euler derivative envelopes, once the preceding
`ρ`-estimate has been supplied by Proposition 4.3 and Lemmas 4.4--4.5. -/
theorem euler_normalizedDerivative_summability_from_rho_estimate
    {stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (payoff : Payoff stateDim) (T β : ℝ) (x₀ : State stateDim)
    (κ p τ rhoBound : ℝ) (hκ : 0 < κ) (hτone : 1 ≤ τ) (hτ : τ < 3 / 2)
    (hp : 2 / 3 < p)
    (hbounded : ∀ J support, BddAbove (Set.range
      (normalizedMixedDerivativeAt (J := J)
        drift diffusion payoff T β x₀ support)))
    (hRhoBound : ∀ J,
      ∑ u ∈ Finset.univ.powerset.filter
          (fun u : Finset (Index J noiseDim) => u.Nonempty),
        (κ ^ ((u.card : ℝ) / p) *
          normalizedDerivativeEnvelope drift diffusion payoff T β x₀ u) ^
            intermediateExponent τ p ≤ rhoBound) :
    ∀ J, weightedDerivativeSum κ p
        (normalizedDerivativeEnvelope (J := J) drift diffusion payoff T β x₀) ≤
      rhoBound ^ (p / intermediateExponent τ p) := by
  apply theorem4_1_from_rho_estimate
    (fun J : ℕ => Index J noiseDim)
    (fun J => normalizedDerivativeEnvelope (J := J)
      drift diffusion payoff T β x₀)
    κ p τ rhoBound hκ hτone hτ hp
  · intro J support
    exact normalizedDerivativeEnvelope_nonneg drift diffusion payoff T β x₀ support
      (hbounded J support)
  · exact hRhoBound

end

end TimeDependentLattice.Regularity
