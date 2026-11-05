/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import TimeDependentLattice.Trees.PlaneCounting

/-!
# Coefficient summation over a fixed tree family

This file is the numerical summation step in paper Lemma B.8.  The analytic estimate for one
tree is kept as an explicit hypothesis; the Catalan count from Lemma B.7 supplies the only
nontrivial family-counting input.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open TimeDependentLattice.BrownianBridge

/-- The local factorial split used at every vertex in paper Lemma B.8.  This is the
real-power version of
`(n + c)! \le 2^(n+c) n! c!`. -/
theorem factorial_add_rpow_le
    (n c : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ((n + c).factorial : ℝ) ^ τ ≤
      (((2 : ℝ) ^ (n + c)) * n.factorial * c.factorial) ^ τ := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hτ
  exact_mod_cast (show
    (n + c).factorial ≤ 2 ^ (n + c) * n.factorial * c.factorial by
      rw [← Nat.add_choose_mul_factorial_mul_factorial]
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_right (n.factorial * c.factorial)
          (Nat.choose_le_two_pow (n + c) c))

/-- Factorized form of `factorial_add_rpow_le`, with the `2^τ` contribution exposed as
one factor for each input of the vertex. -/
theorem factorial_add_rpow_le_split
    (n c : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ((n + c).factorial : ℝ) ^ τ ≤
      ((2 : ℝ) ^ τ) ^ (n + c) *
        (n.factorial : ℝ) ^ τ * (c.factorial : ℝ) ^ τ := by
  calc
    ((n + c).factorial : ℝ) ^ τ ≤
        (((2 : ℝ) ^ (n + c)) * n.factorial * c.factorial) ^ τ :=
      factorial_add_rpow_le n c τ hτ
    _ = (((2 : ℝ) ^ (n + c)) ^ τ) *
        (n.factorial : ℝ) ^ τ * (c.factorial : ℝ) ^ τ := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
    _ = _ := by
      congr 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), Real.rpow_natCast]

theorem finset_prod_rpow {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (τ : ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ τ = ∏ i ∈ s, (f i) ^ τ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Real.mul_rpow (hf a (by simp)) (Finset.prod_nonneg fun i hi ↦ hf i (by simp [hi])),
        ih (fun i hi ↦ hf i (by simp [hi]))]

/-- If `1 ≤ τ` and `0 < a ≤ b`, then `a^τ ≤ b^(τ-1) a`. -/
theorem rpow_le_rpow_sub_one_mul
    {a b τ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hτ : 1 ≤ τ) :
    a ^ τ ≤ b ^ (τ - 1) * a := by
  have hexponent : 0 ≤ τ - 1 := sub_nonneg.mpr hτ
  calc
    a ^ τ = a ^ ((τ - 1) + 1) := by ring_nf
    _ = a ^ (τ - 1) * a ^ (1 : ℝ) := Real.rpow_add ha (τ - 1) 1
    _ = a ^ (τ - 1) * a := by rw [Real.rpow_one]
    _ ≤ b ^ (τ - 1) * a :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow ha.le hab hexponent) ha.le

/-- The coefficient-sum part of paper Lemma B.8.  A per-tree estimate containing one factor
`Q(tree)` sums to the same estimate with `64^k k!`, and the extra factorial combines with
`(k!)^(τ-1)` to give `(k!)^τ`. -/
theorem coefficient_sum_le_of_tree_bound
    {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (support root : Finset (Index J noiseDim))
    (hvalid : ∀ tree ∈ family, tree.Valid support)
    (hroot : ∀ tree ∈ family, tree.direct = root)
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList)
    (hvertices : ∀ tree ∈ family,
      tree.vertexCount ≤ 2 * blocks.card)
    (coefficient : PayoffTreeData J noiseDim → ℝ)
    (C₀ rootFactor blockFactor τ : ℝ)
    (supportCard : ℕ)
    (hC₀ : 0 ≤ C₀) (hrootFactor : 0 ≤ rootFactor)
    (hblockFactor : 0 ≤ blockFactor)
    (hcoefficient : ∀ tree ∈ family,
      coefficient tree ≤
        C₀ ^ (supportCard + blocks.card) * rootFactor * blockFactor *
          (blocks.card.factorial : ℝ) ^ (τ - 1) *
            (tree.childFactorialProduct : ℝ)) :
    ∑ tree ∈ family, coefficient tree ≤
      C₀ ^ (supportCard + blocks.card) * rootFactor * blockFactor *
        (64 : ℝ) ^ blocks.card * (blocks.card.factorial : ℝ) ^ τ := by
  let common : ℝ :=
    C₀ ^ (supportCard + blocks.card) * rootFactor * blockFactor *
      (blocks.card.factorial : ℝ) ^ (τ - 1)
  have hcommon : 0 ≤ common := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hC₀ _) hrootFactor)
        hblockFactor)
      (Real.rpow_nonneg (by positivity) _)
  have hcountNat := weighted_payoffTree_count family blocks support root
    hvalid hroot hblocks hvertices
  have hcountReal :
      (∑ tree ∈ family, (tree.childFactorialProduct : ℝ)) ≤
        (64 : ℝ) ^ blocks.card * (blocks.card.factorial : ℝ) := by
    exact_mod_cast hcountNat
  calc
    ∑ tree ∈ family, coefficient tree ≤
        ∑ tree ∈ family, common * (tree.childFactorialProduct : ℝ) := by
      apply Finset.sum_le_sum
      intro tree htree
      simpa [common] using hcoefficient tree htree
    _ = common * ∑ tree ∈ family,
          (tree.childFactorialProduct : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ common * ((64 : ℝ) ^ blocks.card *
        (blocks.card.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hcountReal hcommon
    _ = C₀ ^ (supportCard + blocks.card) * rootFactor * blockFactor *
        (64 : ℝ) ^ blocks.card * (blocks.card.factorial : ℝ) ^ τ := by
      have hfactorial : (0 : ℝ) < blocks.card.factorial := by positivity
      have hfactorialPow :
          (blocks.card.factorial : ℝ) ^ (τ - 1) *
              (blocks.card.factorial : ℝ) =
            (blocks.card.factorial : ℝ) ^ τ := by
        calc
          _ = (blocks.card.factorial : ℝ) ^ (τ - 1) *
              (blocks.card.factorial : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (blocks.card.factorial : ℝ) ^ ((τ - 1) + 1) :=
            (Real.rpow_add hfactorial (τ - 1) 1).symm
          _ = _ := by
            congr 1
            ring
      change
        (C₀ ^ (supportCard + blocks.card) * rootFactor * blockFactor *
            (blocks.card.factorial : ℝ) ^ (τ - 1)) *
              ((64 : ℝ) ^ blocks.card * (blocks.card.factorial : ℝ)) = _
      calc
        _ = (C₀ ^ (supportCard + blocks.card) * rootFactor * blockFactor *
              (64 : ℝ) ^ blocks.card) *
              ((blocks.card.factorial : ℝ) ^ (τ - 1) *
                (blocks.card.factorial : ℝ)) := by ring
        _ = _ := by rw [hfactorialPow]

end

end TimeDependentLattice.Trees
