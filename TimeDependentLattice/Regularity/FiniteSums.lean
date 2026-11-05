/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic
import TimeDependentLattice.Analysis.Finpartition

/-!
# Finite subset-product estimates

The elementary-symmetric estimate in this file is the combinatorial inequality used in
Lemma 4.4 and Lemma 4.5.  It is proved by comparing enumerations of subsets with all ordered
tuples, so its factorial is explicit rather than hidden in a library asymptotic.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open scoped BigOperators

/-- A cardinality-`n` subset of `s`, together with an enumeration by `Fin n`. -/
abbrev EnumeratedSubset {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) :=
  Σ t : ↥(s.powersetCard n), Fin n ≃ ↥t.1

/-- Forget an enumerated subset and retain the resulting ordered tuple. -/
def EnumeratedSubset.toFunction {α : Type*} [DecidableEq α]
    {s : Finset α} {n : ℕ} (q : EnumeratedSubset s n) : Fin n → ↥s :=
  fun i => ⟨(q.2 i).1, (Finset.mem_powersetCard.mp q.1.2).1 (q.2 i).2⟩

/-- An ordered tuple uniquely determines the subset it enumerates and the enumeration. -/
theorem EnumeratedSubset.toFunction_injective {α : Type*} [DecidableEq α]
    {s : Finset α} {n : ℕ} :
    Function.Injective (EnumeratedSubset.toFunction (s := s) (n := n)) := by
  rintro ⟨left, leftEnum⟩ ⟨right, rightEnum⟩ heq
  have hsets : left.1 = right.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := leftEnum.surjective ⟨x, hx⟩
      have hxval : x = (EnumeratedSubset.toFunction ⟨left, leftEnum⟩ i).1 := by
        simpa [EnumeratedSubset.toFunction] using congrArg Subtype.val hi.symm
      rw [hxval, heq]
      exact (rightEnum i).2
    · intro hx
      obtain ⟨i, hi⟩ := rightEnum.surjective ⟨x, hx⟩
      have hxval : x = (EnumeratedSubset.toFunction ⟨right, rightEnum⟩ i).1 := by
        simpa [EnumeratedSubset.toFunction] using congrArg Subtype.val hi.symm
      rw [hxval, ← heq]
      exact (leftEnum i).2
  have hsubtype : left = right := Subtype.ext hsets
  subst right
  have henum : leftEnum = rightEnum := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    simpa [EnumeratedSubset.toFunction] using
      congrArg Subtype.val (congrFun heq i)
  subst rightEnum
  rfl

/-- Product along an enumeration equals the product over the underlying subset. -/
theorem EnumeratedSubset.prod_toFunction {α : Type*} [DecidableEq α]
    {s : Finset α} {n : ℕ} (f : α → ℝ) (q : EnumeratedSubset s n) :
    (∏ i : Fin n, f (q.toFunction i).1) = ∏ x ∈ q.1.1, f x := by
  calc
    (∏ i : Fin n, f (q.toFunction i).1) =
        ∏ x : ↥q.1.1, f x.1 :=
      Fintype.prod_equiv q.2 (fun i => f (q.toFunction i).1)
        (fun x : ↥q.1.1 => f x.1) (fun i => rfl)
    _ = ∏ x ∈ q.1.1, f x := by
      have huniv : (Finset.univ : Finset ↥q.1.1) = q.1.1.attach := by
        ext x
        simp
      rw [huniv, Finset.prod_attach]

/-- The elementary-symmetric inequality
`n! e_n(a) ≤ (Σ a)^n` for a finite family of nonnegative real numbers. -/
theorem factorial_mul_sum_powersetCard_prod_le_sum_pow
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (n : ℕ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    (n.factorial : ℝ) * (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) ≤
      (∑ x ∈ s, f x) ^ n := by
  let source := EnumeratedSubset s n
  let tupleWeight : (Fin n → ↥s) → ℝ := fun p => ∏ i, f (p i).1
  let sourceWeight : source → ℝ := fun q => tupleWeight q.toFunction
  let embedding : source ↪ (Fin n → ↥s) :=
    ⟨EnumeratedSubset.toFunction, EnumeratedSubset.toFunction_injective⟩
  letI : Fintype source := inferInstanceAs (Fintype (EnumeratedSubset s n))
  have hsource :
      (∑ q : source, sourceWeight q) =
        (n.factorial : ℝ) * (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) := by
    change (∑ q : Σ t : ↥(s.powersetCard n), Fin n ≃ ↥t.1,
      (∏ i : Fin n, f ((q.2 i).1))) = _
    rw [Fintype.sum_sigma
      (fun q : Σ t : ↥(s.powersetCard n), Fin n ≃ ↥t.1 =>
        ∏ i : Fin n, f ((q.2 i).1))]
    have hprod (t : ↥(s.powersetCard n)) (e : Fin n ≃ ↥t.1) :
        (∏ i : Fin n, f ((e i).1)) = ∏ x ∈ t.1, f x := by
      simpa [EnumeratedSubset.toFunction] using
        EnumeratedSubset.prod_toFunction f
          (show EnumeratedSubset s n from ⟨t, e⟩)
    simp_rw [hprod]
    change (∑ t ∈ (Finset.univ : Finset ↥(s.powersetCard n)),
        ∑ _e : Fin n ≃ ↥t.1, ∏ x ∈ t.1, f x) = _
    have huniv : (Finset.univ : Finset ↥(s.powersetCard n)) =
        (s.powersetCard n).attach := by
      ext t
      simp
    rw [huniv, Finset.mul_sum]
    calc
      (∑ t ∈ (s.powersetCard n).attach,
          ∑ _e : Fin n ≃ ↥t.1, ∏ x ∈ t.1, f x) =
          ∑ t ∈ (s.powersetCard n).attach,
            (n.factorial : ℝ) * ∏ x ∈ t.1, f x := by
        apply Finset.sum_congr rfl
        intro t ht
        have htcard : t.1.card = n :=
          (Finset.mem_powersetCard.mp t.2).2
        rw [show (∑ _e : Fin n ≃ ↥t.1, ∏ x ∈ t.1, f x) =
            (Fintype.card (Fin n ≃ ↥t.1) : ℝ) *
              ∏ x ∈ t.1, f x by simp]
        congr 1
        let e₀ : Fin n ≃ ↥t.1 := Fintype.equivOfCardEq (by simp [htcard])
        have hcard : Fintype.card (Fin n ≃ ↥t.1) = n.factorial := by
          rw [Fintype.card_equiv e₀, Fintype.card_fin]
        exact_mod_cast hcard
      _ = ∑ t ∈ s.powersetCard n,
          (n.factorial : ℝ) * ∏ x ∈ t, f x := by
        exact Finset.sum_attach (s.powersetCard n)
          (fun t => (n.factorial : ℝ) * ∏ x ∈ t, f x)
  have himage :
      (∑ q : source, sourceWeight q) =
        ∑ p ∈ Finset.univ.map embedding, tupleWeight p := by
    rw [Finset.sum_map]
    rfl
  have htupleNonneg : ∀ p ∈ (Finset.univ : Finset (Fin n → ↥s)),
      0 ≤ tupleWeight p := by
    intro p hp
    apply Finset.prod_nonneg
    intro i hi
    exact hf (p i).1 (p i).2
  rw [← hsource, himage]
  have hpow :
      (∑ x ∈ s, f x) ^ n = ∑ p : Fin n → ↥s, tupleWeight p := by
    rw [← Finset.sum_attach]
    simpa [tupleWeight] using Fintype.sum_pow (fun x : ↥s => f x.1) n
  rw [hpow]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p hp hnot => htupleNonneg p hp)

/-- Division form of the elementary-symmetric estimate. -/
theorem sum_powersetCard_prod_le_sum_pow_div_factorial
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (n : ℕ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) ≤
      (∑ x ∈ s, f x) ^ n / n.factorial := by
  rw [le_div_iff₀ (by exact_mod_cast Nat.factorial_pos n :
    (0 : ℝ) < n.factorial)]
  simpa [mul_comm] using
    factorial_mul_sum_powersetCard_prod_le_sum_pow s f n hf

/-- A partition with `n` blocks is in particular an `n`-element family of distinct nonempty
subsets.  Dropping the disjointness and covering requirements therefore bounds the partition
sum by the corresponding elementary-symmetric sum. -/
theorem sum_finpartition_card_prod_le_sum_pow_div_factorial
    {α : Type*} [Fintype α] [DecidableEq α]
    (u : Finset α) (f : Finset α → ℝ) (n : ℕ)
    (hf : ∀ block ∈ u.powerset.erase ∅, 0 ≤ f block) :
    (∑ partition : Finpartition u with partition.parts.card = n,
      ∏ block ∈ partition.parts, f block) ≤
      (∑ block ∈ u.powerset.erase ∅, f block) ^ n / n.factorial := by
  let Source := {partition : Finpartition u // partition.parts.card = n}
  let embed : Source → ↥((u.powerset.erase ∅).powersetCard n) := fun partition ↦ by
    refine ⟨partition.1.parts, Finset.mem_powersetCard.mpr ⟨?_, partition.2⟩⟩
    intro block hblock
    apply Finset.mem_erase.mpr
    exact ⟨(partition.1.nonempty_of_mem_parts hblock).ne_empty,
      Finset.mem_powerset.mpr (partition.1.subset hblock)⟩
  have hembed : Function.Injective embed := by
    intro left right heq
    apply Subtype.ext
    apply Finpartition.ext
    exact congrArg (fun family : ↥((u.powerset.erase ∅).powersetCard n) ↦ family.1) heq
  have hsource :
      (∑ partition : Finpartition u with partition.parts.card = n,
        ∏ block ∈ partition.parts, f block) =
        ∑ partition : Source, ∏ block ∈ partition.1.parts, f block := by
    exact Finset.sum_subtype _ (fun partition ↦ by simp) _
  calc
    (∑ partition : Finpartition u with partition.parts.card = n,
      ∏ block ∈ partition.parts, f block) =
        ∑ partition : Source, ∏ block ∈ partition.1.parts, f block := hsource
    _ = ∑ family ∈ Finset.image embed Finset.univ,
        ∏ block ∈ family.1, f block := by
      symm
      exact Finset.sum_image (Set.injOn_of_injective hembed)
    _ ≤ ∑ family : ↥((u.powerset.erase ∅).powersetCard n),
        ∏ block ∈ family.1, f block := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro family hfamily himage
      exact Finset.prod_nonneg fun block hblock ↦
        hf block ((Finset.mem_powersetCard.mp family.2).1 hblock)
    _ = ∑ family ∈ (u.powerset.erase ∅).powersetCard n,
        ∏ block ∈ family, f block := by
      symm
      exact Finset.sum_subtype _ (fun family ↦ by simp) _
    _ ≤ (∑ block ∈ u.powerset.erase ∅, f block) ^ n / n.factorial :=
      sum_powersetCard_prod_le_sum_pow_div_factorial
        (u.powerset.erase ∅) f n hf

end

end TimeDependentLattice.Regularity
