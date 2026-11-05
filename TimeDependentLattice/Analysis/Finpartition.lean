/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin

/-!
# Ordered and unordered finite partitions

Mathlib's `OrderedFinpartition n` is the canonical presentation used by its Faà di Bruno
formula: elements inside a block are increasing, and blocks are ordered by increasing maximum.
This file proves that this representation is equivalent to an ordinary `Finpartition` of
`Fin n`.  The equivalence lets later analytic proofs use Mathlib's chain rule and then return to
the unordered partitions used in the paper.
-/

namespace TimeDependentLattice.Analysis
noncomputable section
open Set

private def partMax {n : ℕ} {p : Finpartition (Finset.univ : Finset (Fin n))}
    (block : p.parts) : Fin n :=
  block.1.max' (p.nonempty_of_mem_parts block.2)

private theorem partMax_injective {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n))) :
    Function.Injective (partMax (p := p)) := by
  intro left right hmax
  apply Subtype.ext
  apply p.eq_of_mem_parts left.2 right.2
  · exact Finset.max'_mem left.1 (p.nonempty_of_mem_parts left.2)
  · have hr := Finset.max'_mem right.1 (p.nonempty_of_mem_parts right.2)
    change partMax right ∈ right.1 at hr
    rw [← hmax] at hr
    exact hr

private def partMaxLE {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    p.parts → p.parts → Prop := fun left right ↦ partMax left ≤ partMax right

private def partMaxLT {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    p.parts → p.parts → Prop := fun left right ↦ partMax left < partMax right

instance {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    IsTrans p.parts (partMaxLT p) := ⟨fun _ _ _ hab hbc ↦ hab.trans hbc⟩

instance {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    Std.Antisymm (partMaxLT p) :=
  ⟨fun _ _ hab hba ↦ False.elim (lt_asymm hab hba)⟩

instance {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    Std.Irrefl (partMaxLT p) := ⟨fun _ ↦ lt_irrefl _⟩

noncomputable instance {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    DecidableRel (partMaxLE p) := Classical.decRel _

instance {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    IsTrans p.parts (partMaxLE p) := ⟨fun _ _ _ hab hbc ↦ hab.trans hbc⟩

instance {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    Std.Antisymm (partMaxLE p) :=
  ⟨fun _ _ hab hba ↦ partMax_injective p (le_antisymm hab hba)⟩

instance {n : ℕ} (p : Finpartition (Finset.univ : Finset (Fin n))) :
    Std.Total (partMaxLE p) :=
  ⟨fun left right ↦ le_total (partMax left) (partMax right)⟩

private noncomputable def orderedParts {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n))) : List p.parts :=
  Finset.univ.sort (partMaxLE p)

private theorem orderedParts_length {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n))) :
    (orderedParts p).length = p.parts.card := by
  simp [orderedParts]

private theorem mem_orderedParts {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n))) (block : p.parts) :
    block ∈ orderedParts p := by
  simp [orderedParts]

private theorem orderedParts_pairwise_max_lt {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n))) :
    (orderedParts p).Pairwise (partMaxLT p) := by
  have hpair : (orderedParts p).Pairwise (partMaxLE p) := by
    exact Finset.pairwise_sort (Finset.univ : Finset p.parts) (partMaxLE p)
  have hle : ((orderedParts p).map partMax).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hpair
  have hnodup : ((orderedParts p).map partMax).Nodup := by
    exact (by simp [orderedParts] : (orderedParts p).Nodup).map (partMax_injective p)
  have hlt := hle.sortedLE.sortedLT_of_nodup hnodup
  change (orderedParts p).Pairwise (fun left right ↦ partMax left < partMax right)
  rw [← List.pairwise_map]
  exact hlt.pairwise

/-- Canonically order the blocks and the elements inside each block of an unordered partition. -/
noncomputable def finpartitionToOrderedFinpartition {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n))) : OrderedFinpartition n := by
  let blocks := orderedParts p
  exact
    { length := blocks.length
      partSize := fun i ↦ (blocks.get i).1.card
      partSize_pos := fun i ↦ Finset.card_pos.mpr
        (p.nonempty_of_mem_parts (blocks.get i).2)
      emb := fun i ↦ (blocks.get i).1.orderEmbOfFin rfl
      emb_strictMono := fun i ↦ ((blocks.get i).1.orderEmbOfFin rfl).strictMono
      parts_strictMono := by
        intro i j hij
        change
          (blocks.get i).1.orderEmbOfFin rfl
              ⟨(blocks.get i).1.card - 1,
                Nat.sub_lt (Finset.card_pos.mpr
                  (p.nonempty_of_mem_parts (blocks.get i).2)) Nat.zero_lt_one⟩ <
            (blocks.get j).1.orderEmbOfFin rfl
              ⟨(blocks.get j).1.card - 1,
                Nat.sub_lt (Finset.card_pos.mpr
                  (p.nonempty_of_mem_parts (blocks.get j).2)) Nat.zero_lt_one⟩
        rw [Finset.orderEmbOfFin_last rfl
          (Finset.card_pos.mpr (p.nonempty_of_mem_parts (blocks.get i).2))]
        rw [Finset.orderEmbOfFin_last rfl
          (Finset.card_pos.mpr (p.nonempty_of_mem_parts (blocks.get j).2))]
        exact List.pairwise_iff_get.mp (orderedParts_pairwise_max_lt p) i j hij
      disjoint := by
        intro i _ j _ hij
        change Disjoint (Set.range ((blocks.get i).1.orderEmbOfFin rfl))
          (Set.range ((blocks.get j).1.orderEmbOfFin rfl))
        rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin]
        have hblocks : blocks.Nodup := by
          dsimp only [blocks]
          simp [orderedParts]
        have hd := p.disjoint (blocks.get i).2 (blocks.get j).2
          (fun heq ↦ hij (hblocks.injective_get (Subtype.ext heq)))
        exact Finset.disjoint_coe.mpr (by simpa only [Function.onFun, id_eq] using hd)
      cover := by
        intro x
        obtain ⟨block, hblock, hx⟩ :=
          p.exists_mem (by simp : x ∈ (Finset.univ : Finset (Fin n)))
        let block' : p.parts := ⟨block, hblock⟩
        obtain ⟨i, hi⟩ := List.get_of_mem (mem_orderedParts p block')
        refine ⟨i, ?_⟩
        rw [Finset.range_orderEmbOfFin]
        have hget : (blocks.get i).1 = block := congrArg Subtype.val hi
        rw [hget]
        exact hx }

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section
open Set

/-- The unordered set underlying one block of a Mathlib ordered partition. -/
def orderedFinpartitionBlock {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) : Finset (Fin n) :=
  Finset.univ.image (c.emb i)

/-- Forget the canonical ordering carried by a Mathlib `OrderedFinpartition`. -/
noncomputable def orderedFinpartitionAsFinpartition {n : ℕ}
    (c : OrderedFinpartition n) :
    Finpartition (Finset.univ : Finset (Fin n)) := by
  let parts : Finset (Finset (Fin n)) := Finset.univ.image (orderedFinpartitionBlock c)
  apply Finpartition.ofExistsUnique parts
  · intro block hblock
    simp only [parts, Finset.mem_image] at hblock
    obtain ⟨i, -, rfl⟩ := hblock
    intro j hj
    simp only [orderedFinpartitionBlock, Finset.mem_image] at hj
    obtain ⟨k, _, rfl⟩ := hj
    exact Finset.mem_univ _
  · intro j _
    obtain ⟨point, hpoint⟩ := c.exists_inverse j
    refine ⟨orderedFinpartitionBlock c point.1, ?_, ?_⟩
    · constructor
      · exact Finset.mem_image.mpr ⟨point.1, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨point.2, Finset.mem_univ _, hpoint⟩
    · intro other hother
      obtain ⟨hparts, hjother⟩ := hother
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hparts
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hjother
      have hemb : c.emb i k = c.emb point.1 point.2 := hk.trans hpoint.symm
      have hsigma : (⟨i, k⟩ : Σ m, Fin (c.partSize m)) = ⟨point.1, point.2⟩ :=
        c.emb_injective hemb
      exact congrArg (fun q ↦ orderedFinpartitionBlock c q.1) hsigma
  · intro hempty
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hempty
    let k : Fin (c.partSize i) := ⟨0, c.partSize_pos i⟩
    have hmem : c.emb i k ∈ orderedFinpartitionBlock c i :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    exact (Finset.nonempty_iff_ne_empty.mp ⟨_, hmem⟩) hi

@[simp]
theorem orderedFinpartitionAsFinpartition_parts {n : ℕ}
    (c : OrderedFinpartition n) :
    (orderedFinpartitionAsFinpartition c).parts =
      Finset.univ.image (orderedFinpartitionBlock c) := by
  simp [orderedFinpartitionAsFinpartition]

private theorem orderedPart_card {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) : (orderedFinpartitionBlock c i).card = c.partSize i := by
  unfold orderedFinpartitionBlock
  rw [Finset.card_image_of_injective _ (c.emb_strictMono i).injective]
  simp

private theorem orderedPart_nonempty {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) : (orderedFinpartitionBlock c i).Nonempty := by
  let k : Fin (c.partSize i) := ⟨0, c.partSize_pos i⟩
  exact ⟨c.emb i k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩

private theorem emb_eq_orderEmb_orderedPart {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) :
    c.emb i = (orderedFinpartitionBlock c i).orderEmbOfFin (orderedPart_card c i) := by
  apply (c.emb_strictMono i).eq_of_range_eq
    ((orderedFinpartitionBlock c i).orderEmbOfFin (orderedPart_card c i)).strictMono
  rw [Finset.range_orderEmbOfFin]
  ext x
  simp [orderedFinpartitionBlock]

private theorem orderedPart_max {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) :
    (orderedFinpartitionBlock c i).max' (orderedPart_nonempty c i) =
      c.emb i ⟨c.partSize i - 1,
        Nat.sub_lt (c.partSize_pos i) Nat.zero_lt_one⟩ := by
  rw [emb_eq_orderEmb_orderedPart c i]
  exact (Finset.orderEmbOfFin_last (orderedPart_card c i)
    (c.partSize_pos i)).symm

private theorem orderedPart_injective {n : ℕ} (c : OrderedFinpartition n) :
    Function.Injective (orderedFinpartitionBlock c) := by
  intro left right heq
  let k : Fin (c.partSize left) := ⟨0, c.partSize_pos left⟩
  have hk : c.emb left k ∈ orderedFinpartitionBlock c left :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  rw [heq, orderedFinpartitionBlock, Finset.mem_image] at hk
  obtain ⟨l, -, hl⟩ := hk
  have hsigma : (⟨left, k⟩ : Σ i, Fin (c.partSize i)) = ⟨right, l⟩ :=
    c.emb_injective hl.symm
  exact congrArg Sigma.fst hsigma

private theorem orderedPart_mem_parts {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) :
    orderedFinpartitionBlock c i ∈ (orderedFinpartitionAsFinpartition c).parts := by
  rw [orderedFinpartitionAsFinpartition_parts]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private noncomputable def originalParts {n : ℕ} (c : OrderedFinpartition n) :
    List (orderedFinpartitionAsFinpartition c).parts :=
  List.ofFn fun i ↦ ⟨orderedFinpartitionBlock c i, orderedPart_mem_parts c i⟩

private theorem mem_originalParts {n : ℕ} (c : OrderedFinpartition n)
    (block : (orderedFinpartitionAsFinpartition c).parts) :
    block ∈ originalParts c := by
  rw [originalParts, List.mem_ofFn]
  have hmem : block.1 ∈ Finset.univ.image (orderedFinpartitionBlock c) := by
    simpa only [orderedFinpartitionAsFinpartition_parts] using block.2
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨i, Subtype.ext ?_⟩
  exact hi

private theorem originalParts_pairwise_max_lt {n : ℕ} (c : OrderedFinpartition n) :
    (originalParts c).Pairwise
      (partMaxLT (orderedFinpartitionAsFinpartition c)) := by
  unfold originalParts
  rw [List.pairwise_iff_get]
  intro i j hij
  unfold partMaxLT partMax
  simp only [List.get_ofFn]
  rw [orderedPart_max, orderedPart_max]
  apply c.parts_strictMono
  simpa using hij

private theorem orderedParts_asFinpartition {n : ℕ} (c : OrderedFinpartition n) :
    orderedParts (orderedFinpartitionAsFinpartition c) = originalParts c := by
  apply List.Pairwise.eq_of_mem_iff
    (orderedParts_pairwise_max_lt (orderedFinpartitionAsFinpartition c))
    (originalParts_pairwise_max_lt c)
  intro block
  simp only [mem_orderedParts, mem_originalParts]

private theorem orderedParts_get_asFinpartition {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin (orderedParts (orderedFinpartitionAsFinpartition c)).length) :
    ((orderedParts (orderedFinpartitionAsFinpartition c)).get i).1 =
      orderedFinpartitionBlock c (Fin.cast (by
        rw [orderedParts_asFinpartition]
        simp [originalParts]) i) := by
  let p := orderedFinpartitionAsFinpartition c
  have hblocks : orderedParts p = originalParts c := orderedParts_asFinpartition c
  have hiOrig : i.val < (originalParts c).length := by
    rw [← hblocks]
    exact i.isLt
  have hget := congrArg (fun l : List p.parts ↦ l[i.val]?) hblocks
  rw [List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem hiOrig] at hget
  have hget' : (orderedParts p)[i.val] =
      (originalParts c)[i.val] := Option.some.inj hget
  have hget'' : (orderedParts p).get i =
      (originalParts c).get ⟨i.val, hiOrig⟩ := hget'
  change ((orderedParts p).get i).1 = _
  rw [congrArg Subtype.val hget'']
  simp only [originalParts, List.get_ofFn]
  congr 1

private theorem orderedPart_finpartitionToOrdered {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n)))
    (i : Fin (orderedParts p).length) :
    orderedFinpartitionBlock (finpartitionToOrderedFinpartition p)
        (Fin.cast (by simp [finpartitionToOrderedFinpartition]) i) =
      (orderedParts p).get i := by
  unfold orderedFinpartitionBlock finpartitionToOrderedFinpartition
  rw [Finset.image_orderEmbOfFin_univ]
  congr 1

/-- Forgetting the canonical order after adding it recovers the unordered partition. -/
theorem orderedFinpartitionAsFinpartition_finpartitionToOrdered {n : ℕ}
    (p : Finpartition (Finset.univ : Finset (Fin n))) :
    orderedFinpartitionAsFinpartition (finpartitionToOrderedFinpartition p) = p := by
  apply Finpartition.ext
  ext block
  simp only [orderedFinpartitionAsFinpartition_parts, Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    let j : Fin (orderedParts p).length := Fin.cast (by
      simp [finpartitionToOrderedFinpartition]) i
    rw [show i = Fin.cast (by simp [finpartitionToOrderedFinpartition]) j by
      apply Fin.ext
      rfl]
    rw [orderedPart_finpartitionToOrdered]
    exact ((orderedParts p).get j).property
  · intro hblock
    let block' : p.parts := ⟨block, hblock⟩
    obtain ⟨i, hi⟩ := List.get_of_mem (mem_orderedParts p block')
    refine ⟨Fin.cast (by simp [finpartitionToOrderedFinpartition]) i,
      Finset.mem_univ _, ?_⟩
    rw [orderedPart_finpartitionToOrdered]
    exact congrArg Subtype.val hi

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- Canonically ordering the forgotten blocks recovers the ordered partition. -/
theorem finpartitionToOrderedFinpartition_orderedFinpartitionAsFinpartition
    {n : ℕ} (c : OrderedFinpartition n) :
    finpartitionToOrderedFinpartition (orderedFinpartitionAsFinpartition c) = c := by
  let p := orderedFinpartitionAsFinpartition c
  have hblocks : orderedParts p = originalParts c := orderedParts_asFinpartition c
  have hlen : (finpartitionToOrderedFinpartition p).length = c.length := by
    change (orderedParts p).length = c.length
    rw [hblocks]
    simp [originalParts]
  have hpartSize : (finpartitionToOrderedFinpartition p).partSize ≍ c.partSize := by
    refine (Fin.heq_fun_iff hlen).mpr ?_
    intro i
    let ib : Fin (orderedParts p).length := Fin.cast (by
      rfl) i
    let ic : Fin c.length := ⟨i.val, hlen ▸ i.isLt⟩
    change ((orderedParts p).get ib).1.card = c.partSize ic
    have hiOrig : ib.val < (originalParts c).length := by
      rw [← hblocks]
      exact ib.isLt
    have hget := congrArg (fun l : List p.parts ↦ l[ib.val]?) hblocks
    simp only [List.getElem?_eq_getElem, ib.isLt, hiOrig] at hget
    have hget' := Option.some.inj hget
    have hget'' : (orderedParts p).get ib =
        (originalParts c).get ⟨ib.val, hiOrig⟩ := hget'
    rw [hget'']
    simp only [originalParts, List.get_ofFn]
    rw [orderedPart_card]
    congr 1
  apply OrderedFinpartition.ext hlen hpartSize
  refine Function.hfunext (congrArg Fin hlen) ?_
  intro i ic hic
  let ic' : Fin c.length := ⟨i.val, hlen ▸ i.isLt⟩
  have hic' : ic = ic' := by
    apply Fin.ext
    exact (Fin.val_eq_val_of_heq hic).symm
  subst ic
  have hsize : (finpartitionToOrderedFinpartition p).partSize i = c.partSize ic' :=
    (Fin.heq_fun_iff hlen).mp hpartSize i
  refine (Fin.heq_fun_iff hsize).mpr ?_
  intro k
  let ib : Fin (orderedParts p).length := Fin.cast (by rfl) i
  change ((orderedParts p).get ib).1.orderEmbOfFin rfl k = _
  have hblock : ((orderedParts p).get ib).1 = orderedFinpartitionBlock c ic' := by
    have h := orderedParts_get_asFinpartition c ib
    exact h.trans (congrArg (orderedFinpartitionBlock c) (Fin.ext rfl))
  let left : Fin (c.partSize ic') → Fin n := fun q ↦
    (finpartitionToOrderedFinpartition p).emb i (Fin.cast hsize.symm q)
  have hleftStrict : StrictMono left :=
    (finpartitionToOrderedFinpartition p).emb_strictMono i |>.comp
      (Fin.castOrderIso hsize.symm).strictMono
  have hleftRange : Set.range left =
      Set.range ((finpartitionToOrderedFinpartition p).emb i) := by
    exact (Fin.castOrderIso hsize.symm).surjective.range_comp _
  have hinverseRange :
      Set.range ((finpartitionToOrderedFinpartition p).emb i) =
        (↑((orderedParts p).get ib).1 : Set (Fin n)) := by
    change Set.range (((orderedParts p).get ib).1.orderEmbOfFin rfl) = _
    exact Finset.range_orderEmbOfFin _ _
  have hcRange : Set.range (c.emb ic') = (↑(orderedFinpartitionBlock c ic') : Set (Fin n)) := by
    ext x
    simp [orderedFinpartitionBlock]
  have hrange : Set.range left = Set.range (c.emb ic') := by
    rw [hleftRange, hinverseRange, hblock, hcRange]
  have hemb := hleftStrict.eq_of_range_eq (c.emb_strictMono ic') hrange
  have happly := congrFun hemb (Fin.cast hsize k)
  change (finpartitionToOrderedFinpartition p).emb i k =
    c.emb ic' (Fin.cast hsize k)
  simpa [left] using happly

/-- Mathlib's canonically ordered partitions are equivalent to ordinary finite partitions. -/
noncomputable def orderedFinpartitionEquivFinpartition (n : ℕ) :
    OrderedFinpartition n ≃
      Finpartition (Finset.univ : Finset (Fin n)) where
  toFun := orderedFinpartitionAsFinpartition
  invFun := finpartitionToOrderedFinpartition
  left_inv := finpartitionToOrderedFinpartition_orderedFinpartitionAsFinpartition
  right_inv := orderedFinpartitionAsFinpartition_finpartitionToOrdered

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- Send a coordinate block in `u` to its ranks in the canonical enumeration of `u`. -/
def rankFinsetBlock {α : Type*} [DecidableEq α] (u block : Finset α)
    (hblock : block ⊆ u) : Finset (Fin u.card) :=
  block.attach.image fun j ↦ u.equivFin ⟨j.1, hblock j.2⟩

/-- Pull a block of coordinate ranks back to the corresponding elements of `u`. -/
def unrankFinsetBlock {α : Type*} [DecidableEq α] (u : Finset α)
    (block : Finset (Fin u.card)) : Finset α :=
  block.image fun j ↦ (u.equivFin.symm j).1

/-- Pulling a ranked coordinate block back recovers the original block. -/
theorem unrankFinsetBlock_rankFinsetBlock {α : Type*} [DecidableEq α]
    (u block : Finset α) (hblock : block ⊆ u) :
    unrankFinsetBlock u (rankFinsetBlock u block hblock) = block := by
  ext x
  simp [unrankFinsetBlock, rankFinsetBlock]

/-- Ranking a block pulled back from `Fin u.card` recovers the ranked block. -/
theorem rankFinsetBlock_unrankFinsetBlock {α : Type*} [DecidableEq α]
    (u : Finset α) (block : Finset (Fin u.card))
    (hblock : unrankFinsetBlock u block ⊆ u) :
    rankFinsetBlock u (unrankFinsetBlock u block) hblock = block := by
  ext k
  simp [unrankFinsetBlock, rankFinsetBlock]

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- Transport a partition of `u` to a partition of the coordinate ranks `Fin u.card`. -/
noncomputable def finpartitionToRank {α : Type*} [DecidableEq α]
    {u : Finset α} (p : Finpartition u) :
    Finpartition (Finset.univ : Finset (Fin u.card)) := by
  let parts : Finset (Finset (Fin u.card)) :=
    p.parts.attach.image fun block ↦ rankFinsetBlock u block.1 (p.subset block.2)
  apply Finpartition.ofExistsUnique parts
  · intro block _
    exact Finset.subset_univ block
  · intro k _
    let x : u := u.equivFin.symm k
    obtain ⟨block, hblock, hx⟩ := p.exists_mem x.2
    refine ⟨rankFinsetBlock u block (p.subset hblock), ?_, ?_⟩
    · constructor
      · exact Finset.mem_image.mpr ⟨⟨block, hblock⟩, Finset.mem_attach _ _, rfl⟩
      · simp [rankFinsetBlock]
        exact ⟨x.1, hx, by simp [x]⟩
    · intro other hother
      obtain ⟨hparts, hk⟩ := hother
      obtain ⟨otherBlock, _, hotherBlock⟩ := Finset.mem_image.mp hparts
      apply hotherBlock.symm.trans
      congr 1
      have hxOther : x.1 ∈ otherBlock.1 := by
        rw [← hotherBlock] at hk
        rw [rankFinsetBlock, Finset.mem_image] at hk
        obtain ⟨j, hj, hjk⟩ := hk
        have heq : (⟨j.1, p.subset otherBlock.2 j.2⟩ : u) = x := by
          apply u.equivFin.injective
          exact hjk.trans (u.equivFin.apply_symm_apply k).symm
        exact congrArg Subtype.val heq ▸ j.2
      exact (p.eq_of_mem_parts hblock otherBlock.2 hx hxOther).symm
  · intro hempty
    obtain ⟨block, _, hblock⟩ := Finset.mem_image.mp hempty
    have hnonempty := p.nonempty_of_mem_parts block.2
    obtain ⟨x, hx⟩ := hnonempty
    have : u.equivFin ⟨x, p.subset block.2 hx⟩ ∈
        rankFinsetBlock u block.1 (p.subset block.2) := by
      simp [rankFinsetBlock]
      exact hx
    exact (Finset.nonempty_iff_ne_empty.mp ⟨_, this⟩) hblock

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- Pull a partition of `Fin u.card` back to a partition of the coordinate set `u`. -/
noncomputable def rankToFinpartition {α : Type*} [DecidableEq α]
    (u : Finset α) (q : Finpartition (Finset.univ : Finset (Fin u.card))) :
    Finpartition u := by
  let parts : Finset (Finset α) :=
    q.parts.attach.image fun block ↦ unrankFinsetBlock u block.1
  apply Finpartition.ofExistsUnique parts
  · intro block hblock
    obtain ⟨ranked, _, hranked⟩ := Finset.mem_image.mp hblock
    rw [← hranked]
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact (u.equivFin.symm k).2
  · intro x hx
    let k : Fin u.card := u.equivFin ⟨x, hx⟩
    obtain ⟨block, hblock, hk⟩ := q.exists_mem (Finset.mem_univ k)
    refine ⟨unrankFinsetBlock u block, ?_, ?_⟩
    · constructor
      · exact Finset.mem_image.mpr ⟨⟨block, hblock⟩, Finset.mem_attach _ _, rfl⟩
      · simp [unrankFinsetBlock]
        exact ⟨k, hk, by simp [k]⟩
    · intro other hother
      obtain ⟨hparts, hxOther⟩ := hother
      obtain ⟨otherBlock, _, hotherBlock⟩ := Finset.mem_image.mp hparts
      apply hotherBlock.symm.trans
      congr 1
      have hkOther : k ∈ otherBlock.1 := by
        rw [← hotherBlock] at hxOther
        rw [unrankFinsetBlock, Finset.mem_image] at hxOther
        obtain ⟨l, hl, hlx⟩ := hxOther
        have heq : l = k := by
          apply u.equivFin.symm.injective
          apply Subtype.ext
          rw [hlx]
          simp [k]
        exact heq ▸ hl
      exact (q.eq_of_mem_parts hblock otherBlock.2 hk hkOther).symm
  · intro hempty
    obtain ⟨block, _, hblock⟩ := Finset.mem_image.mp hempty
    obtain ⟨k, hk⟩ := q.nonempty_of_mem_parts block.2
    have : (u.equivFin.symm k).1 ∈ unrankFinsetBlock u block.1 := by
      simp [unrankFinsetBlock]
      exact hk
    exact (Finset.nonempty_iff_ne_empty.mp ⟨_, this⟩) hblock

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- The blocks of a partition transported to coordinate ranks. -/
@[simp]
theorem finpartitionToRank_parts {α : Type*} [DecidableEq α]
    {u : Finset α} (p : Finpartition u) :
    (finpartitionToRank p).parts = p.parts.attach.image
      (fun block ↦ rankFinsetBlock u block.1 (p.subset block.2)) := by
  simp [finpartitionToRank]

/-- The blocks of a ranked partition pulled back to the coordinate set. -/
@[simp]
theorem rankToFinpartition_parts {α : Type*} [DecidableEq α]
    (u : Finset α) (q : Finpartition (Finset.univ : Finset (Fin u.card))) :
    (rankToFinpartition u q).parts = q.parts.attach.image
      (fun block ↦ unrankFinsetBlock u block.1) := by
  simp [rankToFinpartition]

/-- Pulling back after ranking recovers a partition of the coordinate set. -/
theorem rankToFinpartition_finpartitionToRank {α : Type*} [DecidableEq α]
    {u : Finset α} (p : Finpartition u) :
    rankToFinpartition u (finpartitionToRank p) = p := by
  apply Finpartition.ext
  ext block
  rw [rankToFinpartition_parts]
  constructor
  · intro hblock
    obtain ⟨ranked, _, hrankedBlock⟩ := Finset.mem_image.mp hblock
    have hranked : ranked.1 ∈ p.parts.attach.image
        (fun original ↦ rankFinsetBlock u original.1 (p.subset original.2)) := by
      simpa only [finpartitionToRank_parts] using ranked.2
    obtain ⟨original, _, horiginal⟩ := Finset.mem_image.mp hranked
    have hEq : block = original.1 := by
      calc
        block = unrankFinsetBlock u ranked.1 := hrankedBlock.symm
        _ = unrankFinsetBlock u
            (rankFinsetBlock u original.1 (p.subset original.2)) := by rw [horiginal]
        _ = original.1 := unrankFinsetBlock_rankFinsetBlock u original.1 (p.subset original.2)
    rw [hEq]
    exact original.2
  · intro hblock
    let ranked := rankFinsetBlock u block (p.subset hblock)
    have hranked : ranked ∈ (finpartitionToRank p).parts := by
      rw [finpartitionToRank_parts]
      exact Finset.mem_image.mpr ⟨⟨block, hblock⟩, Finset.mem_attach _ _, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨ranked, hranked⟩, Finset.mem_attach _ _, ?_⟩
    exact unrankFinsetBlock_rankFinsetBlock u block (p.subset hblock)

/-- Ranking after pulling back recovers a partition of the rank set. -/
theorem finpartitionToRank_rankToFinpartition {α : Type*} [DecidableEq α]
    (u : Finset α) (q : Finpartition (Finset.univ : Finset (Fin u.card))) :
    finpartitionToRank (rankToFinpartition u q) = q := by
  apply Finpartition.ext
  ext block
  rw [finpartitionToRank_parts]
  constructor
  · intro hblock
    obtain ⟨unranked, _, hunrankedBlock⟩ := Finset.mem_image.mp hblock
    have hunranked : unranked.1 ∈ q.parts.attach.image
        (fun ranked ↦ unrankFinsetBlock u ranked.1) := by
      simpa only [rankToFinpartition_parts] using unranked.2
    obtain ⟨ranked, _, hranked⟩ := Finset.mem_image.mp hunranked
    have hmem : unrankFinsetBlock u ranked.1 ∈ (rankToFinpartition u q).parts := by
      rw [rankToFinpartition_parts]
      exact Finset.mem_image.mpr
        ⟨⟨ranked.1, ranked.2⟩, Finset.mem_attach _ _, rfl⟩
    have hsubset := (rankToFinpartition u q).subset hmem
    have hEq : block = ranked.1 := by
      calc
        block = rankFinsetBlock u unranked.1
            ((rankToFinpartition u q).subset unranked.2) := hunrankedBlock.symm
        _ = rankFinsetBlock u (unrankFinsetBlock u ranked.1)
            hsubset := by
              congr
              exact hranked.symm
        _ = ranked.1 := rankFinsetBlock_unrankFinsetBlock u ranked.1
          hsubset
    rw [hEq]
    exact ranked.2
  · intro hblock
    let unranked := unrankFinsetBlock u block
    have hunranked : unranked ∈ (rankToFinpartition u q).parts := by
      rw [rankToFinpartition_parts]
      exact Finset.mem_image.mpr ⟨⟨block, hblock⟩, Finset.mem_attach _ _, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨unranked, hunranked⟩, Finset.mem_attach _ _, ?_⟩
    exact rankFinsetBlock_unrankFinsetBlock u block
      ((rankToFinpartition u q).subset hunranked)

/-- Partitions of a finite coordinate set are equivalent to partitions of its canonical ranks. -/
noncomputable def finpartitionRankEquiv {α : Type*} [DecidableEq α]
    (u : Finset α) :
    Finpartition u ≃ Finpartition (Finset.univ : Finset (Fin u.card)) where
  toFun := finpartitionToRank
  invFun := rankToFinpartition u
  left_inv := rankToFinpartition_finpartitionToRank
  right_inv := finpartitionToRank_rankToFinpartition u

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- The unique coordinate in a partition block whose cardinality is one. -/
noncomputable def finpartitionSingletonCoordinate {α : Type*} [DecidableEq α]
    {u : Finset α} {p : Finpartition u} (block : p.parts)
    (hcard : block.1.card = 1) : α :=
  Classical.choose (Finset.card_eq_one.mp hcard)

/-- A block of cardinality one is the singleton containing its selected coordinate. -/
theorem finpartitionBlock_eq_singleton {α : Type*} [DecidableEq α]
    {u : Finset α} {p : Finpartition u} (block : p.parts)
    (hcard : block.1.card = 1) :
    block.1 = {finpartitionSingletonCoordinate block hcard} :=
  Classical.choose_spec (Finset.card_eq_one.mp hcard)

/-- The selected coordinate belongs to its singleton partition block. -/
theorem finpartitionSingletonCoordinate_mem {α : Type*} [DecidableEq α]
    {u : Finset α} {p : Finpartition u} (block : p.parts)
    (hcard : block.1.card = 1) :
    finpartitionSingletonCoordinate block hcard ∈ block.1 := by
  rw [finpartitionBlock_eq_singleton block hcard]
  simp

end
end TimeDependentLattice.Analysis



namespace TimeDependentLattice.Analysis
noncomputable section

/-- Add every coordinate in `direct` as a singleton block to a partition of the complement. -/
noncomputable def finpartitionInsertSingletons {α : Type*} [DecidableEq α]
    {u direct : Finset α} (hdu : direct ⊆ u)
    (q : Finpartition (u \ direct)) : Finpartition u := by
  let parts := q.parts ∪ direct.image ({·})
  apply Finpartition.ofExistsUnique parts
  · intro block hblock
    rcases Finset.mem_union.mp hblock with hq | hs
    · exact fun x hx ↦ (Finset.mem_sdiff.mp (q.subset hq hx)).1
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
      simpa using hdu hx
  · intro x hx
    by_cases hxd : x ∈ direct
    · refine ⟨{x}, ?_, ?_⟩
      · exact ⟨Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨x, hxd, rfl⟩), by simp⟩
      · intro other hother
        rcases Finset.mem_union.mp hother.1 with hq | hs
        · exact False.elim ((Finset.mem_sdiff.mp (q.subset hq hother.2)).2 hxd)
        · obtain ⟨y, hy, hsingleton⟩ := Finset.mem_image.mp hs
          rw [← hsingleton] at hother
          have hxy : x = y := Finset.mem_singleton.mp hother.2
          subst y
          exact hsingleton.symm
    · have hxrem : x ∈ u \ direct := Finset.mem_sdiff.mpr ⟨hx, hxd⟩
      obtain ⟨block, hblock, hxblock⟩ := q.exists_mem hxrem
      refine ⟨block, ?_, ?_⟩
      · exact ⟨Finset.mem_union_left _ hblock, hxblock⟩
      · intro other hother
        rcases Finset.mem_union.mp hother.1 with hq | hs
        · exact q.eq_of_mem_parts hq hblock hother.2 hxblock
        · obtain ⟨y, hy, hsingleton⟩ := Finset.mem_image.mp hs
          rw [← hsingleton] at hother
          have hxy : x = y := Finset.mem_singleton.mp hother.2
          exact False.elim (hxd (hxy ▸ hy))
  · intro hempty
    rcases Finset.mem_union.mp hempty with hq | hs
    · exact q.empty_notMem_parts hq
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hs
      exact Finset.singleton_ne_empty x hx

/-- The inserted partition consists of the old blocks and the new singleton blocks. -/
@[simp]
theorem finpartitionInsertSingletons_parts {α : Type*} [DecidableEq α]
    {u direct : Finset α} (hdu : direct ⊆ u)
    (q : Finpartition (u \ direct)) :
    (finpartitionInsertSingletons hdu q).parts =
      q.parts ∪ direct.image ({·}) := by
  simp [finpartitionInsertSingletons]

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- Removing the inserted singleton coordinates recovers the original remaining partition. -/
theorem finpartitionInsertSingletons_avoid {α : Type*} [DecidableEq α]
    {u direct : Finset α} (hdu : direct ⊆ u)
    (q : Finpartition (u \ direct)) :
    (finpartitionInsertSingletons hdu q).avoid direct = q := by
  apply Finpartition.ext
  ext block
  rw [Finpartition.mem_avoid]
  rw [finpartitionInsertSingletons_parts]
  constructor
  · rintro ⟨source, hsource, hnsub, hdiff⟩
    rcases Finset.mem_union.mp hsource with hq | hs
    · have hdisjoint : Disjoint source direct := by
        rw [Finset.disjoint_left]
        intro x hx hxd
        exact (Finset.mem_sdiff.mp (q.subset hq hx)).2 hxd
      have hsame : source \ direct = source :=
        Finset.sdiff_eq_self_of_disjoint hdisjoint
      rw [hsame] at hdiff
      exact hdiff ▸ hq
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
      exact False.elim (hnsub (by simpa using hx))
  · intro hblock
    refine ⟨block, Finset.mem_union_left _ hblock, ?_, ?_⟩
    · intro hsubset
      obtain ⟨x, hx⟩ := q.nonempty_of_mem_parts hblock
      exact (Finset.mem_sdiff.mp (q.subset hblock hx)).2 (hsubset hx)
    · apply Finset.sdiff_eq_self_of_disjoint
      rw [Finset.disjoint_left]
      intro x hx hxd
      exact (Finset.mem_sdiff.mp (q.subset hblock hx)).2 hxd

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- Removing chosen singleton blocks and then reinserting them recovers the original partition. -/
theorem finpartitionInsertSingletons_avoid_of_singleton_parts
    {α : Type*} [DecidableEq α] {u direct : Finset α}
    (p : Finpartition u) (hdu : direct ⊆ u)
    (hsingle : ∀ x ∈ direct, ({x} : Finset α) ∈ p.parts) :
    finpartitionInsertSingletons hdu (p.avoid direct) = p := by
  apply Finpartition.ext
  ext block
  rw [finpartitionInsertSingletons_parts]
  constructor
  · intro hblock
    rcases Finset.mem_union.mp hblock with havoid | hsingleton
    · rw [Finpartition.mem_avoid] at havoid
      obtain ⟨source, hsource, hnsub, hdiff⟩ := havoid
      have hdisjoint : Disjoint source direct := by
        rw [Finset.disjoint_left]
        intro x hx hxd
        have heq : source = {x} :=
          p.eq_of_mem_parts hsource (hsingle x hxd) hx (by simp)
        exact hnsub (by simpa [heq] using hxd)
      have hsame : source \ direct = source :=
        Finset.sdiff_eq_self_of_disjoint hdisjoint
      rw [hsame] at hdiff
      exact hdiff ▸ hsource
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hsingleton
      exact hsingle x hx
  · intro hblock
    by_cases hsub : block ⊆ direct
    · obtain ⟨x, hx⟩ := p.nonempty_of_mem_parts hblock
      have hxd : x ∈ direct := hsub hx
      have heq : block = {x} :=
        p.eq_of_mem_parts hblock (hsingle x hxd) hx (by simp)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x, hxd, heq.symm⟩
    · apply Finset.mem_union_left
      rw [Finpartition.mem_avoid]
      refine ⟨block, hblock, hsub, ?_⟩
      apply Finset.sdiff_eq_self_of_disjoint
      rw [Finset.disjoint_left]
      intro x hx hxd
      have heq : block = {x} :=
        p.eq_of_mem_parts hblock (hsingle x hxd) hx (by simp)
      exact hsub (by simpa [heq] using hxd)

end
end TimeDependentLattice.Analysis

namespace TimeDependentLattice.Analysis
noncomputable section

/-- Inserting singleton coordinates adds exactly one partition block per coordinate. -/
theorem finpartitionInsertSingletons_card {α : Type*} [DecidableEq α]
    {u direct : Finset α} (hdu : direct ⊆ u)
    (q : Finpartition (u \ direct)) :
    (finpartitionInsertSingletons hdu q).parts.card =
      q.parts.card + direct.card := by
  rw [finpartitionInsertSingletons_parts]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective]
    exact fun left right heq ↦ Finset.singleton_inj.mp heq
  · rw [Finset.disjoint_left]
    intro block hq hs
    obtain ⟨x, hx, hsingleton⟩ := Finset.mem_image.mp hs
    have hxblock : x ∈ block := by
      rw [← hsingleton]
      simp
    exact (Finset.mem_sdiff.mp (q.subset hq hxblock)).2 hx

end
end TimeDependentLattice.Analysis

