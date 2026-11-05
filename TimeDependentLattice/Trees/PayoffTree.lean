/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Data.List.Sort
import Mathlib.Order.Partition.Finpartition
import TimeDependentLattice.BrownianBridge.Index

/-!
# Labelled payoff trees

This file implements the combinatorial layers of the paper's labelled payoff trees.  Raw tree
data use lists for structural recursion.  `Valid` makes that list a canonical representative of
unordered children by sorting subtrees according to the least coordinate in their support.

Analytic values and time assignments deliberately live in later files.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open TimeDependentLattice.BrownianBridge

/-- A drift vertex, its direct coordinate labels, and its child drift trees. -/
inductive DriftTreeData (J noiseDim : ℕ) where
  | node (direct : Finset (Index J noiseDim))
      (children : List (DriftTreeData J noiseDim))

noncomputable instance (J noiseDim : ℕ) : DecidableEq (DriftTreeData J noiseDim) :=
  Classical.decEq _

/-- The payoff root has direct labels and a list of drift subtrees. -/
structure PayoffTreeData (J noiseDim : ℕ) where
  direct : Finset (Index J noiseDim)
  children : List (DriftTreeData J noiseDim)

noncomputable instance (J noiseDim : ℕ) : DecidableEq (PayoffTreeData J noiseDim) :=
  Classical.decEq _

/-- The direct labels at a drift vertex. -/
def DriftTreeData.direct {J noiseDim : ℕ} :
    DriftTreeData J noiseDim → Finset (Index J noiseDim)
  | .node direct _ => direct

/-- The direct child subtrees of a drift vertex. -/
def DriftTreeData.children {J noiseDim : ℕ} :
    DriftTreeData J noiseDim → List (DriftTreeData J noiseDim)
  | .node _ children => children

/-- All coordinate labels appearing in a drift subtree. -/
def DriftTreeData.support {J noiseDim : ℕ} :
    DriftTreeData J noiseDim → Finset (Index J noiseDim)
  | .node direct children =>
      direct ∪ children.foldr (fun child acc => child.support ∪ acc) ∅
termination_by tree => sizeOf tree

/-- The union of the coordinate supports of a list of child subtrees. -/
def childrenSupport {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim)) :
    Finset (Index J noiseDim) :=
  children.foldr (fun child acc => child.support ∪ acc) ∅

/-- The list of supports carried by the direct children of a vertex. -/
def childSupports {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim)) :
    List (Finset (Index J noiseDim)) :=
  children.map DriftTreeData.support

/-- The number of drift vertices in a drift subtree. -/
def DriftTreeData.vertexCount {J noiseDim : ℕ} : DriftTreeData J noiseDim → ℕ
  | .node _ children => 1 + (children.map vertexCount).sum
termination_by tree => sizeOf tree

/-- All coordinate labels appearing in a payoff tree. -/
def PayoffTreeData.support {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    Finset (Index J noiseDim) := tree.direct ∪ childrenSupport tree.children

/-- The total number of vertices, including the payoff root. -/
def PayoffTreeData.vertexCount {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) : ℕ :=
  1 + (tree.children.map DriftTreeData.vertexCount).sum

/-- A fixed injective rank used only to choose canonical sibling order. -/
noncomputable def coordinateRank {J noiseDim : ℕ} (j : Index J noiseDim) : ℕ :=
  (Fintype.equivFin (Index J noiseDim) j).val

theorem coordinateRank_injective {J noiseDim : ℕ} :
    Function.Injective (coordinateRank (J := J) (noiseDim := noiseDim)) :=
  Fin.val_injective.comp (Fintype.equivFin (Index J noiseDim)).injective

/-- The least coordinate rank in a subtree support; empty support is represented by `⊤`. -/
noncomputable def DriftTreeData.supportKey {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) : WithTop ℕ :=
  (tree.support.image coordinateRank).min

/-- Endpoint Brownian-bridge coordinates are precisely the left summand of `Index`. -/
def IsEndpoint {J noiseDim : ℕ} : Index J noiseDim → Prop
  | .inl _ => True
  | .inr _ => False

noncomputable instance {J noiseDim : ℕ} (j : Index J noiseDim) :
    Decidable (IsEndpoint j) := Classical.propDecidable _

/-- The two allowed local configurations at a drift vertex. -/
def locallyAdmissible (directCard childCount : ℕ) : Prop :=
  (directCard = 1 ∧ childCount = 0) ∨ 2 ≤ directCard + childCount

/-- Different children carry disjoint coordinate supports. -/
def childrenDisjoint {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim)) : Prop :=
  (children.map DriftTreeData.support).Pairwise Disjoint

/-- Children are listed in the canonical order induced by their least coordinate ranks. -/
def childrenCanonical {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim)) : Prop :=
  children.Pairwise fun left right => left.supportKey < right.supportKey

/-- Well-formedness of every drift vertex and its descendants. -/
def DriftTreeData.Valid {J noiseDim : ℕ} : DriftTreeData J noiseDim → Prop
  | .node direct children =>
      locallyAdmissible direct.card children.length ∧
      Disjoint direct (childrenSupport children) ∧
      childrenDisjoint children ∧
      childrenCanonical children ∧
      ∀ child ∈ children, child.Valid
termination_by tree => sizeOf tree

/-- A valid payoff tree on `u`: all labels are disjoint with union `u`, root labels are endpoint
coordinates, drift vertices obey the paper's local condition, and siblings are canonical. -/
def PayoffTreeData.Valid {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    (u : Finset (Index J noiseDim)) : Prop :=
  tree.support = u ∧
  (∀ j ∈ tree.direct, IsEndpoint j) ∧
  Disjoint tree.direct (childrenSupport tree.children) ∧
  childrenDisjoint tree.children ∧
  childrenCanonical tree.children ∧
  ∀ child ∈ tree.children, child.Valid

/-- A member of the paper's family `𝒯(u)` of labelled payoff trees.

The correspondence theorem separately assumes that `u` is nonempty.  Keeping that assumption out
of this structure allows the structural API to include the harmless empty root-only tree. -/
structure LabelledPayoffTree (J noiseDim : ℕ) (u : Finset (Index J noiseDim)) where
  data : PayoffTreeData J noiseDim
  valid : data.Valid u

namespace LabelledPayoffTree

@[ext]
theorem ext {J noiseDim : ℕ} {u : Finset (Index J noiseDim)}
    {left right : LabelledPayoffTree J noiseDim u} (hdata : left.data = right.data) :
    left = right := by
  cases left
  cases right
  simp_all

end LabelledPayoffTree

@[simp]
theorem DriftTreeData.support_node {J noiseDim : ℕ}
    (direct : Finset (Index J noiseDim)) (children : List (DriftTreeData J noiseDim)) :
    (DriftTreeData.node direct children).support = direct ∪ childrenSupport children := by
  simp [DriftTreeData.support, childrenSupport]

@[simp]
theorem childrenSupport_nil {J noiseDim : ℕ} :
    childrenSupport ([] : List (DriftTreeData J noiseDim)) = ∅ := by
  rfl

@[simp]
theorem childrenSupport_cons {J noiseDim : ℕ} (head : DriftTreeData J noiseDim)
    (tail : List (DriftTreeData J noiseDim)) :
    childrenSupport (head :: tail) = head.support ∪ childrenSupport tail := by
  rfl

@[simp]
theorem DriftTreeData.vertexCount_node {J noiseDim : ℕ}
    (direct : Finset (Index J noiseDim)) (children : List (DriftTreeData J noiseDim)) :
    (DriftTreeData.node direct children).vertexCount =
      1 + (children.map DriftTreeData.vertexCount).sum := by
  simp [DriftTreeData.vertexCount]

/-- Every singleton-labelled drift leaf satisfies the local tree rules. -/
theorem DriftTreeData.singletonLeaf_valid {J noiseDim : ℕ} (j : Index J noiseDim) :
    (DriftTreeData.node {j} []).Valid := by
  simp [DriftTreeData.Valid, locallyAdmissible, childrenDisjoint, childrenCanonical]

/-- The direct label of every valid drift leaf is nonempty. -/
theorem DriftTreeData.valid_leaf_direct_nonempty {J noiseDim : ℕ}
    (direct : Finset (Index J noiseDim))
    (hvalid : (DriftTreeData.node direct []).Valid) : direct.Nonempty := by
  simp only [DriftTreeData.Valid, locallyAdmissible, List.length_nil, Nat.add_zero] at hvalid
  rcases hvalid.1 with hsingleton | hhigher
  · exact Finset.card_pos.mp (by omega)
  · exact Finset.card_pos.mp (by omega)

/-- A root-only tree is valid whenever all of its labels are endpoint coordinates. -/
theorem PayoffTreeData.rootOnly_valid {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (hendpoint : ∀ j ∈ u, IsEndpoint j) :
    (PayoffTreeData.mk u []).Valid u := by
  refine ⟨?_, hendpoint, ?_, ?_, ?_, ?_⟩
  · simp [PayoffTreeData.support]
  · simp
  · simp [childrenDisjoint]
  · simp [childrenCanonical]
  · simp

/-- The root-only member of `𝒯(u)`, available exactly when every label is an endpoint
coordinate, as required by Definition `def:tree`. -/
def LabelledPayoffTree.rootOnly {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (hendpoint : ∀ j ∈ u, IsEndpoint j) :
    LabelledPayoffTree J noiseDim u :=
  ⟨PayoffTreeData.mk u [], PayoffTreeData.rootOnly_valid u hendpoint⟩

@[simp]
theorem LabelledPayoffTree.rootOnly_data {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (hendpoint : ∀ j ∈ u, IsEndpoint j) :
    (LabelledPayoffTree.rootOnly u hendpoint).data = PayoffTreeData.mk u [] :=
  rfl

/-- The support of a child is contained in the union of all sibling supports. -/
theorem DriftTreeData.support_subset_childrenSupport {J noiseDim : ℕ}
    {child : DriftTreeData J noiseDim} {children : List (DriftTreeData J noiseDim)}
    (hmem : child ∈ children) : child.support ⊆ childrenSupport children := by
  induction children with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [childrenSupport_cons]
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Finset.subset_union_left
      · exact (ih hmem).trans Finset.subset_union_right

theorem mem_childrenSupport_iff_exists {J noiseDim : ℕ}
    {j : Index J noiseDim} {children : List (DriftTreeData J noiseDim)} :
    j ∈ childrenSupport children ↔
      ∃ child ∈ children, j ∈ child.support := by
  induction children with
  | nil => simp
  | cons head tail ih =>
      rw [childrenSupport_cons, Finset.mem_union, ih]
      simp only [List.mem_cons]
      constructor
      · rintro (hj | ⟨child, hchild, hj⟩)
        · exact ⟨head, Or.inl rfl, hj⟩
        · exact ⟨child, Or.inr hchild, hj⟩
      · rintro ⟨child, rfl | hchild, hj⟩
        · exact Or.inl hj
        · exact Or.inr ⟨child, hchild, hj⟩

/-- Pairwise-disjoint child supports have additive cardinality. -/
theorem childrenSupport_card_eq_sum_support_card {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim))
    (hdisjoint : childrenDisjoint children) :
    (childrenSupport children).card =
      (children.map fun child ↦ child.support.card).sum := by
  induction children with
  | nil => simp
  | cons head tail ih =>
      change (head.support :: tail.map DriftTreeData.support).Pairwise Disjoint at hdisjoint
      rw [List.pairwise_cons] at hdisjoint
      have hheadTail : Disjoint head.support (childrenSupport tail) := by
        refine Finset.disjoint_left.mpr ?_
        intro j hjHead hjTail
        rcases mem_childrenSupport_iff_exists.mp hjTail with ⟨child, hchild, hjChild⟩
        have hchildDisjoint : Disjoint head.support child.support :=
          hdisjoint.1 child.support (List.mem_map.mpr ⟨child, hchild, rfl⟩)
        exact Finset.disjoint_left.mp hchildDisjoint hjHead hjChild
      rw [childrenSupport_cons, Finset.card_union_of_disjoint hheadTail, ih hdisjoint.2]
      simp

/-- Every valid drift subtree carries at least one coordinate.  This is the fact that later makes
the least-support-coordinate order meaningful and makes the tree-to-expansion inverse unique. -/
theorem DriftTreeData.valid_support_nonempty {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) : tree.support.Nonempty := by
  match tree with
  | .node direct children =>
      rw [DriftTreeData.support_node]
      by_cases hdirect : direct.Nonempty
      · exact hdirect.mono Finset.subset_union_left
      · have hdirectEmpty : direct = ∅ := Finset.not_nonempty_iff_eq_empty.mp hdirect
        simp only [DriftTreeData.Valid] at hvalid
        have hchildrenLength : 0 < children.length := by
          rcases hvalid.1 with hsingleton | hhigher
          · rw [hdirectEmpty] at hsingleton
            simp at hsingleton
          · rw [hdirectEmpty] at hhigher
            simp at hhigher
            omega
        obtain ⟨child, hmem⟩ := List.exists_mem_of_ne_nil children
          (List.ne_nil_of_length_pos hchildrenLength)
        have hchildValid : child.Valid := hvalid.2.2.2.2 child hmem
        have hchildNonempty := valid_support_nonempty child hchildValid
        exact hchildNonempty.mono
          ((support_subset_childrenSupport hmem).trans Finset.subset_union_right)

/-- At a valid drift vertex, the union of the child-subtree labels is exactly the subtree support
with the direct labels removed.  This is the set identity used to recover the local partition in
the inverse direction of Lemma `lem:correspondence`. -/
theorem DriftTreeData.valid_childrenSupport_eq_support_sdiff_direct {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    childrenSupport tree.children = tree.support \ tree.direct := by
  cases tree with
  | node direct children =>
      simp only [DriftTreeData.Valid] at hvalid
      change childrenSupport children =
        (DriftTreeData.node direct children).support \ direct
      rw [DriftTreeData.support_node]
      apply Finset.ext
      intro j
      constructor
      · intro hj
        have hnotDirect : j ∉ direct := by
          intro hjDirect
          exact Finset.disjoint_left.mp hvalid.2.1 hjDirect hj
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right direct hj, hnotDirect⟩
      · intro hj
        have hsupport : j ∈ direct ∪ childrenSupport children :=
          (Finset.mem_sdiff.mp hj).1
        have hnotDirect : j ∉ direct := (Finset.mem_sdiff.mp hj).2
        rcases Finset.mem_union.mp hsupport with hjDirect | hjChildren
        · exact (hnotDirect hjDirect).elim
        · exact hjChildren

/-- Every direct child of a valid drift vertex has nonempty support. -/
theorem DriftTreeData.valid_child_support_nonempty {J noiseDim : ℕ}
    (tree child : DriftTreeData J noiseDim) (hvalid : tree.Valid)
    (hchild : child ∈ tree.children) : child.support.Nonempty := by
  cases tree with
  | node direct children =>
      simp only [DriftTreeData.Valid, DriftTreeData.children] at hvalid hchild
      exact child.valid_support_nonempty (hvalid.2.2.2.2 child hchild)

/-- At the payoff root, the union of the child-subtree labels is `u \ E`.  Together with
pairwise disjointness and nonempty child supports, these are precisely the blocks of the root
partition in the inverse construction of Lemma `lem:correspondence`. -/
theorem LabelledPayoffTree.childrenSupport_eq_sdiff_direct {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    childrenSupport tree.data.children = u \ tree.data.direct := by
  have hsupport := tree.valid.1
  have hdisjoint := tree.valid.2.2.1
  apply Finset.ext
  intro j
  constructor
  · intro hj
    have hnotDirect : j ∉ tree.data.direct := by
      intro hjDirect
      exact Finset.disjoint_left.mp hdisjoint hjDirect hj
    exact Finset.mem_sdiff.mpr ⟨by
      rw [← hsupport]
      exact Finset.mem_union_right _ hj, hnotDirect⟩
  · intro hj
    have hsupportMem : j ∈ tree.data.support := by
      rw [hsupport]
      exact (Finset.mem_sdiff.mp hj).1
    have hnotDirect : j ∉ tree.data.direct := (Finset.mem_sdiff.mp hj).2
    rcases Finset.mem_union.mp hsupportMem with hjDirect | hjChildren
    · exact (hnotDirect hjDirect).elim
    · exact hjChildren

/-- Every child of a labelled payoff root has nonempty support. -/
theorem LabelledPayoffTree.child_support_nonempty {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u)
    (child : DriftTreeData J noiseDim) (hchild : child ∈ tree.data.children) :
    child.support.Nonempty :=
  child.valid_support_nonempty (tree.valid.2.2.2.2.2 child hchild)

/-- A pairwise-disjoint list of nonempty finite sets has no repeated member. -/
private theorem supports_nodup_of_pairwise_disjoint {α : Type*}
    (supports : List (Finset α)) (hdisjoint : supports.Pairwise Disjoint)
    (hnonempty : ∀ support ∈ supports, support.Nonempty) : supports.Nodup := by
  induction supports with
  | nil => simp
  | cons head tail ih =>
      rw [List.pairwise_cons] at hdisjoint
      rw [List.nodup_cons]
      constructor
      · intro hhead
        have hself : Disjoint head head := hdisjoint.1 head hhead
        exact (hnonempty head (by simp)).ne_empty
          (disjoint_self.mp hself)
      · apply ih hdisjoint.2
        intro support hsupport
        exact hnonempty support (by simp [hsupport])

/-- The supremum of the distinct child-support blocks is their union. -/
theorem childSupports_sup {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim)) :
    (childSupports children).toFinset.sup id = childrenSupport children := by
  induction children with
  | nil => simp [childSupports, childrenSupport]
  | cons head tail ih =>
      rw [show childSupports (head :: tail) = head.support :: childSupports tail by rfl]
      rw [List.toFinset_cons, Finset.sup_insert, ih]
      rfl

/-- Pairwise-disjoint nonempty child supports form a Mathlib finite partition of their union.
This is the library object corresponding to a local partition `π_y` in the paper. -/
noncomputable def childrenPartition {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim))
    (hdisjoint : childrenDisjoint children)
    (hnonempty : ∀ child ∈ children, child.support.Nonempty) :
    Finpartition (childrenSupport children) := by
  let supports := childSupports children
  have hsupportsNonempty : ∀ support ∈ supports, support.Nonempty := by
    intro support hsupport
    rcases List.mem_map.mp hsupport with ⟨child, hchild, rfl⟩
    exact hnonempty child hchild
  have hnodup : supports.Nodup :=
    supports_nodup_of_pairwise_disjoint supports hdisjoint hsupportsNonempty
  have hlistDisjoint : supports.Pairwise Disjoint := by
    simpa [supports, childSupports, childrenDisjoint] using hdisjoint
  have hsetDisjoint : (supports.toFinset : Set (Finset (Index J noiseDim))).PairwiseDisjoint id :=
    (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hnodup).2 (by
      exact hlistDisjoint)
  exact (Finpartition.ofPairwiseDisjoint supports.toFinset hsetDisjoint).copy
    (childSupports_sup children)

/-- No block is lost to the `Finpartition` constructor: the partition parts are exactly the
child-subtree supports. -/
@[simp]
theorem childrenPartition_parts {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim))
    (hdisjoint : childrenDisjoint children)
    (hnonempty : ∀ child ∈ children, child.support.Nonempty) :
    (childrenPartition children hdisjoint hnonempty).parts =
      (childSupports children).toFinset := by
  simp only [childrenPartition, Finpartition.copy_parts,
    Finpartition.ofPairwiseDisjoint_parts]
  apply Finset.erase_eq_self.mpr
  intro hempty
  have hemptyList : ∅ ∈ childSupports children := by simpa using hempty
  rcases List.mem_map.mp hemptyList with ⟨child, hchild, hsupport⟩
  exact (hnonempty child hchild).ne_empty hsupport

/-- A disjoint family of nonempty child supports cannot have more blocks than labels. -/
theorem children_length_le_childrenSupport_card {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim))
    (hdisjoint : childrenDisjoint children)
    (hnonempty : ∀ child ∈ children, child.support.Nonempty) :
    children.length ≤ (childrenSupport children).card := by
  let supports := childSupports children
  have hsupportsNonempty : ∀ support ∈ supports, support.Nonempty := by
    intro support hsupport
    rcases List.mem_map.mp hsupport with ⟨child, hchild, rfl⟩
    exact hnonempty child hchild
  have hnodup : supports.Nodup :=
    supports_nodup_of_pairwise_disjoint supports hdisjoint hsupportsNonempty
  have hcard := (childrenPartition children hdisjoint hnonempty).card_parts_le_card
  rw [childrenPartition_parts, List.toFinset_card_of_nodup hnodup] at hcard
  simpa [supports, childSupports] using hcard

/-- The number of direct arguments plus child arguments is bounded by the number of labels in a
valid drift subtree.  This is the cardinality step in the inverse construction. -/
theorem DriftTreeData.valid_localOrder_le_support_card {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    tree.direct.card + tree.children.length ≤ tree.support.card := by
  cases tree with
  | node direct children =>
      simp only [DriftTreeData.Valid] at hvalid
      rw [DriftTreeData.support_node, Finset.card_union_of_disjoint hvalid.2.1]
      exact Nat.add_le_add_left
        (children_length_le_childrenSupport_card children hvalid.2.2.1
          (fun child hchild =>
            child.valid_support_nonempty (hvalid.2.2.2.2 child hchild))) direct.card

/-- A valid drift vertex is either the exceptional singleton leaf from
`eq:partition-first`, or its whole subtree contains at least two labels and therefore belongs to
the higher-order recurrence `eq:correspondence-reindex`. -/
theorem DriftTreeData.valid_singletonLeaf_or_two_le_support_card {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.direct.card = 1 ∧ tree.children = []) ∨ 2 ≤ tree.support.card := by
  cases tree with
  | node direct children =>
      have hvalidRaw := hvalid
      simp only [DriftTreeData.Valid] at hvalid
      rcases hvalid.1 with hsingleton | hhigher
      · left
        constructor
        · exact hsingleton.1
        · change children = []
          simpa using hsingleton.2
      · right
        exact hhigher.trans
          ((DriftTreeData.node direct children).valid_localOrder_le_support_card hvalidRaw)

/-- The local partition at a valid drift vertex.  Its parts are precisely the supports of the
direct child subtrees, and its underlying set is `support \ direct`. -/
noncomputable def DriftTreeData.childPartition {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    Finpartition (tree.support \ tree.direct) :=
  match tree with
  | .node direct children =>
      have hparts : locallyAdmissible direct.card children.length ∧
          Disjoint direct (childrenSupport children) ∧ childrenDisjoint children ∧
          childrenCanonical children ∧ ∀ child ∈ children, child.Valid := by
        simpa only [DriftTreeData.Valid] using hvalid
      (childrenPartition children hparts.2.2.1 (fun child hchild =>
        child.valid_support_nonempty (hparts.2.2.2.2 child hchild))).copy
        ((DriftTreeData.node direct children).valid_childrenSupport_eq_support_sdiff_direct hvalid)

@[simp]
theorem DriftTreeData.childPartition_parts {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.childPartition hvalid).parts = (childSupports tree.children).toFinset := by
  cases tree with
  | node direct children =>
      simp only [DriftTreeData.childPartition]
      have hparts : locallyAdmissible direct.card children.length ∧
          Disjoint direct (childrenSupport children) ∧ childrenDisjoint children ∧
          childrenCanonical children ∧ ∀ child ∈ children, child.Valid := by
        simpa only [DriftTreeData.Valid] using hvalid
      exact childrenPartition_parts children hparts.2.2.1 (fun child hchild =>
        child.valid_support_nonempty (hparts.2.2.2.2 child hchild))

/-- The local partition at the payoff root.  Its underlying set is `u \ E`. -/
noncomputable def LabelledPayoffTree.childPartition {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    Finpartition (u \ tree.data.direct) :=
  (childrenPartition tree.data.children tree.valid.2.2.2.1 tree.child_support_nonempty).copy
    tree.childrenSupport_eq_sdiff_direct

@[simp]
theorem LabelledPayoffTree.childPartition_parts {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    tree.childPartition.parts = (childSupports tree.data.children).toFinset := by
  simp only [LabelledPayoffTree.childPartition, Finpartition.copy_parts]
  apply childrenPartition_parts

/-- Canonical ordering removes the irrelevant permutation of unordered siblings: two canonical
child lists representing the same multiset are equal. -/
theorem children_eq_of_perm_of_canonical {J noiseDim : ℕ}
    {left right : List (DriftTreeData J noiseDim)} (hperm : left.Perm right)
    (hleft : childrenCanonical left) (hright : childrenCanonical right) :
    left = right := by
  exact hperm.eq_of_pairwise' hleft hright

end

end TimeDependentLattice.Trees
