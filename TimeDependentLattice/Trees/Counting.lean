/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.Permutation
import Mathlib.Data.Fintype.CardEmbedding
import TimeDependentLattice.Trees.PayoffTree

/-!
# Structural counts for labelled payoff trees

This file formalizes the purely combinatorial part of paper Lemma B.6.  A drift vertex is
counted as nonempty or empty according to its direct coordinate set.  The quantity
`PayoffTreeData.childFactorialProduct` is the paper's
`Q(\mathfrak T) = \prod_y c_y!`, including the payoff root.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open TimeDependentLattice.BrownianBridge

/-- Number of drift vertices with a nonempty direct coordinate set. -/
def DriftTreeData.nonemptyDirectCount {J noiseDim : ℕ} : DriftTreeData J noiseDim → ℕ
  | .node direct children =>
      (if direct.Nonempty then 1 else 0) + (children.map nonemptyDirectCount).sum
termination_by tree => sizeOf tree

/-- Number of drift vertices with an empty direct coordinate set. -/
def DriftTreeData.emptyDirectCount {J noiseDim : ℕ} : DriftTreeData J noiseDim → ℕ
  | .node direct children =>
      (if direct = ∅ then 1 else 0) + (children.map emptyDirectCount).sum
termination_by tree => sizeOf tree

/-- Number of leaves in a drift subtree. -/
def DriftTreeData.leafCount {J noiseDim : ℕ} : DriftTreeData J noiseDim → ℕ
  | .node _ children =>
      if children = [] then 1 else (children.map leafCount).sum
termination_by tree => sizeOf tree

/-- Product of the factorials of the child counts over all vertices of a drift subtree. -/
def DriftTreeData.childFactorialProduct {J noiseDim : ℕ} : DriftTreeData J noiseDim → ℕ
  | .node _ children =>
      children.length.factorial * (children.map childFactorialProduct).prod
termination_by tree => sizeOf tree

/-- Sum of the cardinalities of all direct labels in a drift subtree. -/
def DriftTreeData.directCardSum {J noiseDim : ℕ} : DriftTreeData J noiseDim → ℕ
  | .node direct children => direct.card + (children.map directCardSum).sum
termination_by tree => sizeOf tree

/-- Product of the factorials of all direct-label cardinalities in a drift subtree. -/
def DriftTreeData.directFactorialProduct {J noiseDim : ℕ} :
    DriftTreeData J noiseDim → ℕ
  | .node direct children =>
      direct.card.factorial * (children.map directFactorialProduct).prod
termination_by tree => sizeOf tree

/-- Sum of the child counts over all vertices in a drift subtree. -/
def DriftTreeData.childCountSum {J noiseDim : ℕ} : DriftTreeData J noiseDim → ℕ
  | .node _ children => children.length + (children.map childCountSum).sum
termination_by tree => sizeOf tree

/-- Direct coordinate sets in preorder, including empty direct sets. -/
def DriftTreeData.directLabels {J noiseDim : ℕ} :
    DriftTreeData J noiseDim → List (Finset (Index J noiseDim))
  | .node direct children =>
      direct :: children.flatMap DriftTreeData.directLabels
termination_by tree => sizeOf tree

/-- Direct coordinate sets on drift vertices of a payoff tree, excluding the payoff root. -/
def PayoffTreeData.driftDirectLabels {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : List (Finset (Index J noiseDim)) :=
  tree.children.flatMap DriftTreeData.directLabels

/-- Every preorder direct label is contained in the support of its drift subtree. -/
theorem DriftTreeData.directLabel_subset_support
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    ∀ direct ∈ tree.directLabels, direct ⊆ tree.support := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ ∀ direct ∈ tree.directLabels,
      direct ⊆ tree.support)
    (motive_2 := fun trees ↦ ∀ direct ∈ trees.flatMap DriftTreeData.directLabels,
      ∃ child ∈ trees, direct ⊆ child.support)
    (fun root children hchildren direct hdirect ↦ by
      simp only [DriftTreeData.directLabels, List.mem_cons] at hdirect
      rcases hdirect with hdirect | hdirect
      · rw [hdirect]
        intro coordinate hcoordinate
        rw [DriftTreeData.support_node]
        exact Finset.mem_union_left _ hcoordinate
      · rcases hchildren direct hdirect with ⟨child, hchild, hsubset⟩
        simpa only [DriftTreeData.support_node] using
          hsubset.trans ((child.support_subset_childrenSupport hchild).trans
            (Finset.subset_union_right :
              childrenSupport children ⊆ root ∪ childrenSupport children)))
    (fun direct hdirect ↦ by simp at hdirect)
    (fun head tail hhead htail direct hdirect ↦ by
      simp only [List.flatMap_cons, List.mem_append] at hdirect
      rcases hdirect with hdirect | hdirect
      · exact ⟨head, List.mem_cons_self, hhead direct hdirect⟩
      · rcases htail direct hdirect with ⟨child, hchild, hsubset⟩
        exact ⟨child, List.mem_cons_of_mem head hchild, hsubset⟩)
    tree

/-- A coordinate lies in a drift-tree support exactly when it lies in one preorder direct
label. -/
theorem DriftTreeData.mem_support_iff_exists_directLabel
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim)
    (coordinate : Index J noiseDim) :
    coordinate ∈ tree.support ↔
      ∃ direct ∈ tree.directLabels, coordinate ∈ direct := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ coordinate ∈ tree.support ↔
      ∃ direct ∈ tree.directLabels, coordinate ∈ direct)
    (motive_2 := fun trees ↦ coordinate ∈ childrenSupport trees ↔
      ∃ direct ∈ trees.flatMap DriftTreeData.directLabels, coordinate ∈ direct)
    (fun direct children hchildren ↦ by
      rw [DriftTreeData.support_node, Finset.mem_union, hchildren]
      simp only [DriftTreeData.directLabels, List.mem_cons]
      constructor
      · rintro (hdirect | ⟨label, hlabel, hcoordinate⟩)
        · exact ⟨direct, Or.inl rfl, hdirect⟩
        · exact ⟨label, Or.inr hlabel, hcoordinate⟩
      · rintro ⟨label, rfl | hlabel, hcoordinate⟩
        · exact Or.inl hcoordinate
        · exact Or.inr ⟨label, hlabel, hcoordinate⟩)
    (by simp)
    (fun head tail hhead htail ↦ by
      rw [childrenSupport_cons, Finset.mem_union, hhead, htail]
      simp only [List.flatMap_cons, List.mem_append]
      constructor
      · rintro (⟨label, hlabel, hcoordinate⟩ |
          ⟨label, hlabel, hcoordinate⟩)
        · exact ⟨label, Or.inl hlabel, hcoordinate⟩
        · exact ⟨label, Or.inr hlabel, hcoordinate⟩
      · rintro ⟨label, hlabel | hlabel, hcoordinate⟩
        · exact Or.inl ⟨label, hlabel, hcoordinate⟩
        · exact Or.inr ⟨label, hlabel, hcoordinate⟩)
    tree

/-- In a valid drift subtree, direct labels at distinct vertices are pairwise disjoint. -/
theorem DriftTreeData.valid_directLabels_pairwiseDisjoint
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    tree.directLabels.Pairwise Disjoint := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ tree.Valid → tree.directLabels.Pairwise Disjoint)
    (motive_2 := fun trees ↦
      childrenDisjoint trees → (∀ child ∈ trees, child.Valid) →
        (trees.flatMap DriftTreeData.directLabels).Pairwise Disjoint)
    (fun direct children hchildren hvalidNode ↦ by
      simp only [DriftTreeData.Valid] at hvalidNode
      rw [DriftTreeData.directLabels, List.pairwise_cons]
      constructor
      · intro label hlabel
        rcases List.mem_flatMap.mp hlabel with ⟨child, hchild, hlabelChild⟩
        exact hvalidNode.2.1.mono_right
          ((child.directLabel_subset_support label hlabelChild).trans
            (child.support_subset_childrenSupport hchild))
      · exact hchildren hvalidNode.2.2.1 hvalidNode.2.2.2.2)
    (fun _ _ ↦ by simp)
    (fun head tail hhead htail hdisjoint hvalidChildren ↦ by
      change (head.support :: tail.map DriftTreeData.support).Pairwise Disjoint at hdisjoint
      have htailDisjoint : childrenDisjoint tail := by
        change (tail.map DriftTreeData.support).Pairwise Disjoint
        exact (List.pairwise_cons.mp hdisjoint).2
      have htailValid : ∀ child ∈ tail, child.Valid := by
        intro child hchild
        exact hvalidChildren child (List.mem_cons_of_mem head hchild)
      have htailPairwise := htail htailDisjoint htailValid
      rw [List.pairwise_flatMap]
      constructor
      · intro child hchild
        rcases List.mem_cons.mp hchild with hchild | hchild
        · rw [hchild]
          exact hhead (hvalidChildren _ List.mem_cons_self)
        · exact (List.pairwise_flatMap.mp htailPairwise).1 child hchild
      · rw [List.pairwise_cons]
        constructor
        · intro child hchild left hleft right hright
          have hsupports : Disjoint head.support child.support :=
            (List.pairwise_cons.mp hdisjoint).1 child.support
              (by exact List.mem_map.mpr ⟨child, hchild, rfl⟩)
          exact hsupports.mono
            (head.directLabel_subset_support left hleft)
            (child.directLabel_subset_support right hright)
        · exact (List.pairwise_flatMap.mp htailPairwise).2)
    tree hvalid

/-- Nonempty direct blocks on drift vertices. -/
def PayoffTreeData.nonemptyDirectLabels {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : List (Finset (Index J noiseDim)) :=
  tree.driftDirectLabels.filter fun direct => decide direct.Nonempty

/-- Empty direct labels on drift vertices. -/
def PayoffTreeData.emptyDirectLabels {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : List (Finset (Index J noiseDim)) :=
  tree.driftDirectLabels.filter fun direct => decide (direct = ∅)

/-- For a valid payoff tree, all nonroot direct labels are pairwise disjoint. -/
theorem PayoffTreeData.valid_driftDirectLabels_pairwiseDisjoint
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    {support : Finset (Index J noiseDim)} (hvalid : tree.Valid support) :
    tree.driftDirectLabels.Pairwise Disjoint := by
  unfold PayoffTreeData.driftDirectLabels
  rw [List.pairwise_flatMap]
  constructor
  · intro child hchild
    exact child.valid_directLabels_pairwiseDisjoint
      (hvalid.2.2.2.2.2 child hchild)
  · have hsupports := hvalid.2.2.2.1
    unfold childrenDisjoint at hsupports
    rw [List.pairwise_map] at hsupports
    exact hsupports.imp (fun {left right} hdisjoint labelLeft hleft
      labelRight hright ↦ hdisjoint.mono
        (left.directLabel_subset_support labelLeft hleft)
        (right.directLabel_subset_support labelRight hright))

/-- The nonempty direct labels of a valid payoff tree have no repetitions. -/
theorem PayoffTreeData.valid_nonemptyDirectLabels_nodup
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    {support : Finset (Index J noiseDim)} (hvalid : tree.Valid support) :
    tree.nonemptyDirectLabels.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  have hpairwise :=
    (tree.valid_driftDirectLabels_pairwiseDisjoint hvalid).filter
      (fun direct ↦ decide direct.Nonempty)
  exact hpairwise.imp_of_mem (fun {left right} hleft _ hdisjoint heq ↦ by
    subst right
    have hempty : left = ∅ := disjoint_self.mp hdisjoint
    have hnonempty : left.Nonempty := by
      have hdecide := (List.mem_filter.mp hleft).2
      simpa using hdecide
    exact hnonempty.ne_empty hempty)

/-- A valid tree's preorder list is a permutation of the finite set of its nonempty direct
blocks. -/
theorem PayoffTreeData.valid_nonemptyDirectLabels_perm_toFinset
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    {support : Finset (Index J noiseDim)} (hvalid : tree.Valid support) :
    tree.nonemptyDirectLabels.Perm tree.nonemptyDirectLabels.toFinset.toList :=
  (List.toFinset_toList (tree.valid_nonemptyDirectLabels_nodup hvalid)).symm

/-- A valid payoff tree with no nonempty label below the root has no drift child. -/
theorem PayoffTreeData.valid_children_eq_nil_of_nonemptyDirectLabels_eq_nil
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    {support : Finset (Index J noiseDim)} (hvalid : tree.Valid support)
    (hlabels : tree.nonemptyDirectLabels = []) :
    tree.children = [] := by
  by_contra hchildren
  rcases List.exists_mem_of_ne_nil tree.children hchildren with ⟨child, hchild⟩
  have hchildValid := hvalid.2.2.2.2.2 child hchild
  rcases child.valid_support_nonempty hchildValid with ⟨coordinate, hcoordinate⟩
  rcases (child.mem_support_iff_exists_directLabel coordinate).mp hcoordinate with
    ⟨direct, hdirect, hcoordinateDirect⟩
  have hnonempty : direct.Nonempty := ⟨coordinate, hcoordinateDirect⟩
  have hmem : direct ∈ tree.nonemptyDirectLabels := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_flatMap.mpr ⟨child, hchild, hdirect⟩, by simp [hnonempty]⟩
  rw [hlabels] at hmem
  simp at hmem

/-- The nonroot support is covered exactly by the preorder drift labels. -/
theorem PayoffTreeData.mem_childrenSupport_iff_exists_driftDirectLabel
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    (coordinate : Index J noiseDim) :
    coordinate ∈ childrenSupport tree.children ↔
      ∃ direct ∈ tree.driftDirectLabels, coordinate ∈ direct := by
  constructor
  · intro hcoordinate
    rcases mem_childrenSupport_iff_exists.mp hcoordinate with
      ⟨child, hchild, hcoordinateChild⟩
    rcases (child.mem_support_iff_exists_directLabel coordinate).mp
      hcoordinateChild with ⟨direct, hdirect, hcoordinateDirect⟩
    exact ⟨direct, List.mem_flatMap.mpr ⟨child, hchild, hdirect⟩,
      hcoordinateDirect⟩
  · rintro ⟨direct, hdirect, hcoordinateDirect⟩
    rcases List.mem_flatMap.mp hdirect with ⟨child, hchild, hdirectChild⟩
    apply mem_childrenSupport_iff_exists.mpr
    exact ⟨child, hchild,
      (child.mem_support_iff_exists_directLabel coordinate).mpr
        ⟨direct, hdirectChild, hcoordinateDirect⟩⟩

/-- The nonempty direct labels cover the same nonroot support; empty labels contribute no
coordinates. -/
theorem PayoffTreeData.mem_childrenSupport_iff_exists_nonemptyDirectLabel
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    (coordinate : Index J noiseDim) :
    coordinate ∈ childrenSupport tree.children ↔
      ∃ direct ∈ tree.nonemptyDirectLabels, coordinate ∈ direct := by
  rw [tree.mem_childrenSupport_iff_exists_driftDirectLabel coordinate]
  constructor
  · rintro ⟨direct, hdirect, hcoordinate⟩
    have hnonempty : direct.Nonempty := ⟨coordinate, hcoordinate⟩
    exact ⟨direct, List.mem_filter.mpr ⟨hdirect, by simp [hnonempty]⟩,
      hcoordinate⟩
  · rintro ⟨direct, hdirect, hcoordinate⟩
    exact ⟨direct, (List.mem_filter.mp hdirect).1, hcoordinate⟩

/-- The paper's global partition `Π(𝔗)`: all nonempty direct labels below the payoff root. -/
noncomputable def LabelledPayoffTree.nonemptyDirectPartition
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (tree : LabelledPayoffTree J noiseDim support) :
    Finpartition (support \ tree.data.direct) := by
  let parts := tree.data.nonemptyDirectLabels.toFinset
  apply Finpartition.ofExistsUnique parts
  · intro direct hdirect
    have hdirectList : direct ∈ tree.data.nonemptyDirectLabels := by
      simpa [parts] using hdirect
    have hdirectAll := (List.mem_filter.mp hdirectList).1
    rcases List.mem_flatMap.mp hdirectAll with ⟨child, hchild, hdirectChild⟩
    rw [← tree.childrenSupport_eq_sdiff_direct]
    exact (child.directLabel_subset_support direct hdirectChild).trans
      (child.support_subset_childrenSupport hchild)
  · intro coordinate hcoordinate
    have hchildren : coordinate ∈ childrenSupport tree.data.children := by
      rwa [tree.childrenSupport_eq_sdiff_direct]
    rcases (tree.data.mem_childrenSupport_iff_exists_nonemptyDirectLabel coordinate).mp
      hchildren with ⟨direct, hdirect, hcoordinateDirect⟩
    refine ⟨direct, ⟨by simpa [parts] using hdirect, hcoordinateDirect⟩, ?_⟩
    intro other hother
    by_contra hne
    have hpairwise := tree.data.valid_driftDirectLabels_pairwiseDisjoint tree.valid
    have hdirectAll : direct ∈ tree.data.driftDirectLabels :=
      (List.mem_filter.mp hdirect).1
    have hotherList : other ∈ tree.data.nonemptyDirectLabels := by
      simpa [parts] using hother.1
    have hotherAll : other ∈ tree.data.driftDirectLabels :=
      (List.mem_filter.mp hotherList).1
    have hdisjoint : Disjoint direct other :=
      hpairwise.forall hdirectAll hotherAll (fun heq ↦ hne heq.symm)
    exact Finset.disjoint_left.mp hdisjoint hcoordinateDirect hother.2
  · intro hempty
    have hemptyList : (∅ : Finset (Index J noiseDim)) ∈
        tree.data.nonemptyDirectLabels := by
      simpa [parts] using hempty
    have hnonempty : (∅ : Finset (Index J noiseDim)).Nonempty := by
      have hdecide := (List.mem_filter.mp hemptyList).2
      simpa using hdecide
    exact Finset.not_nonempty_empty hnonempty

@[simp]
theorem LabelledPayoffTree.nonemptyDirectPartition_parts
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (tree : LabelledPayoffTree J noiseDim support) :
    tree.nonemptyDirectPartition.parts =
      tree.data.nonemptyDirectLabels.toFinset := by
  simp [LabelledPayoffTree.nonemptyDirectPartition]

/-- The preorder nonempty labels are a permutation of the parts of the global partition. -/
theorem LabelledPayoffTree.nonemptyDirectLabels_perm_partitionParts
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (tree : LabelledPayoffTree J noiseDim support) :
    tree.data.nonemptyDirectLabels.Perm
      tree.nonemptyDirectPartition.parts.toList := by
  rw [tree.nonemptyDirectPartition_parts]
  exact tree.data.valid_nonemptyDirectLabels_perm_toFinset tree.valid

/-- Number of drift vertices with a nonempty direct set in a payoff tree.  On the paper's
family `Γ(E, π)`, this is `|π|`. -/
def PayoffTreeData.nonemptyDriftCount {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : ℕ :=
  (tree.children.map DriftTreeData.nonemptyDirectCount).sum

/-- Number `k₀` of drift vertices with an empty direct set in paper Lemma B.6. -/
def PayoffTreeData.emptyDriftCount {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : ℕ :=
  (tree.children.map DriftTreeData.emptyDirectCount).sum

/-- Number of leaves in the whole payoff tree. -/
def PayoffTreeData.leafCount {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) : ℕ :=
  if tree.children = [] then 1 else (tree.children.map DriftTreeData.leafCount).sum

/-- The paper's global input factorial `Q(𝔗) = ∏_y c_y!`, including the payoff root. -/
def PayoffTreeData.childFactorialProduct {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : ℕ :=
  tree.children.length.factorial *
    (tree.children.map DriftTreeData.childFactorialProduct).prod

theorem DriftTreeData.childFactorialProduct_pos
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    0 < tree.childFactorialProduct := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ 0 < tree.childFactorialProduct)
    (motive_2 := fun children ↦
      0 < (children.map DriftTreeData.childFactorialProduct).prod)
    (fun _ children hchildren ↦ by
      simp only [DriftTreeData.childFactorialProduct]
      exact mul_pos (Nat.factorial_pos _) hchildren)
    (by simp)
    (fun _ _ hhead htail ↦ by
      simp only [List.map_cons, List.prod_cons]
      exact mul_pos hhead htail)
    tree

theorem PayoffTreeData.childFactorialProduct_pos
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    0 < tree.childFactorialProduct := by
  unfold PayoffTreeData.childFactorialProduct
  apply mul_pos (Nat.factorial_pos _)
  apply List.prod_pos
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨child, _, rfl⟩
  exact child.childFactorialProduct_pos

/-- Sum of the cardinalities of all direct labels, including the payoff root. -/
def PayoffTreeData.directCardSum {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : ℕ :=
  tree.direct.card + (tree.children.map DriftTreeData.directCardSum).sum

/-- Product of the direct-label factorials at all drift vertices. -/
def PayoffTreeData.nonrootDirectFactorialProduct {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : ℕ :=
  (tree.children.map DriftTreeData.directFactorialProduct).prod

/-- Sum of all child counts, including the payoff root. -/
def PayoffTreeData.childCountSum {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : ℕ :=
  tree.children.length + (tree.children.map DriftTreeData.childCountSum).sum

/-- In any finite rooted tree, the sum of all child counts is the number of vertices minus one. -/
theorem DriftTreeData.childCountSum_add_one_eq_vertexCount
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    tree.childCountSum + 1 = tree.vertexCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ tree.childCountSum + 1 = tree.vertexCount)
    (motive_2 := fun children ↦
      (children.map DriftTreeData.childCountSum).sum + children.length =
        (children.map DriftTreeData.vertexCount).sum)
    (fun _ children hchildren ↦ by
      simp only [DriftTreeData.childCountSum, DriftTreeData.vertexCount]
      omega)
    (by simp)
    (fun head tail hhead htail ↦ by
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega)
    tree

theorem PayoffTreeData.childCountSum_add_one_eq_vertexCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.childCountSum + 1 = tree.vertexCount := by
  have hforest :
      (tree.children.map DriftTreeData.childCountSum).sum + tree.children.length =
        (tree.children.map DriftTreeData.vertexCount).sum := by
    induction tree.children with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have hhead := head.childCountSum_add_one_eq_vertexCount
        omega
  simp only [PayoffTreeData.childCountSum, PayoffTreeData.vertexCount]
  omega

theorem DriftTreeData.directFactorialProduct_eq_directLabels_prod
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    tree.directFactorialProduct =
      (tree.directLabels.map fun direct ↦ direct.card.factorial).prod := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ tree.directFactorialProduct =
      (tree.directLabels.map fun direct ↦ direct.card.factorial).prod)
    (motive_2 := fun children ↦
      (children.map DriftTreeData.directFactorialProduct).prod =
        ((children.flatMap DriftTreeData.directLabels).map
          fun direct ↦ direct.card.factorial).prod)
    (fun direct children hchildren ↦ by
      simp only [DriftTreeData.directFactorialProduct, DriftTreeData.directLabels,
        List.map_cons, List.prod_cons]
      rw [hchildren])
    (by simp)
    (fun head tail hhead htail ↦ by
      simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
        List.prod_append]
      rw [hhead, htail])
    tree

theorem PayoffTreeData.nonrootDirectFactorialProduct_eq_driftDirectLabels_prod
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.nonrootDirectFactorialProduct =
      (tree.driftDirectLabels.map fun direct ↦ direct.card.factorial).prod := by
  unfold PayoffTreeData.nonrootDirectFactorialProduct PayoffTreeData.driftDirectLabels
  induction tree.children with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
        List.prod_append]
      rw [head.directFactorialProduct_eq_directLabels_prod, ih]

private theorem directLabels_factorial_prod_eq_filter_nonempty
    {α : Type*} [DecidableEq α] (labels : List (Finset α)) :
    (labels.map fun direct ↦ direct.card.factorial).prod =
      ((labels.filter fun direct ↦ decide direct.Nonempty).map
        fun direct ↦ direct.card.factorial).prod := by
  induction labels with
  | nil => simp
  | cons direct labels ih =>
      by_cases hdirect : direct.Nonempty
      · simp [hdirect, ih]
      · have hempty : direct = ∅ := Finset.not_nonempty_iff_eq_empty.mp hdirect
        simp [hdirect, hempty, ih]

/-- On the paper's family `Γ(E, π)`, the nonroot direct factorials are precisely the
factorials of the blocks of `π`; empty drift labels contribute `0! = 1`. -/
theorem PayoffTreeData.nonrootDirectFactorialProduct_eq_blocks
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    (blocks : Finset (Finset (Index J noiseDim)))
    (hblocks : tree.nonemptyDirectLabels.Perm blocks.toList) :
    tree.nonrootDirectFactorialProduct =
      ∏ block ∈ blocks, block.card.factorial := by
  rw [tree.nonrootDirectFactorialProduct_eq_driftDirectLabels_prod]
  rw [directLabels_factorial_prod_eq_filter_nonempty]
  change (tree.nonemptyDirectLabels.map fun direct ↦ direct.card.factorial).prod = _
  have hperm := hblocks.map (fun direct ↦ direct.card.factorial)
  rw [hperm.prod_eq]
  simp

/-- In a valid drift tree, the direct labels are a disjoint decomposition of its support. -/
theorem DriftTreeData.valid_directCardSum_eq_support_card
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    tree.directCardSum = tree.support.card := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ tree.Valid → tree.directCardSum = tree.support.card)
    (motive_2 := fun children ↦
      (∀ child ∈ children, child.Valid) →
        (children.map DriftTreeData.directCardSum).sum =
          (children.map fun child ↦ child.support.card).sum)
    (fun direct children hchildren hvalidNode ↦ by
      simp only [DriftTreeData.Valid] at hvalidNode
      simp only [DriftTreeData.directCardSum, DriftTreeData.support_node]
      rw [hchildren hvalidNode.2.2.2.2]
      rw [Finset.card_union_of_disjoint hvalidNode.2.1]
      rw [childrenSupport_card_eq_sum_support_card children hvalidNode.2.2.1])
    (fun _ ↦ by simp)
    (fun head tail hhead htail hvalidChildren ↦ by
      have hheadValid : head.Valid := hvalidChildren head (by simp)
      have htailValid : ∀ child ∈ tail, child.Valid := by
        intro child hchild
        exact hvalidChildren child (by simp [hchild])
      simp only [List.map_cons, List.sum_cons]
      rw [hhead hheadValid, htail htailValid])
    tree hvalid

/-- In a valid payoff tree, all direct-label cardinalities add up to the support cardinality. -/
theorem PayoffTreeData.valid_directCardSum_eq_support_card
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    {u : Finset (Index J noiseDim)} (hvalid : tree.Valid u) :
    tree.directCardSum = u.card := by
  have hchildren :
      (tree.children.map DriftTreeData.directCardSum).sum =
        (tree.children.map fun child ↦ child.support.card).sum := by
    rw [List.map_congr_left fun child hchild ↦
      child.valid_directCardSum_eq_support_card
        (hvalid.2.2.2.2.2 child hchild)]
  rw [← hvalid.1]
  simp only [PayoffTreeData.directCardSum, PayoffTreeData.support]
  rw [hchildren, Finset.card_union_of_disjoint hvalid.2.2.1]
  rw [childrenSupport_card_eq_sum_support_card tree.children hvalid.2.2.2.1]

/-- Filtering the preorder labels by nonemptiness counts precisely the nonempty-direct
vertices. -/
theorem DriftTreeData.length_filter_directLabels_eq_nonemptyDirectCount
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    (tree.directLabels.filter fun direct => decide direct.Nonempty).length =
      tree.nonemptyDirectCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree =>
      (tree.directLabels.filter fun direct => decide direct.Nonempty).length =
        tree.nonemptyDirectCount)
    (motive_2 := fun children =>
      ((children.flatMap DriftTreeData.directLabels).filter fun direct =>
        decide direct.Nonempty).length =
        (children.map DriftTreeData.nonemptyDirectCount).sum)
    (fun direct children hchildren => by
      by_cases hdirect : direct.Nonempty
      · simp [DriftTreeData.directLabels, DriftTreeData.nonemptyDirectCount,
          hdirect, hchildren, Nat.add_comm]
      · simp [DriftTreeData.directLabels, DriftTreeData.nonemptyDirectCount,
          hdirect, hchildren])
    (by simp)
    (fun head tail hhead htail => by
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.map_cons, List.sum_cons]
      rw [hhead, htail])
    tree

theorem PayoffTreeData.length_nonemptyDirectLabels_eq_nonemptyDriftCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.nonemptyDirectLabels.length = tree.nonemptyDriftCount := by
  rcases tree with ⟨direct, children⟩
  unfold PayoffTreeData.nonemptyDirectLabels PayoffTreeData.driftDirectLabels
  unfold PayoffTreeData.nonemptyDriftCount
  induction children with
  | nil => simp [PayoffTreeData.nonemptyDriftCount]
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.map_cons, List.sum_cons]
      rw [head.length_filter_directLabels_eq_nonemptyDirectCount, ih]

theorem DriftTreeData.length_filter_empty_directLabels_eq_emptyDirectCount
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    (tree.directLabels.filter fun direct => decide (direct = ∅)).length =
      tree.emptyDirectCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦
      (tree.directLabels.filter fun direct => decide (direct = ∅)).length =
        tree.emptyDirectCount)
    (motive_2 := fun children ↦
      ((children.flatMap DriftTreeData.directLabels).filter
          fun direct => decide (direct = ∅)).length =
        (children.map DriftTreeData.emptyDirectCount).sum)
    (fun direct children hchildren ↦ by
      by_cases hdirect : direct = ∅
      · simp [DriftTreeData.directLabels, DriftTreeData.emptyDirectCount,
          hdirect, hchildren, Nat.add_comm]
      · simp [DriftTreeData.directLabels, DriftTreeData.emptyDirectCount,
          hdirect, hchildren])
    (by simp)
    (fun head tail hhead htail ↦ by
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.map_cons, List.sum_cons]
      rw [hhead, htail])
    tree

theorem PayoffTreeData.length_emptyDirectLabels_eq_emptyDriftCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.emptyDirectLabels.length = tree.emptyDriftCount := by
  unfold PayoffTreeData.emptyDirectLabels PayoffTreeData.driftDirectLabels
  unfold PayoffTreeData.emptyDriftCount
  induction tree.children with
  | nil => simp
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.map_cons, List.sum_cons]
      rw [head.length_filter_empty_directLabels_eq_emptyDirectCount, ih]

/-- Every drift vertex is counted exactly once, according to whether its direct set is empty. -/
theorem DriftTreeData.vertexCount_eq_nonemptyDirectCount_add_emptyDirectCount
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    tree.vertexCount = tree.nonemptyDirectCount + tree.emptyDirectCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree =>
      tree.vertexCount = tree.nonemptyDirectCount + tree.emptyDirectCount)
    (motive_2 := fun children =>
      (children.map DriftTreeData.vertexCount).sum =
        (children.map DriftTreeData.nonemptyDirectCount).sum +
          (children.map DriftTreeData.emptyDirectCount).sum)
    (fun direct children hchildren => by
      by_cases hdirect : direct.Nonempty
      · have hne : direct ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hdirect
        simp only [DriftTreeData.vertexCount, DriftTreeData.nonemptyDirectCount,
          DriftTreeData.emptyDirectCount, hdirect, hne, ite_true, ite_false]
        rw [hchildren]
        omega
      · have hempty : direct = ∅ := Finset.not_nonempty_iff_eq_empty.mp hdirect
        simp [DriftTreeData.vertexCount, DriftTreeData.nonemptyDirectCount,
          DriftTreeData.emptyDirectCount, hempty]
        rw [hchildren]
        omega)
    (by simp)
    (fun head tail hhead htail => by
      simp only [List.map_cons, List.sum_cons]
      rw [hhead, htail]
      omega)
    tree

/-- The payoff root adds one vertex to the two classes of drift vertices. -/
theorem PayoffTreeData.vertexCount_eq_one_add_nonemptyDriftCount_add_emptyDriftCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.vertexCount = 1 + tree.nonemptyDriftCount + tree.emptyDriftCount := by
  have hsum :
      (tree.children.map DriftTreeData.vertexCount).sum =
        (tree.children.map DriftTreeData.nonemptyDirectCount).sum +
          (tree.children.map DriftTreeData.emptyDirectCount).sum := by
    induction tree.children with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [head.vertexCount_eq_nonemptyDirectCount_add_emptyDirectCount, ih]
        omega
  simp only [PayoffTreeData.vertexCount, PayoffTreeData.nonemptyDriftCount,
    PayoffTreeData.emptyDriftCount]
  rw [hsum]
  omega

/-- In a valid drift subtree, empty-direct vertices are strictly fewer than nonempty-direct
vertices.  The list motive records the stronger forest inequality used by the nested induction. -/
theorem DriftTreeData.valid_emptyDirectCount_lt_nonemptyDirectCount
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    tree.emptyDirectCount < tree.nonemptyDirectCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree =>
      tree.Valid → tree.emptyDirectCount < tree.nonemptyDirectCount)
    (motive_2 := fun children =>
      (∀ child ∈ children, child.Valid) →
        (children.map DriftTreeData.emptyDirectCount).sum + children.length ≤
          (children.map DriftTreeData.nonemptyDirectCount).sum)
    (fun direct children hchildren hvalidNode => by
      simp only [DriftTreeData.Valid] at hvalidNode
      have hforest := hchildren hvalidNode.2.2.2.2
      by_cases hdirect : direct.Nonempty
      · have hne : direct ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hdirect
        simp only [DriftTreeData.emptyDirectCount, DriftTreeData.nonemptyDirectCount,
          hdirect, hne, ite_true, ite_false]
        omega
      · have hempty : direct = ∅ := Finset.not_nonempty_iff_eq_empty.mp hdirect
        have htwo : 2 ≤ children.length := by
          rcases hvalidNode.1 with hsingleton | hhigher
          · rw [hempty] at hsingleton
            simp at hsingleton
          · rw [hempty] at hhigher
            simpa using hhigher
        simp [DriftTreeData.emptyDirectCount, DriftTreeData.nonemptyDirectCount, hempty]
        omega)
    (by simp)
    (fun head tail hhead htail hvalidChildren => by
      have hheadValid : head.Valid := hvalidChildren head (by simp)
      have htailValid : ∀ child ∈ tail, child.Valid := by
        intro child hchild
        exact hvalidChildren child (by simp [hchild])
      have hheadBound := hhead hheadValid
      have htailBound := htail htailValid
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega)
    tree hvalid

/-- Forest form of `valid_emptyDirectCount_lt_nonemptyDirectCount`.  Each valid component
contributes at least one more nonempty-direct vertex than empty-direct vertices. -/
theorem validForest_emptyDirectCount_add_length_le_nonemptyDirectCount
    {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim))
    (hvalid : ∀ child ∈ children, child.Valid) :
    (children.map DriftTreeData.emptyDirectCount).sum + children.length ≤
      (children.map DriftTreeData.nonemptyDirectCount).sum := by
  induction children with
  | nil => simp
  | cons head tail ih =>
      have hheadValid : head.Valid := hvalid head List.mem_cons_self
      have htailValid : ∀ child ∈ tail, child.Valid := by
        intro child hchild
        exact hvalid child (List.mem_cons_of_mem head hchild)
      have hheadBound := head.valid_emptyDirectCount_lt_nonemptyDirectCount hheadValid
      have htailBound := ih htailValid
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- For a nontrivial valid payoff tree, the paper's `k₀` satisfies `k₀ ≤ k - 1`. -/
theorem PayoffTreeData.emptyDriftCount_lt_nonemptyDriftCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) {u : Finset (Index J noiseDim)}
    (hvalid : tree.Valid u) (hchildren : tree.children ≠ []) :
    tree.emptyDriftCount < tree.nonemptyDriftCount := by
  have hforest :
      (tree.children.map DriftTreeData.emptyDirectCount).sum + tree.children.length ≤
        (tree.children.map DriftTreeData.nonemptyDirectCount).sum :=
    validForest_emptyDirectCount_add_length_le_nonemptyDirectCount tree.children
      hvalid.2.2.2.2.2
  have hlength : 0 < tree.children.length := List.length_pos_iff_ne_nil.mpr hchildren
  simpa only [PayoffTreeData.emptyDriftCount, PayoffTreeData.nonemptyDriftCount] using
    (show (tree.children.map DriftTreeData.emptyDirectCount).sum <
        (tree.children.map DriftTreeData.nonemptyDirectCount).sum by omega)

/-- Vertex-count part of paper Lemma B.6, with `k` represented by
`nonemptyDriftCount`. -/
theorem PayoffTreeData.vertexCount_le_two_mul_nonemptyDriftCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) {u : Finset (Index J noiseDim)}
    (hvalid : tree.Valid u) (hchildren : tree.children ≠ []) :
    tree.vertexCount ≤ 2 * tree.nonemptyDriftCount := by
  have hcount := tree.vertexCount_eq_one_add_nonemptyDriftCount_add_emptyDriftCount
  have hempty := tree.emptyDriftCount_lt_nonemptyDriftCount hvalid hchildren
  omega

/-- An interior binomial coefficient is at least the row number.  This elementary helper is used
to compare the number of child orderings with the number of leaf orderings. -/
theorem Nat.le_choose_of_pos_of_lt {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      by_cases hlast : k + 1 = n
      · subst n
        simpa using Nat.choose_succ_self_right (k + 1)
      · have hlt : k + 1 < n := by omega
        have hlarge : n ≤ n.choose (k + 1) := ih (by omega) hlt
        have hlarge' : n ≤ n.choose k.succ := by
          simpa [Nat.succ_eq_add_one] using hlarge
        have hpositive : 0 < n.choose k := Nat.choose_pos (by omega)
        rw [Nat.choose_succ_succ]
        omega

/-- A list of positive natural numbers has length at most its sum. -/
theorem list_length_le_sum_of_forall_pos (values : List ℕ)
    (hpos : ∀ value ∈ values, 0 < value) : values.length ≤ values.sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : 0 < head := hpos head List.mem_cons_self
      have htail : ∀ value ∈ tail, 0 < value := by
        intro value hvalue
        exact hpos value (List.mem_cons_of_mem head hvalue)
      have htailBound := ih htail
      simp only [List.length_cons, List.sum_cons]
      omega

/-- If `L₁, …, L_c` are positive, then `c! ∏ Lᵢ! ≤ (∑ Lᵢ)!`.  This is the
factorial inequality used in the proof of paper Lemma B.6. -/
theorem list_length_factorial_mul_prod_factorial_le_sum_factorial
    (values : List ℕ) (hpos : ∀ value ∈ values, 0 < value) :
    values.length.factorial * (values.map Nat.factorial).prod ≤ values.sum.factorial := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : 0 < head := hpos head List.mem_cons_self
      have htail : ∀ value ∈ tail, 0 < value := by
        intro value hvalue
        exact hpos value (List.mem_cons_of_mem head hvalue)
      have htailBound := ih htail
      by_cases htailEmpty : tail = []
      · subst tail
        simp
      · have hsumPos : 0 < tail.sum := by
          have hlengthPos : 0 < tail.length := List.length_pos_iff_ne_nil.mpr htailEmpty
          exact lt_of_lt_of_le hlengthPos (list_length_le_sum_of_forall_pos tail htail)
        have hchoose : head + tail.sum ≤ (head + tail.sum).choose tail.sum :=
          Nat.le_choose_of_pos_of_lt hsumPos (by omega)
        have hlength : tail.length + 1 ≤ head + tail.sum := by
          have := list_length_le_sum_of_forall_pos tail htail
          omega
        calc
          (head :: tail).length.factorial *
              ((head :: tail).map Nat.factorial).prod =
              (tail.length + 1) * head.factorial *
                (tail.length.factorial * (tail.map Nat.factorial).prod) := by
                  simp only [List.length_cons, Nat.factorial_succ, List.map_cons,
                    List.prod_cons]
                  ring
          _ ≤ (tail.length + 1) * head.factorial * tail.sum.factorial := by
                gcongr
          _ ≤ (head + tail.sum).choose tail.sum * head.factorial * tail.sum.factorial := by
                gcongr
                exact hlength.trans hchoose
          _ = (head + tail.sum).factorial :=
                Nat.add_choose_mul_factorial_mul_factorial head tail.sum
          _ = (head :: tail).sum.factorial := by simp

/-- Every finite drift tree has at least one leaf. -/
theorem DriftTreeData.leafCount_pos {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    0 < tree.leafCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree => 0 < tree.leafCount)
    (motive_2 := fun children =>
      children ≠ [] → 0 < (children.map DriftTreeData.leafCount).sum)
    (fun direct children hchildren => by
      by_cases hempty : children = []
      · subst children
        simp [DriftTreeData.leafCount]
      · simpa [DriftTreeData.leafCount, hempty] using hchildren hempty)
    (by simp)
    (fun head tail hhead _ _ => by
      simp only [List.map_cons, List.sum_cons]
      omega)
    tree

/-- For any finite rooted drift tree, the product of all child-count factorials is bounded by
the factorial of the number of leaves.  No admissibility hypothesis is needed. -/
theorem DriftTreeData.childFactorialProduct_le_leafCount_factorial
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    tree.childFactorialProduct ≤ tree.leafCount.factorial := by
  exact DriftTreeData.rec
    (motive_1 := fun tree =>
      tree.childFactorialProduct ≤ tree.leafCount.factorial)
    (motive_2 := fun children =>
      (children.map DriftTreeData.childFactorialProduct).prod ≤
        (children.map fun child => child.leafCount.factorial).prod)
    (fun direct children hchildren => by
      have hpositive : ∀ value ∈ children.map DriftTreeData.leafCount, 0 < value := by
        intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨child, hchild, rfl⟩
        exact child.leafCount_pos
      calc
        (DriftTreeData.node direct children).childFactorialProduct =
            children.length.factorial *
              (children.map DriftTreeData.childFactorialProduct).prod := by
                simp only [DriftTreeData.childFactorialProduct]
        _ ≤ children.length.factorial *
              (children.map fun child => child.leafCount.factorial).prod := by
                gcongr
        _ = (children.map DriftTreeData.leafCount).length.factorial *
              ((children.map DriftTreeData.leafCount).map Nat.factorial).prod := by
                rw [List.length_map, List.map_map]
                rfl
        _ ≤ (children.map DriftTreeData.leafCount).sum.factorial :=
              list_length_factorial_mul_prod_factorial_le_sum_factorial _ hpositive
        _ = (DriftTreeData.node direct children).leafCount.factorial := by
              by_cases hempty : children = []
              · subst children
                simp [DriftTreeData.leafCount]
              · simp [DriftTreeData.leafCount, hempty])
    (by simp)
    (fun head tail hhead htail => by
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul hhead htail)
    tree

/-- Forest form of the child-factorial bound. -/
theorem driftForest_childFactorialProduct_le_leafFactorialProduct
    {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim)) :
    (children.map DriftTreeData.childFactorialProduct).prod ≤
      (children.map fun child => child.leafCount.factorial).prod := by
  induction children with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul head.childFactorialProduct_le_leafCount_factorial ih

/-- Auxiliary rooted-tree inequality in paper Lemma B.6:
`Q(𝔖) ≤ L(𝔖)!` for every finite rooted payoff tree. -/
theorem PayoffTreeData.childFactorialProduct_le_leafCount_factorial
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.childFactorialProduct ≤ tree.leafCount.factorial := by
  have hpositive :
      ∀ value ∈ tree.children.map DriftTreeData.leafCount, 0 < value := by
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨child, hchild, rfl⟩
    exact child.leafCount_pos
  calc
    tree.childFactorialProduct = tree.children.length.factorial *
        (tree.children.map DriftTreeData.childFactorialProduct).prod := rfl
    _ ≤ tree.children.length.factorial *
        (tree.children.map fun child => child.leafCount.factorial).prod := by
          gcongr
          exact driftForest_childFactorialProduct_le_leafFactorialProduct tree.children
    _ = (tree.children.map DriftTreeData.leafCount).length.factorial *
        ((tree.children.map DriftTreeData.leafCount).map Nat.factorial).prod := by
          rw [List.length_map, List.map_map]
          rfl
    _ ≤ (tree.children.map DriftTreeData.leafCount).sum.factorial :=
      list_length_factorial_mul_prod_factorial_le_sum_factorial _ hpositive
    _ = tree.leafCount.factorial := by
      by_cases hempty : tree.children = []
      · simp [PayoffTreeData.leafCount, hempty]
      · simp [PayoffTreeData.leafCount, hempty]

/-- Every leaf of a valid drift tree has a nonempty direct set, so the number of leaves is at
most the number of nonempty-direct vertices. -/
theorem DriftTreeData.valid_leafCount_le_nonemptyDirectCount
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    tree.leafCount ≤ tree.nonemptyDirectCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree => tree.Valid → tree.leafCount ≤ tree.nonemptyDirectCount)
    (motive_2 := fun children =>
      (∀ child ∈ children, child.Valid) →
        (children.map DriftTreeData.leafCount).sum ≤
          (children.map DriftTreeData.nonemptyDirectCount).sum)
    (fun direct children hchildren hvalidNode => by
      simp only [DriftTreeData.Valid] at hvalidNode
      have hforest := hchildren hvalidNode.2.2.2.2
      by_cases hchildrenEmpty : children = []
      · subst children
        have hdirect : direct.Nonempty :=
          DriftTreeData.valid_leaf_direct_nonempty direct (by
            simpa only [DriftTreeData.Valid] using hvalidNode)
        simp [DriftTreeData.leafCount, DriftTreeData.nonemptyDirectCount, hdirect]
      · by_cases hdirect : direct.Nonempty
        · simp [DriftTreeData.leafCount, DriftTreeData.nonemptyDirectCount,
            hchildrenEmpty, hdirect]
          omega
        · simp [DriftTreeData.leafCount, DriftTreeData.nonemptyDirectCount,
            hchildrenEmpty, hdirect]
          exact hforest)
    (by simp)
    (fun head tail hhead htail hvalidChildren => by
      have hheadValid : head.Valid := hvalidChildren head List.mem_cons_self
      have htailValid : ∀ child ∈ tail, child.Valid := by
        intro child hchild
        exact hvalidChildren child (List.mem_cons_of_mem head hchild)
      have hheadBound := hhead hheadValid
      have htailBound := htail htailValid
      simp only [List.map_cons, List.sum_cons]
      omega)
    tree hvalid

/-- Forest form of the valid leaf-count bound. -/
theorem validForest_leafCount_le_nonemptyDirectCount
    {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim))
    (hvalid : ∀ child ∈ children, child.Valid) :
    (children.map DriftTreeData.leafCount).sum ≤
      (children.map DriftTreeData.nonemptyDirectCount).sum := by
  induction children with
  | nil => simp
  | cons head tail ih =>
      have hheadValid : head.Valid := hvalid head List.mem_cons_self
      have htailValid : ∀ child ∈ tail, child.Valid := by
        intro child hchild
        exact hvalid child (List.mem_cons_of_mem head hchild)
      have hheadBound := head.valid_leafCount_le_nonemptyDirectCount hheadValid
      have htailBound := ih htailValid
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A nontrivial valid payoff tree has at most `k` leaves, where `k` is the number of its
nonempty-direct drift vertices. -/
theorem PayoffTreeData.leafCount_le_nonemptyDriftCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) {u : Finset (Index J noiseDim)}
    (hvalid : tree.Valid u) (hchildren : tree.children ≠ []) :
    tree.leafCount ≤ tree.nonemptyDriftCount := by
  have hforest := validForest_leafCount_le_nonemptyDirectCount tree.children
    hvalid.2.2.2.2.2
  simp [PayoffTreeData.leafCount, PayoffTreeData.nonemptyDriftCount, hchildren]
  exact hforest

/-- Factorial part of paper Lemma B.6: `Q(𝔗) ≤ k!`. -/
theorem PayoffTreeData.childFactorialProduct_le_nonemptyDriftCount_factorial
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) {u : Finset (Index J noiseDim)}
    (hvalid : tree.Valid u) (hchildren : tree.children ≠ []) :
    tree.childFactorialProduct ≤ tree.nonemptyDriftCount.factorial :=
  tree.childFactorialProduct_le_leafCount_factorial.trans
    (Nat.factorial_le (tree.leafCount_le_nonemptyDriftCount hvalid hchildren))

/-- Paper Lemma B.6 (`lem:expression-structure`).  Here `nonemptyDriftCount` is the number
`k = |π|` of nonempty direct blocks, and `emptyDriftCount` is the paper's `k₀`. -/
theorem PayoffTreeData.expression_structure
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) {u : Finset (Index J noiseDim)}
    (hvalid : tree.Valid u) (hchildren : tree.children ≠ []) :
    tree.emptyDriftCount < tree.nonemptyDriftCount ∧
      tree.vertexCount ≤ 2 * tree.nonemptyDriftCount ∧
      tree.childFactorialProduct ≤ tree.nonemptyDriftCount.factorial :=
  ⟨tree.emptyDriftCount_lt_nonemptyDriftCount hvalid hchildren,
    tree.vertexCount_le_two_mul_nonemptyDriftCount hvalid hchildren,
    tree.childFactorialProduct_le_nonemptyDriftCount_factorial hvalid hchildren⟩

/-- The numerical Catalan estimate used in paper Lemma B.7. -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)

/-- A geometric sum with ratio eight is bounded by its next power. -/
theorem sum_eight_pow_le_eight_pow (n : ℕ) :
    ∑ i ∈ Finset.range n, 8 ^ i ≤ 8 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (∑ i ∈ Finset.range n, 8 ^ i) + 8 ^ n ≤ 8 ^ n + 8 ^ n :=
          Nat.add_le_add_right ih _
        _ ≤ 8 ^ n * 8 := by omega

/-- Arithmetic part of the weighted tree-pattern estimate.  The index `i = n - 1` is the
number of non-root vertices of a plane rooted tree. -/
theorem catalan_choose_sum_le_sixtyFour_pow (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), catalan i * i.choose k ≤ 64 ^ k := by
  calc
    (∑ i ∈ Finset.range (2 * k), catalan i * i.choose k) ≤
        ∑ i ∈ Finset.range (2 * k), 8 ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            catalan i * i.choose k ≤ 4 ^ i * 2 ^ i :=
              Nat.mul_le_mul (catalan_le_four_pow i) (Nat.choose_le_two_pow i k)
            _ = 8 ^ i := by norm_num [← mul_pow]
    _ ≤ 8 ^ (2 * k) := sum_eight_pow_le_eight_pow (2 * k)
    _ = 64 ^ k := by norm_num [pow_mul]

/-- Numerical form of the final bound in paper Lemma B.7. -/
theorem catalan_choose_factorial_sum_le_weightedPatternBound (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k), catalan i * i.choose k) * k.factorial ≤
      64 ^ k * k.factorial :=
  Nat.mul_le_mul_right k.factorial (catalan_choose_sum_le_sixtyFour_pow k)

/-- Cartesian choices from a list of finite choice lists. -/
def listChoices {α : Type*} : List (List α) → List (List α)
  | [] => [[]]
  | choices :: rest =>
      choices.flatMap fun choice => (listChoices rest).map (choice :: ·)

@[simp]
theorem listChoices_nil {α : Type*} : listChoices ([] : List (List α)) = [[]] := rfl

@[simp]
theorem listChoices_cons {α : Type*} (choices : List α) (rest : List (List α)) :
    listChoices (choices :: rest) =
      choices.flatMap fun choice => (listChoices rest).map (choice :: ·) := rfl

/-- Every Cartesian choice has one entry for each input choice list. -/
theorem length_eq_of_mem_listChoices {α : Type*} {families : List (List α)}
    {chosen : List α} (hchosen : chosen ∈ listChoices families) :
    chosen.length = families.length := by
  induction families generalizing chosen with
  | nil => simpa [listChoices] using hchosen
  | cons choices rest ih =>
      simp only [listChoices_cons, List.mem_flatMap, List.mem_map] at hchosen
      rcases hchosen with ⟨choice, hchoice, tail, htail, rfl⟩
      simp [ih htail]

/-- The number of Cartesian choices is the product of the numbers of local choices. -/
theorem length_listChoices {α : Type*} (families : List (List α)) :
    (listChoices families).length = (families.map List.length).prod := by
  induction families with
  | nil => simp [listChoices]
  | cons choices rest ih =>
      simp only [listChoices_cons, List.length_flatMap, List.length_map, ih,
        List.map_cons, List.prod_cons]
      simp

/-- A finite sum is constant times the length when the summand has the same value on every
entry. -/
theorem sum_map_eq_length_mul_of_mem_eq {α : Type*} (entries : List α) (value : α → ℕ)
    (constant : ℕ) (hvalue : ∀ entry ∈ entries, value entry = constant) :
    (entries.map value).sum = entries.length * constant := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      have hhead : value head = constant := hvalue head List.mem_cons_self
      have htail : ∀ entry ∈ tail, value entry = constant := by
        intro entry hentry
        exact hvalue entry (List.mem_cons_of_mem head hentry)
      simp [hhead, ih htail, Nat.add_mul, Nat.add_comm]

/-- All plane orderings of a raw drift tree.  At every vertex, recursive child variants are
chosen independently and then the resulting child list is permuted. -/
noncomputable def DriftTreeData.orderedVersions {J noiseDim : ℕ}
    : DriftTreeData J noiseDim → List (DriftTreeData J noiseDim)
  | .node direct children =>
      (listChoices (children.map DriftTreeData.orderedVersions)).flatMap fun chosen =>
        chosen.permutations.map (DriftTreeData.node direct)
termination_by tree => sizeOf tree

/-- The nested-recursion list produced inside `orderedVersions` is the list of the children's
ordered-version lists. -/
@[simp]
theorem DriftTreeData.orderedVersions_node {J noiseDim : ℕ}
    (direct : Finset (Index J noiseDim)) (children : List (DriftTreeData J noiseDim)) :
    DriftTreeData.orderedVersions (.node direct children) =
      (listChoices (children.map DriftTreeData.orderedVersions)).flatMap
        (fun chosen => chosen.permutations.map (DriftTreeData.node direct)) := by
  rw [DriftTreeData.orderedVersions]

/-- The local-order multiplicity of a drift tree is exactly the product of the factorials of
its child counts.  This is the precise bridge between the paper's weight `Q` and plane rooted
trees. -/
theorem DriftTreeData.length_orderedVersions_eq_childFactorialProduct
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) :
    tree.orderedVersions.length = tree.childFactorialProduct := by
  exact DriftTreeData.rec
    (motive_1 := fun tree =>
      tree.orderedVersions.length = tree.childFactorialProduct)
    (motive_2 := fun children =>
      ((children.map DriftTreeData.orderedVersions).map List.length).prod =
        (children.map DriftTreeData.childFactorialProduct).prod)
    (fun direct children hchildren => by
      let families := children.map DriftTreeData.orderedVersions
      have hpermutations :
          ((listChoices families).map fun chosen =>
              (chosen.permutations.map (DriftTreeData.node direct)).length).sum =
            (listChoices families).length * children.length.factorial := by
        apply sum_map_eq_length_mul_of_mem_eq
        intro chosen hchosen
        rw [List.length_map, List.length_permutations,
          length_eq_of_mem_listChoices hchosen]
        simp [families]
      rw [DriftTreeData.orderedVersions_node, List.length_flatMap, hpermutations,
        length_listChoices]
      simp only [families, DriftTreeData.childFactorialProduct]
      rw [hchildren]
      exact Nat.mul_comm _ _)
    (by simp)
    (fun head tail hhead htail => by
      simp only [List.map_cons, List.prod_cons]
      rw [hhead, htail])
    tree

/-- All simultaneous choices of a plane ordering at every vertex of a payoff tree. -/
noncomputable def PayoffTreeData.orderedVersions {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : List (PayoffTreeData J noiseDim) :=
  (listChoices (tree.children.map DriftTreeData.orderedVersions)).flatMap fun chosen =>
    chosen.permutations.map (PayoffTreeData.mk tree.direct)

/-- The paper weight `Q` is exactly the number of plane orderings of a payoff tree. -/
theorem PayoffTreeData.length_orderedVersions_eq_childFactorialProduct
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.orderedVersions.length = tree.childFactorialProduct := by
  let families := tree.children.map DriftTreeData.orderedVersions
  have hpermutations :
      ((listChoices families).map fun chosen =>
          (chosen.permutations.map (PayoffTreeData.mk tree.direct)).length).sum =
        (listChoices families).length * tree.children.length.factorial := by
    apply sum_map_eq_length_mul_of_mem_eq
    intro chosen hchosen
    rw [List.length_map, List.length_permutations,
      length_eq_of_mem_listChoices hchosen]
    simp [families]
  rw [PayoffTreeData.orderedVersions, List.length_flatMap, hpermutations,
    length_listChoices]
  simp only [families, PayoffTreeData.childFactorialProduct]
  rw [List.map_map]
  have hprod :
      (tree.children.map
          (List.length ∘ DriftTreeData.orderedVersions)).prod =
        (tree.children.map DriftTreeData.childFactorialProduct).prod := by
    induction tree.children with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.prod_cons, Function.comp_apply]
        rw [head.length_orderedVersions_eq_childFactorialProduct, ih]
  rw [hprod]
  exact Nat.mul_comm _ _

/-! ## Left-child/right-sibling encoding of plane payoff trees -/

/-- Encode a plane forest as a binary tree: the left branch contains the first root's children
and the right branch contains its following siblings. -/
def encodeDriftForest {J noiseDim : ℕ} :
    List (DriftTreeData J noiseDim) → BinaryTree (Finset (Index J noiseDim))
  | [] => .nil
  | .node direct children :: tail =>
      .node direct (encodeDriftForest children) (encodeDriftForest tail)
termination_by trees => sizeOf trees

/-- Decode the left-child/right-sibling representation. -/
def decodeDriftForest {J noiseDim : ℕ} :
    BinaryTree (Finset (Index J noiseDim)) → List (DriftTreeData J noiseDim)
  | .nil => []
  | .node direct children tail =>
      .node direct (decodeDriftForest children) :: decodeDriftForest tail

/-- The forest encoding loses no information. -/
theorem decodeDriftForest_encodeDriftForest {J noiseDim : ℕ}
    : ∀ trees : List (DriftTreeData J noiseDim),
      decodeDriftForest (encodeDriftForest trees) = trees
  | [] => by simp [encodeDriftForest, decodeDriftForest]
  | .node direct children :: tail => by
      rw [encodeDriftForest, decodeDriftForest,
        decodeDriftForest_encodeDriftForest children,
        decodeDriftForest_encodeDriftForest tail]
termination_by trees => sizeOf trees

/-- Plane forests inject into their binary encodings. -/
theorem encodeDriftForest_injective {J noiseDim : ℕ} :
    Function.Injective
      (encodeDriftForest : List (DriftTreeData J noiseDim) →
        BinaryTree (Finset (Index J noiseDim))) := by
  intro left right heq
  rw [← decodeDriftForest_encodeDriftForest left,
    ← decodeDriftForest_encodeDriftForest right, heq]

/-- The binary forest code has one internal node for each drift vertex. -/
theorem numNodes_encodeDriftForest {J noiseDim : ℕ}
    : ∀ trees : List (DriftTreeData J noiseDim),
      (encodeDriftForest trees).numNodes =
        (trees.map DriftTreeData.vertexCount).sum
  | [] => by simp [encodeDriftForest]
  | .node direct children :: tail => by
      rw [encodeDriftForest]
      simp only [BinaryTree.numNodes, List.map_cons, List.sum_cons,
        DriftTreeData.vertexCount]
      rw [numNodes_encodeDriftForest children, numNodes_encodeDriftForest tail]
      omega
termination_by trees => sizeOf trees

/-- The binary code of the drift forest below a payoff root. -/
def PayoffTreeData.planeCode {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    BinaryTree (Finset (Index J noiseDim)) :=
  encodeDriftForest tree.children

@[simp]
theorem PayoffTreeData.numNodes_planeCode {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) :
    tree.planeCode.numNodes + 1 = tree.vertexCount := by
  rw [PayoffTreeData.planeCode, numNodes_encodeDriftForest]
  simp [PayoffTreeData.vertexCount, Nat.add_comm]

/-- A plane payoff tree is determined by its root label and its binary forest code. -/
theorem PayoffTreeData.eq_of_direct_eq_of_planeCode_eq {J noiseDim : ℕ}
    {left right : PayoffTreeData J noiseDim} (hdirect : left.direct = right.direct)
    (hcode : left.planeCode = right.planeCode) : left = right := by
  cases left with
  | mk leftDirect leftChildren =>
      cases right with
      | mk rightDirect rightChildren =>
          simp only [PayoffTreeData.planeCode] at hcode
          have hchildren := encodeDriftForest_injective hcode
          simp only at hdirect
          subst rightDirect
          subst rightChildren
          rfl

/-- Node labels in root-left-right order. -/
def binaryTreePreorder {α : Type*} : BinaryTree α → List α
  | .nil => []
  | .node value left right =>
      value :: (binaryTreePreorder left ++ binaryTreePreorder right)

@[simp]
theorem BinaryTree.length_preorder {α : Type*} (tree : BinaryTree α) :
    (binaryTreePreorder tree).length = tree.numNodes := by
  induction tree with
  | nil => rfl
  | node value left right hleft hright =>
      simp [binaryTreePreorder, hleft, hright, Nat.add_assoc, Nat.add_comm]

@[simp]
theorem BinaryTree.numNodes_map {α β : Type*} (f : α → β) (tree : BinaryTree α) :
    (tree.map f).numNodes = tree.numNodes := by
  induction tree with
  | nil => rfl
  | node value left right hleft hright => simp [BinaryTree.map, hleft, hright]

/-- A labelled binary tree is determined by its unlabelled shape and its preorder label list. -/
theorem BinaryTree.eq_of_map_const_eq_of_preorder_eq {α : Type*}
    {left right : BinaryTree α}
    (hshape : left.map (Function.const α ()) = right.map (Function.const α ()))
    (hlabels : binaryTreePreorder left = binaryTreePreorder right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | node value rightLeft rightRight => simp [BinaryTree.map] at hshape
  | node value leftLeft leftRight ihLeft ihRight =>
      cases right with
      | nil => simp [BinaryTree.map] at hshape
      | node other rightLeft rightRight =>
          simp only [BinaryTree.map, BinaryTree.node.injEq] at hshape
          rcases hshape with ⟨-, hleftShape, hrightShape⟩
          simp only [binaryTreePreorder, List.cons.injEq] at hlabels
          rcases hlabels with ⟨hvalue, htail⟩
          have hleftLength :
              (binaryTreePreorder leftLeft).length =
                (binaryTreePreorder rightLeft).length := by
            rw [BinaryTree.length_preorder, BinaryTree.length_preorder]
            simpa using congrArg BinaryTree.numNodes hleftShape
          have hleftLabels :
              binaryTreePreorder leftLeft = binaryTreePreorder rightLeft := by
            have htaken :=
              congrArg (List.take (binaryTreePreorder leftLeft).length) htail
            simpa [hleftLength] using htaken
          have hrightLabels :
              binaryTreePreorder leftRight = binaryTreePreorder rightRight := by
            have hdropped :=
              congrArg (List.drop (binaryTreePreorder leftLeft).length) htail
            simpa [hleftLength] using hdropped
          have hleft := ihLeft hleftShape hleftLabels
          have hright := ihRight hrightShape hrightLabels
          subst other
          subst rightLeft
          subst rightRight
          rfl

/-- A plane rooted shape with `n + 1` vertices is represented by a binary tree with `n`
internal nodes (the encoded forest below its root). -/
abbrev PlaneRootedShape (n : ℕ) := ↥(BinaryTree.treesOfNumNodesEq n)

/-- A plane shape together with an injective placement of the `k` distinct nonempty direct
blocks among its `n` non-root vertices. -/
structure PlaneLabelPattern (Block : Type*) [Fintype Block] (n : ℕ) where
  shape : PlaneRootedShape n
  placement : Block ↪ Fin n

noncomputable def planeLabelPatternEquiv
    (Block : Type*) [Fintype Block] (n : ℕ) :
    PlaneLabelPattern Block n ≃ PlaneRootedShape n × (Block ↪ Fin n) where
  toFun := fun pattern => (pattern.shape, pattern.placement)
  invFun := fun code => ⟨code.1, code.2⟩
  left_inv := fun pattern => by cases pattern; rfl
  right_inv := fun code => by cases code; rfl

noncomputable instance instFintypePlaneLabelPattern
    (Block : Type*) [Fintype Block] [DecidableEq Block] (n : ℕ) :
    Fintype (PlaneLabelPattern Block n) := by
  letI : Fintype (Block ↪ Fin n) := Fintype.ofFinite _
  exact Fintype.ofEquiv (PlaneRootedShape n × (Block ↪ Fin n))
    (planeLabelPatternEquiv Block n).symm

/-- The number of shape-and-label patterns is precisely the Catalan/binomial/factorial factor
used in paper Lemma B.7. -/
theorem card_planeLabelPattern (Block : Type*) [Fintype Block] [DecidableEq Block]
    (n : ℕ) :
    Fintype.card (PlaneLabelPattern Block n) =
      catalan n * n.choose (Fintype.card Block) * (Fintype.card Block).factorial := by
  letI : Fintype (Block ↪ Fin n) := Fintype.ofFinite _
  rw [Fintype.card_congr (planeLabelPatternEquiv Block n)]
  rw [Fintype.card_prod, Fintype.card_coe,
    BinaryTree.treesOfNumNodesEq_card_eq_catalan, Fintype.card_embedding_eq,
    Fintype.card_fin, Nat.descFactorial_eq_factorial_mul_choose]
  ring

/-- Summing all pattern types with fewer than `2k` non-root vertices gives the numerical
right-hand side in Lemma B.7. -/
theorem sum_card_planeLabelPattern_le_sixtyFour_pow_factorial
    (Block : Type*) [Fintype Block] [DecidableEq Block]
    (k : ℕ) (hcard : Fintype.card Block = k) :
    (∑ n ∈ Finset.range (2 * k), Fintype.card (PlaneLabelPattern Block n)) ≤
      64 ^ k * k.factorial := by
  simp_rw [card_planeLabelPattern, hcard]
  rw [← Finset.sum_mul]
  exact catalan_choose_factorial_sum_le_weightedPatternBound k

/-- Occurrences of local plane orderings in a finite family of canonical payoff trees.  Its
cardinality is the weighted sum `∑ Q(𝔗)`. -/
abbrev OrderedPayoffOccurrence {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim)) :=
  Σ tree : ↥family, Fin tree.1.childFactorialProduct

/-- All Catalan shape-and-label patterns allowed by the vertex bound in Lemma B.6. -/
abbrev BoundedPlaneLabelPattern (Block : Type*) [Fintype Block] (k : ℕ) :=
  Σ n : Fin (2 * k), PlaneLabelPattern Block n

/-- Abstract final step of paper Lemma B.7.  Once the ordered tree occurrences are injected into
their Catalan shape-and-label patterns, their weighted count is at most `64^k k!`. -/
theorem weighted_payoffTree_count_of_planeEncoding
    {J noiseDim : ℕ} (family : Finset (PayoffTreeData J noiseDim))
    (Block : Type*) [Fintype Block] [DecidableEq Block]
    (k : ℕ) (hcard : Fintype.card Block = k)
    (encoding : OrderedPayoffOccurrence family ↪ BoundedPlaneLabelPattern Block k) :
    ∑ tree ∈ family, tree.childFactorialProduct ≤ 64 ^ k * k.factorial := by
  letI (tree : ↥family) : Fintype (Fin tree.1.childFactorialProduct) :=
    inferInstance
  letI (n : Fin (2 * k)) : Fintype (PlaneLabelPattern Block n.1) :=
    instFintypePlaneLabelPattern Block n.1
  calc
    ∑ tree ∈ family, tree.childFactorialProduct =
        Fintype.card (OrderedPayoffOccurrence family) := by
      rw [Fintype.card_sigma]
      simp_rw [Fintype.card_fin]
      rw [Finset.sum_coe_sort]
    _ ≤ Fintype.card (BoundedPlaneLabelPattern Block k) :=
      Fintype.card_le_of_embedding encoding
    _ = ∑ n ∈ Finset.range (2 * k),
          Fintype.card (PlaneLabelPattern Block n) := by
      rw [Fintype.card_sigma]
      simpa using Fin.sum_univ_eq_sum_range
        (fun n : ℕ => Fintype.card (PlaneLabelPattern Block n)) (2 * k)
    _ ≤ 64 ^ k * k.factorial :=
      sum_card_planeLabelPattern_le_sixtyFour_pow_factorial Block k hcard

end

end TimeDependentLattice.Trees
