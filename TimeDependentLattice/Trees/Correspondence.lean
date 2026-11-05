/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Data.Finset.Sort
import TimeDependentLattice.Trees.ExpansionChoice

/-!
# Correspondence between expansion choices and timed payoff trees

This file constructs the checked bijection used in Lemma `lem:correspondence`.  Expansion choices
use genuinely unordered `Finpartition` blocks.  The tree representation enumerates those blocks
in increasing order of their least coordinate, which is well-defined because distinct partition
blocks are nonempty and disjoint.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open TimeDependentLattice.BrownianBridge

/-- The least coordinate rank of a partition block. -/
def partitionBlockMinRank {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (partition : Finpartition support) (block : partition.parts) : ℕ :=
  (block.1.image coordinateRank).min'
    ((Finset.nonempty_iff_ne_empty.mpr (partition.ne_bot block.2)).image coordinateRank)

/-- Distinct partition blocks have distinct least coordinates. -/
theorem partitionBlockMinRank_injective {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    Function.Injective (partitionBlockMinRank partition) := by
  intro left right heq
  have hleftNonempty : left.1.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (partition.ne_bot left.2)
  have hrightNonempty : right.1.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (partition.ne_bot right.2)
  have hleftMin := Finset.min'_mem (left.1.image coordinateRank)
    (hleftNonempty.image coordinateRank)
  have hrightMin := Finset.min'_mem (right.1.image coordinateRank)
    (hrightNonempty.image coordinateRank)
  rcases Finset.mem_image.mp hleftMin with ⟨leftCoordinate, hleftMem, hleftRank⟩
  rcases Finset.mem_image.mp hrightMin with ⟨rightCoordinate, hrightMem, hrightRank⟩
  have hcoordinate : leftCoordinate = rightCoordinate := coordinateRank_injective (by
    rw [hleftRank, hrightRank]
    exact heq)
  apply Subtype.ext
  exact partition.eq_of_mem_parts left.2 right.2 hleftMem (hcoordinate ▸ hrightMem)

/-- The canonical comparison on partition blocks, induced by their least coordinate ranks. -/
def partitionBlockLE {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    partition.parts → partition.parts → Prop :=
  fun left right => partitionBlockMinRank partition left ≤ partitionBlockMinRank partition right

noncomputable instance partitionBlockLE_decidable {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    DecidableRel (partitionBlockLE partition) :=
  Classical.decRel _

instance partitionBlockLE_isTrans {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    IsTrans partition.parts (partitionBlockLE partition) :=
  ⟨fun _ _ _ hab hbc => hab.trans hbc⟩

instance partitionBlockLE_isAntisymm {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    Std.Antisymm (partitionBlockLE partition) :=
  ⟨fun _ _ hab hba => partitionBlockMinRank_injective partition (Nat.le_antisymm hab hba)⟩

instance partitionBlockLE_isTotal {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    Std.Total (partitionBlockLE partition) :=
  ⟨fun left right => Nat.le_total (partitionBlockMinRank partition left)
    (partitionBlockMinRank partition right)⟩

/-- The unordered blocks of a finite partition, canonically enumerated by least coordinate. -/
noncomputable def orderedPartitionBlocks {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    List partition.parts :=
  Finset.univ.sort (partitionBlockLE partition)

@[simp]
theorem orderedPartitionBlocks_length {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    (orderedPartitionBlocks partition).length = partition.parts.card := by
  simp [orderedPartitionBlocks]

@[simp]
theorem mem_orderedPartitionBlocks {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support)
    (block : partition.parts) : block ∈ orderedPartitionBlocks partition := by
  simp [orderedPartitionBlocks]

theorem orderedPartitionBlocks_nodup {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    (orderedPartitionBlocks partition).Nodup := by
  simp [orderedPartitionBlocks]

/-- Positions in the canonical block list are equivalent to the unordered partition parts. -/
noncomputable def orderedPartitionBlocksEquiv {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    Fin (orderedPartitionBlocks partition).length ≃ partition.parts :=
  (orderedPartitionBlocks_nodup partition).getEquivOfForallMemList
    (orderedPartitionBlocks partition) (mem_orderedPartitionBlocks partition)

@[simp]
theorem orderedPartitionBlocksEquiv_apply {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support)
    (i : Fin (orderedPartitionBlocks partition).length) :
    orderedPartitionBlocksEquiv partition i =
      (orderedPartitionBlocks partition).get i := by
  rfl

/-- The canonical block enumeration is strictly increasing in its least coordinates. -/
theorem orderedPartitionBlocks_pairwise_min_lt {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    (orderedPartitionBlocks partition).Pairwise
      (fun left right =>
        partitionBlockMinRank partition left < partitionBlockMinRank partition right) := by
  have hpair : (orderedPartitionBlocks partition).Pairwise
      (partitionBlockLE partition) := by
    exact Finset.pairwise_sort (Finset.univ : Finset partition.parts)
      (partitionBlockLE partition)
  have hleRanks :
      ((orderedPartitionBlocks partition).map (partitionBlockMinRank partition)).Pairwise
        (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hpair
  have hnodupRanks :
      ((orderedPartitionBlocks partition).map
        (partitionBlockMinRank partition)).Nodup :=
    (orderedPartitionBlocks_nodup partition).map
      (partitionBlockMinRank_injective partition)
  have hltRanks := hleRanks.sortedLE.sortedLT_of_nodup hnodupRanks
  simpa only [List.pairwise_map] using hltRanks.pairwise

/-- For a nonempty partition block, its `WithTop` minimum is the finite minimum rank used for
canonical sorting. -/
theorem partitionBlock_min_eq_coe_minRank {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support)
    (block : partition.parts) :
    (block.1.image coordinateRank).min =
      (partitionBlockMinRank partition block : WithTop ℕ) := by
  exact (Finset.coe_min'
    ((Finset.nonempty_iff_ne_empty.mpr (partition.ne_bot block.2)).image coordinateRank)).symm

/-- Membership in the union of child supports. -/
theorem mem_childrenSupport_iff {J noiseDim : ℕ} {j : Index J noiseDim}
    {children : List (DriftTreeData J noiseDim)} :
    j ∈ childrenSupport children ↔
      ∃ child ∈ children, j ∈ child.support := by
  induction children with
  | nil => simp
  | cons head tail ih =>
      rw [childrenSupport_cons, Finset.mem_union, ih]
      simp

/-- Canonically enumerating all blocks and replacing each block by an object with that support
preserves their union. -/
theorem childrenSupport_map_orderedPartitionBlocks {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support)
    (trees : ∀ _block : partition.parts, DriftTreeData J noiseDim)
    (htrees : ∀ block, (trees block).support = block.1) :
    childrenSupport ((orderedPartitionBlocks partition).map trees) = support := by
  apply Finset.ext
  intro j
  rw [mem_childrenSupport_iff]
  constructor
  · rintro ⟨tree, htree, hj⟩
    rcases List.mem_map.mp htree with ⟨block, _, rfl⟩
    rw [htrees block] at hj
    exact partition.le block.2 hj
  · intro hj
    obtain ⟨part, hpart, hjpart⟩ := partition.exists_mem hj
    let block : partition.parts := ⟨part, hpart⟩
    refine ⟨trees block, List.mem_map.mpr ⟨block, ?_, rfl⟩, ?_⟩
    · exact mem_orderedPartitionBlocks partition block
    · simpa [htrees block] using hjpart

/-- A tree occurring in a valid aligned child list has a corresponding valid time datum. -/
theorem DriftTimeData.exists_of_validChildren_of_mem {J noiseDim parentTime : ℕ}
    {trees : List (DriftTreeData J noiseDim)} {assignments : List DriftTimeData}
    (hvalid : DriftTimeData.ValidChildren parentTime trees assignments)
    {tree : DriftTreeData J noiseDim} (htree : tree ∈ trees) :
    ∃ assignment ∈ assignments, assignment.Valid parentTime tree := by
  induction trees generalizing assignments with
  | nil => simp at htree
  | cons head tail ih =>
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          rcases List.mem_cons.mp htree with rfl | htail
          · exact ⟨assignment, by simp, hvalid.1⟩
          · obtain ⟨found, hfound, hfoundValid⟩ := ih hvalid.2 htail
            exact ⟨found, by simp [hfound], hfoundValid⟩

/-- Valid aligned child data remain valid when both lists are read at the same position. -/
theorem DriftTimeData.validChildren_get {J noiseDim parentTime : ℕ}
    {trees : List (DriftTreeData J noiseDim)} {assignments : List DriftTimeData}
    (hvalid : DriftTimeData.ValidChildren parentTime trees assignments)
    (index : Fin trees.length) :
    let assignmentIndex : Fin assignments.length :=
      ⟨index.val, by rw [← DriftTimeData.validChildren_length_eq hvalid]; exact index.isLt⟩
    (assignments.get assignmentIndex).Valid parentTime (trees.get index) := by
  induction trees generalizing assignments with
  | nil => exact Fin.elim0 index
  | cons tree trees ih =>
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          refine Fin.cases ?_ (fun tailIndex => ?_) index
          · simpa using hvalid.1
          · simpa using ih hvalid.2 tailIndex

private theorem finsetList_nodup_of_pairwise_disjoint {α : Type*}
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
        exact (hnonempty head (by simp)).ne_empty (disjoint_self.mp hself)
      · apply ih hdisjoint.2
        intro support hsupport
        exact hnonempty support (by simp [hsupport])

/-- The child-support list is duplicate-free when the supports are pairwise disjoint and
nonempty. -/
theorem childSupports_nodup_of_disjoint {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim))
    (hdisjoint : childrenDisjoint children)
    (hnonempty : ∀ child ∈ children, child.support.Nonempty) :
    (childSupports children).Nodup := by
  apply finsetList_nodup_of_pairwise_disjoint _ hdisjoint
  intro support hsupport
  rcases List.mem_map.mp hsupport with ⟨child, hchild, rfl⟩
  exact hnonempty child hchild

/-- Every direct child is structurally smaller than its parent node. -/
theorem DriftTreeData.sizeOf_child_lt {J noiseDim : ℕ}
    (direct : Finset (Index J noiseDim)) (children : List (DriftTreeData J noiseDim))
    (child : DriftTreeData J noiseDim) (hchild : child ∈ children) :
    sizeOf child < sizeOf (DriftTreeData.node direct children) := by
  have hlist := List.sizeOf_lt_of_mem hchild
  simp_all
  omega

/-- The parts of the recovered child partition are counted by the original child list. -/
theorem DriftTreeData.childPartition_card_eq_children_length {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.childPartition hvalid).parts.card = tree.children.length := by
  cases tree with
  | node direct children =>
      simp only [DriftTreeData.Valid] at hvalid
      rw [DriftTreeData.childPartition_parts]
      rw [List.toFinset_card_of_nodup]
      · simp [childSupports]
      · apply childSupports_nodup_of_disjoint
        · exact hvalid.2.2.1
        · intro child hchild
          exact child.valid_support_nonempty (hvalid.2.2.2.2 child hchild)

/-- Every recovered partition block is the support of an actual direct child. -/
theorem DriftTreeData.exists_child_of_mem_childPartition {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid)
    (block : (tree.childPartition hvalid).parts) :
    ∃ child ∈ tree.children, child.support = block.1 := by
  have hpart : block.1 ∈ (childSupports tree.children).toFinset := by
    simpa only [DriftTreeData.childPartition_parts] using block.2
  have hlist : block.1 ∈ childSupports tree.children := by
    simpa using hpart
  rcases List.mem_map.mp hlist with ⟨child, hchild, hsupport⟩
  exact ⟨child, hchild, hsupport⟩

/-- Every payoff-root partition block is the support of an actual direct child. -/
theorem LabelledPayoffTree.exists_child_of_mem_childPartition {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u)
    (block : tree.childPartition.parts) :
    ∃ child ∈ tree.data.children, child.support = block.1 := by
  have hpart : block.1 ∈ (childSupports tree.data.children).toFinset := by
    simpa only [LabelledPayoffTree.childPartition_parts] using block.2
  have hlist : block.1 ∈ childSupports tree.data.children := by
    simpa using hpart
  rcases List.mem_map.mp hlist with ⟨child, hchild, hsupport⟩
  exact ⟨child, hchild, hsupport⟩

/-- The original child list, lifted to the subtype of recovered partition blocks. -/
noncomputable def DriftTreeData.childBlocks {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    List (tree.childPartition hvalid).parts :=
  tree.children.attach.map fun child =>
    ⟨child.1.support, by
      rw [DriftTreeData.childPartition_parts]
      rw [List.mem_toFinset]
      exact List.mem_map.mpr ⟨child.1, child.2, rfl⟩⟩

@[simp]
theorem DriftTreeData.childBlocks_values {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.childBlocks hvalid).map Subtype.val = childSupports tree.children := by
  simp [DriftTreeData.childBlocks, childSupports, Function.comp_def]

theorem DriftTreeData.childBlocks_nodup {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.childBlocks hvalid).Nodup := by
  cases tree with
  | node direct children =>
      simp only [DriftTreeData.Valid] at hvalid
      apply (List.nodup_map_iff Subtype.val_injective).mp
      rw [DriftTreeData.childBlocks_values]
      apply childSupports_nodup_of_disjoint
      · exact hvalid.2.2.1
      · intro child hchild
        exact child.valid_support_nonempty (hvalid.2.2.2.2 child hchild)

theorem DriftTreeData.childBlocks_toFinset {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.childBlocks hvalid).toFinset = Finset.univ := by
  apply Finset.ext
  intro block
  simp only [Finset.mem_univ, iff_true]
  have hpart : block.1 ∈ (childSupports tree.children).toFinset := by
    simpa only [DriftTreeData.childPartition_parts] using block.2
  have hlist : block.1 ∈ childSupports tree.children := by simpa using hpart
  rcases List.mem_map.mp hlist with ⟨child, hchild, hsupport⟩
  rw [List.mem_toFinset, DriftTreeData.childBlocks]
  apply List.mem_map.mpr
  refine ⟨⟨child, hchild⟩, by simp, ?_⟩
  exact Subtype.ext hsupport

/-- Validity's canonical sibling order agrees with the least-rank ordering used by the forward
map.  Thus recovering a partition and sorting its blocks does not permute the original list. -/
theorem DriftTreeData.ordered_childPartition_eq_childBlocks {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    orderedPartitionBlocks (tree.childPartition hvalid) = tree.childBlocks hvalid := by
  have hcanonical : childrenCanonical tree.children := by
    cases tree with
    | node direct children =>
        simp only [DriftTreeData.Valid] at hvalid
        exact hvalid.2.2.2.1
  have hattach : tree.children.attach.Pairwise
      (fun left right => left.1.supportKey < right.1.supportKey) := by
    simpa [childrenCanonical, List.pairwise_iff_getElem] using hcanonical
  have hblocks : (tree.childBlocks hvalid).Pairwise
      (partitionBlockLE (tree.childPartition hvalid)) := by
    rw [DriftTreeData.childBlocks, List.pairwise_map]
    apply hattach.imp
    intro left right hlt
    unfold partitionBlockLE
    let leftBlock : (tree.childPartition hvalid).parts :=
      ⟨left.1.support, by
        rw [DriftTreeData.childPartition_parts, List.mem_toFinset]
        exact List.mem_map.mpr ⟨left.1, left.2, rfl⟩⟩
    let rightBlock : (tree.childPartition hvalid).parts :=
      ⟨right.1.support, by
        rw [DriftTreeData.childPartition_parts, List.mem_toFinset]
        exact List.mem_map.mpr ⟨right.1, right.2, rfl⟩⟩
    change partitionBlockMinRank (tree.childPartition hvalid) leftBlock ≤
      partitionBlockMinRank (tree.childPartition hvalid) rightBlock
    have hkey :
        (left.1.support.image coordinateRank).min <
          (right.1.support.image coordinateRank).min := by
      simpa [DriftTreeData.supportKey] using hlt
    change (leftBlock.1.image coordinateRank).min <
      (rightBlock.1.image coordinateRank).min at hkey
    rw [partitionBlock_min_eq_coe_minRank (tree.childPartition hvalid) leftBlock,
      partitionBlock_min_eq_coe_minRank (tree.childPartition hvalid) rightBlock] at hkey
    exact Nat.le_of_lt (WithTop.coe_lt_coe.mp hkey)
  have hsort :=
    (List.toFinset_sort (partitionBlockLE (tree.childPartition hvalid))
      (tree.childBlocks_nodup hvalid)).2 hblocks
  rw [tree.childBlocks_toFinset hvalid] at hsort
  exact hsort

/-- The position of a recovered block in the original canonical child list. -/
noncomputable def DriftTreeData.childBlockIndex {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid)
    (block : (tree.childPartition hvalid).parts) : Fin tree.children.length := by
  let index := tree.childBlocks hvalid |>.idxOf block
  have hmem : block ∈ tree.childBlocks hvalid := by
    rw [← List.mem_toFinset, tree.childBlocks_toFinset hvalid]
    simp
  have hlt : index < (tree.childBlocks hvalid).length := by
    exact List.idxOf_lt_length_of_mem hmem
  exact ⟨index, by simpa [DriftTreeData.childBlocks] using hlt⟩

/-- Looking up a child by its recovered block returns a tree with exactly that support. -/
theorem DriftTreeData.childBlockIndex_support {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid)
    (block : (tree.childPartition hvalid).parts) :
    (tree.children.get (tree.childBlockIndex hvalid block)).support = block.1 := by
  have hmem : block ∈ tree.childBlocks hvalid := by
    rw [← List.mem_toFinset, tree.childBlocks_toFinset hvalid]
    simp
  have hlt := List.idxOf_lt_length_of_mem hmem
  let index : Fin (tree.childBlocks hvalid).length :=
    ⟨(tree.childBlocks hvalid).idxOf block, hlt⟩
  have hget : (tree.childBlocks hvalid).get index = block := by
    simp [index, List.get_eq_getElem]
  have hchildLt : index.val < tree.children.length := by
    simpa [DriftTreeData.childBlocks] using index.isLt
  have hlookup := congrArg (fun list => list[index.val]?)
    (tree.childBlocks_values hvalid)
  simp only [childSupports] at hlookup
  have hleftMapLt : index.val <
      ((tree.childBlocks hvalid).map Subtype.val).length := by
    simp
  have hrightMapLt : index.val <
      (tree.children.map DriftTreeData.support).length := by
    simpa using hchildLt
  rw [List.getElem?_eq_getElem hleftMapLt,
    List.getElem?_eq_getElem hrightMapLt] at hlookup
  simp only [List.getElem_map] at hlookup
  have hblockValue : ((tree.childBlocks hvalid).get index).1 = block.1 :=
    congrArg Subtype.val hget
  have hvalue : (tree.children[index.val]).support = block.1 := by
    rw [← hblockValue]
    simpa [List.get_eq_getElem] using hlookup.symm
  simpa [DriftTreeData.childBlockIndex, index] using hvalue

@[simp]
theorem DriftTreeData.childBlockIndex_get_val {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid)
    (index : Fin (tree.childBlocks hvalid).length) :
    (tree.childBlockIndex hvalid ((tree.childBlocks hvalid).get index)).val = index.val := by
  change (tree.childBlocks hvalid).idxOf
    ((tree.childBlocks hvalid).get index) = index.val
  exact List.get_idxOf (tree.childBlocks_nodup hvalid) index

/-- Looking up every recovered block reproduces the original drift-child list pointwise. -/
theorem DriftTreeData.map_childBlockIndex_get {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.childBlocks hvalid).map
      (fun block => tree.children.get (tree.childBlockIndex hvalid block)) =
        tree.children := by
  apply List.ext_get
  · simp [DriftTreeData.childBlocks]
  · intro index hleft hright
    let blockIndex : Fin (tree.childBlocks hvalid).length :=
      ⟨index, by simpa using hleft⟩
    have hindex := tree.childBlockIndex_get_val hvalid blockIndex
    simp only [List.get_eq_getElem, List.getElem_map]
    apply congrArg tree.children.get
    apply Fin.ext
    simpa [blockIndex] using hindex

/-- Reading the aligned time list at the recovered child positions restores the original list. -/
theorem DriftTreeData.map_childBlockIndex_get_time {J noiseDim parentTime : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid)
    (assignments : List DriftTimeData)
    (htime : DriftTimeData.ValidChildren parentTime tree.children assignments) :
    (tree.childBlocks hvalid).map (fun block =>
      let index := tree.childBlockIndex hvalid block
      let timeIndex : Fin assignments.length :=
        ⟨index.val, by
          rw [← DriftTimeData.validChildren_length_eq htime]
          exact index.isLt⟩
      assignments.get timeIndex) = assignments := by
  apply List.ext_get
  · simpa [DriftTreeData.childBlocks] using
      DriftTimeData.validChildren_length_eq htime
  · intro index hleft hright
    let blockIndex : Fin (tree.childBlocks hvalid).length :=
      ⟨index, by simpa using hleft⟩
    have hindex := tree.childBlockIndex_get_val hvalid blockIndex
    simp only [List.get_eq_getElem, List.getElem_map]
    apply congrArg assignments.get
    apply Fin.ext
    simpa [blockIndex] using hindex

/-- The payoff root's child list, lifted to its recovered partition blocks. -/
noncomputable def LabelledPayoffTree.childBlocks {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    List tree.childPartition.parts :=
  tree.data.children.attach.map fun child =>
    ⟨child.1.support, by
      rw [LabelledPayoffTree.childPartition_parts, List.mem_toFinset]
      exact List.mem_map.mpr ⟨child.1, child.2, rfl⟩⟩

@[simp]
theorem LabelledPayoffTree.childBlocks_values {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    tree.childBlocks.map Subtype.val = childSupports tree.data.children := by
  simp [LabelledPayoffTree.childBlocks, childSupports, Function.comp_def]

theorem LabelledPayoffTree.childBlocks_nodup {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    tree.childBlocks.Nodup := by
  apply (List.nodup_map_iff Subtype.val_injective).mp
  rw [tree.childBlocks_values]
  exact childSupports_nodup_of_disjoint tree.data.children tree.valid.2.2.2.1
    tree.child_support_nonempty

theorem LabelledPayoffTree.childBlocks_toFinset {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    tree.childBlocks.toFinset = Finset.univ := by
  apply Finset.ext
  intro block
  simp only [Finset.mem_univ, iff_true]
  have hpart : block.1 ∈ (childSupports tree.data.children).toFinset := by
    simpa only [LabelledPayoffTree.childPartition_parts] using block.2
  have hlist : block.1 ∈ childSupports tree.data.children := by simpa using hpart
  rcases List.mem_map.mp hlist with ⟨child, hchild, hsupport⟩
  rw [List.mem_toFinset, LabelledPayoffTree.childBlocks]
  apply List.mem_map.mpr
  refine ⟨⟨child, hchild⟩, by simp, ?_⟩
  exact Subtype.ext hsupport

/-- The canonical ordering at the payoff root agrees with sorting the recovered partition. -/
theorem LabelledPayoffTree.ordered_childPartition_eq_childBlocks {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    orderedPartitionBlocks tree.childPartition = tree.childBlocks := by
  have hcanonical : childrenCanonical tree.data.children := tree.valid.2.2.2.2.1
  have hattach : tree.data.children.attach.Pairwise
      (fun left right => left.1.supportKey < right.1.supportKey) := by
    simpa [childrenCanonical, List.pairwise_iff_getElem] using hcanonical
  have hblocks : tree.childBlocks.Pairwise
      (partitionBlockLE tree.childPartition) := by
    rw [LabelledPayoffTree.childBlocks, List.pairwise_map]
    apply hattach.imp
    intro left right hlt
    unfold partitionBlockLE
    let leftBlock : tree.childPartition.parts :=
      ⟨left.1.support, by
        rw [LabelledPayoffTree.childPartition_parts, List.mem_toFinset]
        exact List.mem_map.mpr ⟨left.1, left.2, rfl⟩⟩
    let rightBlock : tree.childPartition.parts :=
      ⟨right.1.support, by
        rw [LabelledPayoffTree.childPartition_parts, List.mem_toFinset]
        exact List.mem_map.mpr ⟨right.1, right.2, rfl⟩⟩
    change partitionBlockMinRank tree.childPartition leftBlock ≤
      partitionBlockMinRank tree.childPartition rightBlock
    have hkey :
        (left.1.support.image coordinateRank).min <
          (right.1.support.image coordinateRank).min := by
      simpa [DriftTreeData.supportKey] using hlt
    change (leftBlock.1.image coordinateRank).min <
      (rightBlock.1.image coordinateRank).min at hkey
    rw [partitionBlock_min_eq_coe_minRank tree.childPartition leftBlock,
      partitionBlock_min_eq_coe_minRank tree.childPartition rightBlock] at hkey
    exact Nat.le_of_lt (WithTop.coe_lt_coe.mp hkey)
  have hsort :=
    (List.toFinset_sort (partitionBlockLE tree.childPartition)
      tree.childBlocks_nodup).2 hblocks
  rw [tree.childBlocks_toFinset] at hsort
  exact hsort

/-- The position of a payoff-root partition block in its canonical child list. -/
noncomputable def LabelledPayoffTree.childBlockIndex {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u)
    (block : tree.childPartition.parts) : Fin tree.data.children.length := by
  let index := tree.childBlocks.idxOf block
  have hmem : block ∈ tree.childBlocks := by
    rw [← List.mem_toFinset, tree.childBlocks_toFinset]
    simp
  have hlt : index < tree.childBlocks.length :=
    List.idxOf_lt_length_of_mem hmem
  exact ⟨index, by simpa [LabelledPayoffTree.childBlocks] using hlt⟩

/-- Looking up a payoff child by its recovered block returns that block as its support. -/
theorem LabelledPayoffTree.childBlockIndex_support {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u)
    (block : tree.childPartition.parts) :
    (tree.data.children.get (tree.childBlockIndex block)).support = block.1 := by
  have hmem : block ∈ tree.childBlocks := by
    rw [← List.mem_toFinset, tree.childBlocks_toFinset]
    simp
  have hlt := List.idxOf_lt_length_of_mem hmem
  let index : Fin tree.childBlocks.length :=
    ⟨tree.childBlocks.idxOf block, hlt⟩
  have hget : tree.childBlocks.get index = block := by
    simp [index, List.get_eq_getElem]
  have hchildLt : index.val < tree.data.children.length := by
    simpa [LabelledPayoffTree.childBlocks] using index.isLt
  have hlookup := congrArg (fun list => list[index.val]?) tree.childBlocks_values
  simp only [childSupports] at hlookup
  have hleftMapLt : index.val < (tree.childBlocks.map Subtype.val).length := by
    simp
  have hrightMapLt : index.val <
      (tree.data.children.map DriftTreeData.support).length := by
    simpa using hchildLt
  rw [List.getElem?_eq_getElem hleftMapLt,
    List.getElem?_eq_getElem hrightMapLt] at hlookup
  simp only [List.getElem_map] at hlookup
  have hblockValue : (tree.childBlocks.get index).1 = block.1 :=
    congrArg Subtype.val hget
  have hvalue : (tree.data.children[index.val]).support = block.1 := by
    rw [← hblockValue]
    simpa [List.get_eq_getElem] using hlookup.symm
  simpa [LabelledPayoffTree.childBlockIndex, index] using hvalue

@[simp]
theorem LabelledPayoffTree.childBlockIndex_get_val {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u)
    (index : Fin tree.childBlocks.length) :
    (tree.childBlockIndex (tree.childBlocks.get index)).val = index.val := by
  change tree.childBlocks.idxOf (tree.childBlocks.get index) = index.val
  exact List.get_idxOf tree.childBlocks_nodup index

/-- Looking up every recovered root block reproduces the original payoff-child list. -/
theorem LabelledPayoffTree.map_childBlockIndex_get {J noiseDim : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u) :
    tree.childBlocks.map
      (fun block => tree.data.children.get (tree.childBlockIndex block)) =
        tree.data.children := by
  apply List.ext_get
  · simp [LabelledPayoffTree.childBlocks]
  · intro index hleft hright
    let blockIndex : Fin tree.childBlocks.length :=
      ⟨index, by simpa using hleft⟩
    have hindex := tree.childBlockIndex_get_val blockIndex
    simp only [List.get_eq_getElem, List.getElem_map]
    apply congrArg tree.data.children.get
    apply Fin.ext
    simpa [blockIndex] using hindex

/-- Reading the payoff-root time list at recovered child positions restores that list. -/
theorem LabelledPayoffTree.map_childBlockIndex_get_time {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} (tree : LabelledPayoffTree J noiseDim u)
    (assignments : List DriftTimeData)
    (htime : DriftTimeData.ValidChildren m tree.data.children assignments) :
    tree.childBlocks.map (fun block =>
      let index := tree.childBlockIndex block
      let timeIndex : Fin assignments.length :=
        ⟨index.val, by
          rw [← DriftTimeData.validChildren_length_eq htime]
          exact index.isLt⟩
      assignments.get timeIndex) = assignments := by
  apply List.ext_get
  · simpa [LabelledPayoffTree.childBlocks] using
      DriftTimeData.validChildren_length_eq htime
  · intro index hleft hright
    let blockIndex : Fin tree.childBlocks.length :=
      ⟨index, by simpa using hleft⟩
    have hindex := tree.childBlockIndex_get_val blockIndex
    simp only [List.get_eq_getElem, List.getElem_map]
    apply congrArg assignments.get
    apply Fin.ext
    simpa [blockIndex] using hindex

private theorem list_prod_eq_of_map_fst_snd_eq {A B : Type*}
    {left right : List (A × B)}
    (hfst : left.map Prod.fst = right.map Prod.fst)
    (hsnd : left.map Prod.snd = right.map Prod.snd) : left = right := by
  induction left generalizing right with
  | nil => simpa using hfst
  | cons head tail ih =>
      cases right with
      | nil => simp at hfst
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at hfst hsnd
          have hhead : head = other := Prod.ext hfst.1 hsnd.1
          subst other
          exact congrArg (head :: ·) (ih hfst.2 hsnd.2)

private theorem apply_eq_of_map_eq_of_mem {A B : Type*}
    (items : List A) (left right : A → B)
    (hmaps : items.map left = items.map right) {item : A}
    (hitem : item ∈ items) : left item = right item := by
  induction items with
  | nil => simp at hitem
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at hmaps
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact hmaps.1
      · exact ih hmaps.2 htail

private theorem finpartition_heq_of_parts_eq {A : Type*}
    [Lattice A] [OrderBot A] {a b : A}
    (left : Finpartition a) (right : Finpartition b)
    (hparts : left.parts = right.parts) : HEq left right := by
  have hab : a = b := by
    rw [← left.sup_parts, ← right.sup_parts, hparts]
  subst b
  exact heq_of_eq (Finpartition.ext hparts)

namespace DriftExpansionChoice

/-- Convert one unordered recursive expansion choice into a tree and a time assignment.  At every
higher-order vertex, the partition blocks are put into the canonical least-rank order. -/
def toTreeTime {J noiseDim parentTime : ℕ} {support : Finset (Index J noiseDim)} :
    DriftExpansionChoice J noiseDim parentTime support →
      DriftTreeData J noiseDim × DriftTimeData
  | .singleton time j _ =>
      (.node {j} [], .node time [])
  | .higher time _ direct _ partition _ children =>
      let childPairs := (orderedPartitionBlocks partition).map fun block =>
        toTreeTime (children block)
      (.node direct (childPairs.map Prod.fst),
        .node time (childPairs.map Prod.snd))

@[simp]
theorem toTreeTime_cast_support {J noiseDim parentTime : ℕ}
    {left right : Finset (Index J noiseDim)} (h : left = right)
    (choice : DriftExpansionChoice J noiseDim parentTime left) :
    (h ▸ choice).toTreeTime = choice.toTreeTime := by
  subst right
  rfl

/-- The canonical drift tree associated with a recursive expansion choice. -/
def toTree {J noiseDim parentTime : ℕ} {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    DriftTreeData J noiseDim :=
  choice.toTreeTime.1

/-- The time data associated with a recursive expansion choice. -/
def toTime {J noiseDim parentTime : ℕ} {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) : DriftTimeData :=
  choice.toTreeTime.2

@[simp]
theorem singleton_toTree {J noiseDim parentTime time : ℕ}
    (j : Index J noiseDim) (htime : time < parentTime) :
    (DriftExpansionChoice.singleton time j htime).toTree = .node {j} [] :=
  rfl

@[simp]
theorem singleton_toTime {J noiseDim parentTime time : ℕ}
    (j : Index J noiseDim) (htime : time < parentTime) :
    (DriftExpansionChoice.singleton time j htime).toTime = .node time [] :=
  rfl

@[simp]
theorem higher_toTree {J noiseDim parentTime time : ℕ}
    {support : Finset (Index J noiseDim)} (htime : time < parentTime)
    (direct : Finset (Index J noiseDim)) (hsubset : direct ⊆ support)
    (partition : Finpartition (support \ direct))
    (horder : 2 ≤ direct.card + partition.parts.card)
    (children : ∀ block : partition.parts,
      DriftExpansionChoice J noiseDim time block.1) :
    (DriftExpansionChoice.higher time htime direct hsubset partition horder children).toTree =
      .node direct
        ((orderedPartitionBlocks partition).map fun block => (children block).toTree) := by
  simp [toTree, toTreeTime, Function.comp_def]

@[simp]
theorem higher_toTime {J noiseDim parentTime time : ℕ}
    {support : Finset (Index J noiseDim)} (htime : time < parentTime)
    (direct : Finset (Index J noiseDim)) (hsubset : direct ⊆ support)
    (partition : Finpartition (support \ direct))
    (horder : 2 ≤ direct.card + partition.parts.card)
    (children : ∀ block : partition.parts,
      DriftExpansionChoice J noiseDim time block.1) :
    (DriftExpansionChoice.higher time htime direct hsubset partition horder children).toTime =
      .node time
        ((orderedPartitionBlocks partition).map fun block => (children block).toTime) := by
  simp [toTime, toTreeTime, Function.comp_def]

/-- The canonical tree constructed from a recursive choice carries exactly the coordinate set
indexing that choice. -/
theorem toTree_support {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    choice.toTree.support = support := by
  induction choice with
  | singleton time j htime => simp
  | higher time htime direct hsubset partition horder children ih =>
      rw [higher_toTree, DriftTreeData.support_node]
      rw [childrenSupport_map_orderedPartitionBlocks partition
        (fun block => (children block).toTree) ih]
      exact Finset.union_sdiff_of_subset hsubset

/-- The forward construction simultaneously produces a valid drift tree and time data of exactly
the same recursive shape. -/
theorem toTree_valid_and_toTime_valid {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    choice.toTree.Valid ∧ choice.toTime.Valid parentTime choice.toTree := by
  induction choice with
  | singleton time j htime =>
      constructor
      · exact DriftTreeData.singletonLeaf_valid j
      · rw [singleton_toTree, singleton_toTime]
        simp only [DriftTimeData.Valid]
        exact ⟨htime, by simp [DriftTimeData.ValidChildren]⟩
  | higher time htime direct hsubset partition horder children ih =>
      rw [higher_toTree, higher_toTime]
      let blocks := orderedPartitionBlocks partition
      have hchildrenSupport :=
        childrenSupport_map_orderedPartitionBlocks partition
          (fun block => (children block).toTree)
          (fun block => toTree_support (children block))
      have hchildrenDisjoint :
          childrenDisjoint (blocks.map fun block => (children block).toTree) := by
        rw [childrenDisjoint, List.map_map, List.pairwise_map]
        apply (orderedPartitionBlocks_pairwise_min_lt partition).imp
        intro left right hlt
        simp only [Function.comp_apply, toTree_support]
        apply partition.disjoint left.2 right.2
        intro heq
        have hsub : left = right := Subtype.ext heq
        subst right
        exact (Nat.lt_irrefl _ hlt)
      have hchildrenCanonical :
          childrenCanonical (blocks.map fun block => (children block).toTree) := by
        rw [childrenCanonical, List.pairwise_map]
        apply (orderedPartitionBlocks_pairwise_min_lt partition).imp
        intro left right hlt
        simp only [DriftTreeData.supportKey, toTree_support]
        rw [partitionBlock_min_eq_coe_minRank, partitionBlock_min_eq_coe_minRank]
        exact WithTop.coe_lt_coe.mpr hlt
      have hchildrenValid :
          ∀ child ∈ blocks.map (fun block => (children block).toTree), child.Valid := by
        intro child hchild
        rcases List.mem_map.mp hchild with ⟨block, _, rfl⟩
        exact (ih block).1
      have htimeChildren :
          DriftTimeData.ValidChildren time
            (blocks.map fun block => (children block).toTree)
            (blocks.map fun block => (children block).toTime) := by
        induction blocks with
        | nil => simp [DriftTimeData.ValidChildren]
        | cons block tail ihTail =>
            simp only [List.map, DriftTimeData.ValidChildren]
            exact ⟨(ih block).2, ihTail⟩
      constructor
      · simp only [DriftTreeData.Valid]
        refine ⟨?_, ?_, hchildrenDisjoint, hchildrenCanonical, hchildrenValid⟩
        · right
          simpa [blocks] using horder
        · rw [hchildrenSupport]
          exact Finset.disjoint_sdiff
      · simp only [DriftTimeData.Valid]
        exact ⟨htime, htimeChildren⟩

theorem toTree_valid {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    choice.toTree.Valid :=
  choice.toTree_valid_and_toTime_valid.1

theorem toTime_valid {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    choice.toTime.Valid parentTime choice.toTree :=
  choice.toTree_valid_and_toTime_valid.2

/-- At a higher drift vertex, the local partition recovered from the forward tree has exactly
the blocks of the partition selected by the expansion choice. -/
theorem higher_toTree_childPartition_parts {J noiseDim parentTime time : ℕ}
    {support : Finset (Index J noiseDim)} (htime : time < parentTime)
    (direct : Finset (Index J noiseDim)) (hsubset : direct ⊆ support)
    (partition : Finpartition (support \ direct))
    (horder : 2 ≤ direct.card + partition.parts.card)
    (children : ∀ block : partition.parts,
      DriftExpansionChoice J noiseDim time block.1) :
    let choice := DriftExpansionChoice.higher time htime direct hsubset
      partition horder children
    (choice.toTree.childPartition choice.toTree_valid).parts =
      partition.parts := by
  let choice := DriftExpansionChoice.higher time htime direct hsubset
    partition horder children
  dsimp only
  rw [DriftTreeData.childPartition_parts]
  rw [higher_toTree]
  simp only [childSupports]
  apply Finset.ext
  intro part
  simp only [List.mem_toFinset]
  change part ∈
      List.map DriftTreeData.support
        (List.map (fun block => (children block).toTree)
          (orderedPartitionBlocks partition)) ↔
    part ∈ partition.parts
  simp only [List.map_map, List.mem_map]
  constructor
  · rintro ⟨block, hblock, hsupport⟩
    simp only [Function.comp_apply] at hsupport
    have hexact := toTree_support (children block)
    rw [hexact] at hsupport
    rw [← hsupport]
    exact block.2
  · intro hpart
    let block : partition.parts := ⟨part, hpart⟩
    refine ⟨block, mem_orderedPartitionBlocks partition block, ?_⟩
    simpa only [Function.comp_apply] using toTree_support (children block)

/-- Even when the support indices are presented differently, equal forward tree-time data
determine heterogeneously equal recursive expansion choices. -/
theorem toTreeTime_injective_heq {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (left : DriftExpansionChoice J noiseDim parentTime support) :
    ∀ {otherSupport : Finset (Index J noiseDim)}
      (right : DriftExpansionChoice J noiseDim parentTime otherSupport),
      left.toTreeTime = right.toTreeTime → HEq left right := by
  induction left with
  | @singleton actualParent time j htime =>
      intro otherSupport right heq
      cases right with
      | singleton otherTime k otherHtime =>
          simp only [toTreeTime] at heq
          have htimeEq : time = otherTime := by
            injection heq with htree htimes
            injection htimes
          subst otherTime
          have hj : j = k := by
            injection heq with htree htimes
            injection htree with hdirect hchildren
            exact Finset.singleton_inj.mp hdirect
          cases hj
          rfl
      | higher otherTime otherHtime direct hsubset partition horder children =>
          simp only [toTreeTime] at heq
          have htree := congrArg Prod.fst heq
          injection htree with hdirect hchildren
          have hblocksLength :
              (orderedPartitionBlocks partition).length = 0 := by
            simpa using congrArg List.length hchildren.symm
          have hblocks : partition.parts.card = 0 := by
            simpa using hblocksLength
          have hdirectCard : direct.card = 1 := by
            rw [← hdirect]
            simp
          omega
  | @higher actualParent actualSupport time htime direct hsubset partition horder
      children ih =>
      intro otherSupport right heq
      cases right with
      | singleton otherTime k otherHtime =>
          simp only [toTreeTime] at heq
          have htree := congrArg Prod.fst heq
          injection htree with hdirect hchildren
          have hblocksLength :
              (orderedPartitionBlocks partition).length = 0 := by
            simpa using congrArg List.length hchildren
          have hblocks : partition.parts.card = 0 := by
            simpa using hblocksLength
          have hdirectCard : direct.card = 1 := by
            rw [hdirect]
            simp
          omega
      | higher otherTime otherHtime otherDirect otherSubset otherPartition
          otherOrder otherChildren =>
          simp only [toTreeTime] at heq
          have htreeEq := congrArg Prod.fst heq
          have htimes := congrArg Prod.snd heq
          have htree := htreeEq
          injection htree with hdirect htreeChildren
          injection htimes with htimeEq htimeChildren
          subst otherTime
          subst otherDirect
          have hsupportEq : actualSupport = otherSupport := by
            have hleftSupport := toTree_support
              (higher time htime direct hsubset partition horder children)
            have hrightSupport := toTree_support
              (higher time otherHtime direct otherSubset otherPartition
                otherOrder otherChildren)
            exact hleftSupport.symm.trans
              ((congrArg DriftTreeData.support htreeEq).trans hrightSupport)
          subst otherSupport
          have hpartition : partition = otherPartition := by
            apply Finpartition.ext
            have hleft := higher_toTree_childPartition_parts htime direct hsubset
              partition horder children
            have hright := higher_toTree_childPartition_parts otherHtime direct
              otherSubset otherPartition otherOrder otherChildren
            dsimp only at hleft hright
            calc
              partition.parts =
                  ((higher time htime direct hsubset partition horder children).toTree
                    |>.childPartition
                      (higher time htime direct hsubset partition horder children).toTree_valid
                    ).parts := hleft.symm
              _ =
                  ((higher time otherHtime direct otherSubset otherPartition otherOrder
                    otherChildren).toTree |>.childPartition
                      (higher time otherHtime direct otherSubset otherPartition otherOrder
                        otherChildren).toTree_valid).parts := by
                    rw [DriftTreeData.childPartition_parts,
                      DriftTreeData.childPartition_parts]
                    exact congrArg (fun list => (childSupports list).toFinset)
                      htreeChildren
              _ = otherPartition.parts := hright
          subst otherPartition
          have hpairs :
              (orderedPartitionBlocks partition).map
                  (fun block => (children block).toTreeTime) =
                (orderedPartitionBlocks partition).map
                  (fun block => (otherChildren block).toTreeTime) := by
            apply list_prod_eq_of_map_fst_snd_eq
            · exact htreeChildren
            · exact htimeChildren
          have hchildren : children = otherChildren := by
            funext block
            apply eq_of_heq
            apply ih block (otherChildren block)
            apply apply_eq_of_map_eq_of_mem
                (orderedPartitionBlocks partition)
                (fun part => (children part).toTreeTime)
                (fun part => (otherChildren part).toTreeTime) hpairs
              (mem_orderedPartitionBlocks partition block)
          subst otherChildren
          rfl

/-- The forward map from recursive drift expansion choices to timed drift trees is injective. -/
theorem toTreeTime_injective {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)} :
    Function.Injective
      (@toTreeTime J noiseDim parentTime support) := by
  intro left right heq
  exact eq_of_heq (toTreeTime_injective_heq left right heq)

/-- Fuelled core of the inverse construction.  The fuel is an implementation device only; the
public inverse below supplies the exact structural bound. -/
noncomputable def ofTreeTimeAux {J noiseDim parentTime : ℕ} (fuel : ℕ)
    (tree : DriftTreeData J noiseDim) (assignment : DriftTimeData)
    (treeValid : tree.Valid) (assignmentValid : assignment.Valid parentTime tree)
    (size_lt : sizeOf tree < fuel) :
    DriftExpansionChoice J noiseDim parentTime tree.support :=
  match fuel with
  | 0 => (Nat.not_lt_zero (sizeOf tree) size_lt).elim
  | fuel + 1 => by
    classical
    cases tree with
      | node direct children =>
        cases assignment with
        | node time assignments =>
          have htree : (DriftTreeData.node direct children).Valid := treeValid
          have htime : (DriftTimeData.node time assignments).Valid parentTime
              (DriftTreeData.node direct children) := assignmentValid
          simp only [DriftTreeData.Valid] at htree
          simp only [DriftTimeData.Valid] at htime
          by_cases hsingleton : direct.card = 1 ∧ children.length = 0
          · let j := Classical.choose (Finset.card_eq_one.mp hsingleton.1)
            have hj : direct = {j} :=
              Classical.choose_spec (Finset.card_eq_one.mp hsingleton.1)
            have hchildren : children = [] := by simpa using hsingleton.2
            subst children
            have hsupport : (DriftTreeData.node direct []).support = {j} := by
              simp [hj]
            exact hsupport.symm ▸ DriftExpansionChoice.singleton time j htime.1
          · let parentTree := DriftTreeData.node direct children
            have hhigher : 2 ≤ direct.card + children.length :=
              Or.resolve_left htree.1 hsingleton
            have hparentValid : parentTree.Valid := treeValid
            let partition := parentTree.childPartition hparentValid
            have hsubset : direct ⊆ parentTree.support := by
              intro j hj
              simp only [parentTree, DriftTreeData.support_node]
              exact Finset.mem_union_left _ hj
            have horder : 2 ≤ direct.card + partition.parts.card := by
              rw [show partition.parts.card = children.length by
                exact parentTree.childPartition_card_eq_children_length hparentValid]
              exact hhigher
            refine DriftExpansionChoice.higher time htime.1 direct hsubset partition
              horder ?_
            intro block
            let index := parentTree.childBlockIndex hparentValid block
            let child := children.get index
            have hchild : child ∈ children := List.get_mem children index
            have hsupport : child.support = block.1 :=
              parentTree.childBlockIndex_support hparentValid block
            have hlength := DriftTimeData.validChildren_length_eq htime.2
            let timeIndex : Fin assignments.length :=
              ⟨index.val, by rw [← hlength]; exact index.isLt⟩
            let childTime := assignments.get timeIndex
            have hchildTimeValid : childTime.Valid time child := by
              exact DriftTimeData.validChildren_get htime.2 index
            have hchildValid : child.Valid := htree.2.2.2.2 child hchild
            have hchildSize : sizeOf child < fuel := by
              have hproper := DriftTreeData.sizeOf_child_lt direct children child hchild
              simp_all
              omega
            exact hsupport ▸ ofTreeTimeAux fuel child childTime hchildValid
              hchildTimeValid hchildSize
termination_by fuel

/-- Inverse construction on a drift subtree.  A valid canonical tree and its aligned time data
recover a complete recursive expansion choice on exactly the tree support. -/
noncomputable def ofTreeTime {J noiseDim parentTime : ℕ}
    (tree : DriftTreeData J noiseDim) (assignment : DriftTimeData)
    (treeValid : tree.Valid) (assignmentValid : assignment.Valid parentTime tree) :
    DriftExpansionChoice J noiseDim parentTime tree.support :=
  ofTreeTimeAux (sizeOf tree + 1) tree assignment treeValid assignmentValid (by omega)

/-- Reconstructing an expansion choice from any valid timed drift tree and applying the forward
map recovers the original tree and time assignment. -/
theorem ofTreeTimeAux_toTreeTime {J noiseDim : ℕ} (fuel : ℕ) :
    ∀ {parentTime : ℕ} (tree : DriftTreeData J noiseDim)
      (assignment : DriftTimeData) (treeValid : tree.Valid)
      (assignmentValid : assignment.Valid parentTime tree)
      (size_lt : sizeOf tree < fuel),
      (ofTreeTimeAux fuel tree assignment treeValid assignmentValid size_lt).toTreeTime =
        (tree, assignment) := by
  induction fuel with
  | zero =>
      intro parentTime tree assignment treeValid assignmentValid size_lt
      omega
  | succ fuel ih =>
      intro parentTime tree assignment treeValid assignmentValid size_lt
      rw [ofTreeTimeAux.eq_2]
      cases tree with
      | node direct children =>
        cases assignment with
        | node time assignments =>
          dsimp only
          split
          · rename_i hsingleton
            obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hsingleton.1
            have hchildren : children = [] := by simpa using hsingleton.2
            subst direct
            subst children
            have htimeRaw := assignmentValid
            simp only [DriftTimeData.Valid] at htimeRaw
            have hassignments : assignments = [] := by
              cases assignments with
              | nil => rfl
              | cons head tail =>
                  simp [DriftTimeData.ValidChildren] at htimeRaw
            subst assignments
            simp [toTreeTime]
          · rename_i hnonsingleton
            have htree := treeValid
            have htime := assignmentValid
            simp only [DriftTreeData.Valid] at htree
            simp only [DriftTimeData.Valid] at htime
            let parentTree := DriftTreeData.node direct children
            have hparentValid : parentTree.Valid := treeValid
            let partition := parentTree.childPartition hparentValid
            let recoveredTree : (parentTree.childPartition hparentValid).parts →
                DriftTreeData J noiseDim := fun block =>
              parentTree.children.get
                (parentTree.childBlockIndex hparentValid block)
            let recoveredTime : (parentTree.childPartition hparentValid).parts →
                DriftTimeData := fun block =>
              let index := parentTree.childBlockIndex hparentValid block
              let timeIndex : Fin assignments.length :=
                ⟨index.val, by
                  rw [← DriftTimeData.validChildren_length_eq htime.2]
                  exact index.isLt⟩
              assignments.get timeIndex
            let recoveredChoice : ∀ block :
                (parentTree.childPartition hparentValid).parts,
                DriftExpansionChoice J noiseDim time block.1 := fun block => by
              let index := parentTree.childBlockIndex hparentValid block
              let child := parentTree.children.get index
              have hchild : child ∈ parentTree.children :=
                List.get_mem parentTree.children index
              have hsupport : child.support = block.1 :=
                parentTree.childBlockIndex_support hparentValid block
              have hchildValid : child.Valid := by
                have hchild' : child ∈ children := by
                  change child ∈ children at hchild
                  exact hchild
                exact htree.2.2.2.2 child hchild'
              let timeIndex : Fin assignments.length :=
                ⟨index.val, by
                  rw [← DriftTimeData.validChildren_length_eq htime.2]
                  exact index.isLt⟩
              let childTime := assignments.get timeIndex
              have hchildTimeValid : childTime.Valid time child :=
                DriftTimeData.validChildren_get htime.2 index
              have hchildSize : sizeOf child < fuel := by
                have hproper :=
                  DriftTreeData.sizeOf_child_lt parentTree.direct
                    parentTree.children child hchild
                have hnode :
                    DriftTreeData.node parentTree.direct parentTree.children =
                      parentTree := by rfl
                rw [hnode] at hproper
                have hparentSize : sizeOf parentTree < fuel + 1 := by
                  simpa [parentTree] using size_lt
                omega
              exact hsupport ▸ ofTreeTimeAux fuel child childTime hchildValid
                hchildTimeValid hchildSize
            have hpairs : ∀ block,
                (recoveredChoice block).toTreeTime =
                  (recoveredTree block, recoveredTime block) := by
              intro block
              dsimp only [recoveredChoice, recoveredTree, recoveredTime]
              let index := parentTree.childBlockIndex hparentValid block
              let child := parentTree.children.get index
              have hchild : child ∈ parentTree.children :=
                List.get_mem parentTree.children index
              have hchildValid : child.Valid := by
                have hchild' : child ∈ children := by
                  change child ∈ children at hchild
                  exact hchild
                exact htree.2.2.2.2 child hchild'
              have hsupport : child.support = block.1 :=
                parentTree.childBlockIndex_support hparentValid block
              let timeIndex : Fin assignments.length :=
                ⟨index.val, by
                  rw [← DriftTimeData.validChildren_length_eq htime.2]
                  exact index.isLt⟩
              let childTime := assignments.get timeIndex
              have hchildTimeValid : childTime.Valid time child :=
                DriftTimeData.validChildren_get htime.2 index
              have hchildSize : sizeOf child < fuel := by
                have hproper : sizeOf child < sizeOf parentTree := by
                  have hproper' :=
                    DriftTreeData.sizeOf_child_lt parentTree.direct
                      parentTree.children child hchild
                  have hnode :
                      DriftTreeData.node parentTree.direct parentTree.children =
                        parentTree := by rfl
                  rwa [hnode] at hproper'
                have hparentSize : sizeOf parentTree < fuel + 1 := by
                  simpa [parentTree] using size_lt
                omega
              change
                (hsupport ▸ ofTreeTimeAux fuel child childTime hchildValid
                  hchildTimeValid hchildSize).toTreeTime =
                    (child, childTime)
              rw [toTreeTime_cast_support]
              exact ih child childTime hchildValid hchildTimeValid hchildSize
            have hpairList :
                (parentTree.childBlocks hparentValid).map
                    (fun block => (recoveredChoice block).toTreeTime) =
                  (parentTree.childBlocks hparentValid).map
                    (fun block => (recoveredTree block, recoveredTime block)) := by
              apply List.map_congr_left
              intro block hblock
              exact hpairs block
            change
              (DriftTreeData.node direct
                  (((orderedPartitionBlocks partition).map fun block =>
                    (recoveredChoice block).toTreeTime).map Prod.fst),
                DriftTimeData.node time
                  (((orderedPartitionBlocks partition).map fun block =>
                    (recoveredChoice block).toTreeTime).map Prod.snd)) =
                (DriftTreeData.node direct children,
                  DriftTimeData.node time assignments)
            rw [show orderedPartitionBlocks partition =
                parentTree.childBlocks hparentValid by
              exact parentTree.ordered_childPartition_eq_childBlocks hparentValid]
            rw [hpairList]
            simp only [List.map_map]
            change
              (DriftTreeData.node direct
                  ((parentTree.childBlocks hparentValid).map recoveredTree),
                DriftTimeData.node time
                  ((parentTree.childBlocks hparentValid).map recoveredTime)) =
                (DriftTreeData.node direct children,
                  DriftTimeData.node time assignments)
            dsimp only [recoveredTree, recoveredTime]
            rw [parentTree.map_childBlockIndex_get hparentValid]
            rw [parentTree.map_childBlockIndex_get_time hparentValid assignments htime.2]
            rfl

/-- Public form of the drift-tree inverse law. -/
theorem ofTreeTime_toTreeTime {J noiseDim parentTime : ℕ}
    (tree : DriftTreeData J noiseDim) (assignment : DriftTimeData)
    (treeValid : tree.Valid) (assignmentValid : assignment.Valid parentTime tree) :
    (ofTreeTime tree assignment treeValid assignmentValid).toTreeTime =
      (tree, assignment) := by
  apply ofTreeTimeAux_toTreeTime

/-- Applying the inverse construction to the timed tree produced by a recursive expansion
choice recovers that choice. -/
theorem ofTreeTime_leftInverse {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    choice.toTree_support ▸
        ofTreeTime choice.toTree choice.toTime choice.toTree_valid
          choice.toTime_valid = choice := by
  apply toTreeTime_injective
  rw [toTreeTime_cast_support]
  rw [ofTreeTime_toTreeTime]
  rfl

/-- The inverse and forward maps are already inverse on the exceptional singleton leaf. -/
theorem ofTreeTimeAux_singleton_toTreeTime {J noiseDim parentTime time fuel : ℕ}
    (j : Index J noiseDim) (htime : time < parentTime)
    (hsize : sizeOf (DriftTreeData.node {j} []) < fuel) :
    (ofTreeTimeAux fuel (.node {j} []) (.node time [])
      (DriftTreeData.singletonLeaf_valid j)
      (by
        rw [DriftTimeData.Valid]
        exact ⟨htime, by simp [DriftTimeData.ValidChildren]⟩) hsize).toTreeTime =
        (.node {j} [], .node time []) := by
  induction fuel with
  | zero => omega
  | succ fuel ih =>
      rw [ofTreeTimeAux.eq_2]
      dsimp only
      split
      · rename_i htrue
        let k := Classical.choose (Finset.card_eq_one.mp htrue.1)
        have hk : ({j} : Finset (Index J noiseDim)) = {k} :=
          Classical.choose_spec (Finset.card_eq_one.mp htrue.1)
        have hkj : j = k := Finset.singleton_inj.mp hk
        subst k
        simp [toTreeTime]
      · rename_i hfalse
        exact (hfalse ⟨by simp, by simp⟩).elim

theorem ofTreeTime_singleton_toTreeTime {J noiseDim parentTime time : ℕ}
    (j : Index J noiseDim) (htime : time < parentTime) :
    (ofTreeTime (.node {j} []) (.node time [])
      (DriftTreeData.singletonLeaf_valid j)
      (by
        rw [DriftTimeData.Valid]
        exact ⟨htime, by simp [DriftTimeData.ValidChildren]⟩)).toTreeTime =
        (.node {j} [], .node time []) := by
  simpa only [ofTreeTime] using
    ofTreeTimeAux_singleton_toTreeTime (fuel := sizeOf (DriftTreeData.node {j} []) + 1)
      j htime (by omega)

end DriftExpansionChoice

namespace PayoffExpansionChoice

/-- Extensionality for complete payoff expansion choices.  Proof fields are irrelevant; direct
labels, the selected partition, and the recursively selected children determine the choice. -/
@[ext]
theorem ext {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    {left right : PayoffExpansionChoice J noiseDim u m}
    (hdirect : left.direct = right.direct)
    (hpartition : HEq left.partition right.partition)
    (hchildren : HEq left.children right.children) : left = right := by
  cases left with
  | mk leftDirect leftSubset leftEndpoint leftPartition leftChildren =>
    cases right with
    | mk rightDirect rightSubset rightEndpoint rightPartition rightChildren =>
      dsimp only at hdirect hpartition hchildren
      subst rightDirect
      have hp : leftPartition = rightPartition := eq_of_heq hpartition
      subst rightPartition
      have hc : leftChildren = rightChildren := eq_of_heq hchildren
      subst rightChildren
      rfl

private theorem children_heq_of_pair_lists {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)}
    {left right : PayoffExpansionChoice J noiseDim u m}
    (hdirect : left.direct = right.direct)
    (hpartition : HEq left.partition right.partition)
    (hpairs :
      (orderedPartitionBlocks left.partition).map
          (fun block => (left.children block).toTreeTime) =
        (orderedPartitionBlocks right.partition).map
          (fun block => (right.children block).toTreeTime)) :
    HEq left.children right.children := by
  cases left with
  | mk leftDirect leftSubset leftEndpoint leftPartition leftChildren =>
    cases right with
    | mk rightDirect rightSubset rightEndpoint rightPartition rightChildren =>
      dsimp only at hdirect hpartition hpairs ⊢
      subst rightDirect
      have hp : leftPartition = rightPartition := eq_of_heq hpartition
      subst rightPartition
      apply heq_of_eq
      funext block
      apply DriftExpansionChoice.toTreeTime_injective
      apply apply_eq_of_map_eq_of_mem (orderedPartitionBlocks leftPartition)
          (fun part => (leftChildren part).toTreeTime)
          (fun part => (rightChildren part).toTreeTime) hpairs
        (mem_orderedPartitionBlocks leftPartition block)

/-- The canonical payoff-tree data associated with a complete payoff expansion choice. -/
def toTreeData {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) : PayoffTreeData J noiseDim :=
  let childPairs := (orderedPartitionBlocks choice.partition).map fun block =>
    (choice.children block).toTreeTime
  ⟨choice.direct, childPairs.map Prod.fst⟩

/-- The time assignment carried by a complete payoff expansion choice. -/
def toAssignment {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) : TimeAssignment :=
  let childPairs := (orderedPartitionBlocks choice.partition).map fun block =>
    (choice.children block).toTreeTime
  ⟨m, childPairs.map Prod.snd⟩

@[simp]
theorem toTreeData_direct {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toTreeData.direct = choice.direct := by
  simp [toTreeData]

@[simp]
theorem toTreeData_children {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toTreeData.children =
      (orderedPartitionBlocks choice.partition).map fun block =>
        (choice.children block).toTree := by
  simp [toTreeData, DriftExpansionChoice.toTree, Function.comp_def]

@[simp]
theorem toAssignment_rootTime {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toAssignment.rootTime = m := by
  simp [toAssignment]

@[simp]
theorem toAssignment_children {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toAssignment.children =
      (orderedPartitionBlocks choice.partition).map fun block =>
        (choice.children block).toTime := by
  simp [toAssignment, DriftExpansionChoice.toTime, Function.comp_def]

/-- The payoff tree obtained from a complete expansion choice carries exactly the original
coordinate set. -/
theorem toTreeData_support {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toTreeData.support = u := by
  rw [PayoffTreeData.support, toTreeData_direct, toTreeData_children]
  rw [childrenSupport_map_orderedPartitionBlocks choice.partition
    (fun block => (choice.children block).toTree)
    (fun block => DriftExpansionChoice.toTree_support (choice.children block))]
  exact Finset.union_sdiff_of_subset choice.direct_subset

/-- The root data produced by the forward map satisfy all payoff-tree conditions. -/
theorem toTreeData_valid {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toTreeData.Valid u := by
  let blocks := orderedPartitionBlocks choice.partition
  rw [PayoffTreeData.Valid]
  refine ⟨choice.toTreeData_support, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using choice.direct_endpoint
  · rw [toTreeData_direct, toTreeData_children]
    rw [childrenSupport_map_orderedPartitionBlocks choice.partition
      (fun block => (choice.children block).toTree)
      (fun block => DriftExpansionChoice.toTree_support (choice.children block))]
    exact Finset.disjoint_sdiff
  · rw [toTreeData_children, childrenDisjoint, List.map_map, List.pairwise_map]
    apply (orderedPartitionBlocks_pairwise_min_lt choice.partition).imp
    intro left right hlt
    simp only [Function.comp_apply, DriftExpansionChoice.toTree_support]
    apply choice.partition.disjoint left.2 right.2
    intro heq
    have hsub : left = right := Subtype.ext heq
    subst right
    exact Nat.lt_irrefl _ hlt
  · rw [toTreeData_children, childrenCanonical, List.pairwise_map]
    apply (orderedPartitionBlocks_pairwise_min_lt choice.partition).imp
    intro left right hlt
    simp only [DriftTreeData.supportKey, DriftExpansionChoice.toTree_support]
    rw [partitionBlock_min_eq_coe_minRank, partitionBlock_min_eq_coe_minRank]
    exact WithTop.coe_lt_coe.mpr hlt
  · rw [toTreeData_children]
    intro child hchild
    rcases List.mem_map.mp hchild with ⟨block, _, rfl⟩
    exact DriftExpansionChoice.toTree_valid (choice.children block)

/-- The root and recursive time labels produced by the forward map form a valid assignment. -/
theorem toAssignment_valid {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toAssignment.Valid m choice.toTreeData := by
  rw [TimeAssignment.Valid, toAssignment_rootTime, toTreeData_children,
    toAssignment_children]
  refine ⟨rfl, ?_⟩
  let blocks := orderedPartitionBlocks choice.partition
  change DriftTimeData.ValidChildren m
    (blocks.map fun block => (choice.children block).toTree)
    (blocks.map fun block => (choice.children block).toTime)
  induction blocks with
  | nil => simp [DriftTimeData.ValidChildren]
  | cons block tail ihTail =>
      simp only [List.map, DriftTimeData.ValidChildren]
      exact ⟨DriftExpansionChoice.toTime_valid (choice.children block), ihTail⟩

/-- Forward half of the correspondence: a complete recursive expansion choice determines a
canonical timed payoff tree. -/
def toTimedPayoffTree {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    TimedPayoffTree J noiseDim u m where
  tree := ⟨choice.toTreeData, choice.toTreeData_valid⟩
  assignment := choice.toAssignment
  assignmentValid := choice.toAssignment_valid

@[simp]
theorem toTimedPayoffTree_data {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toTimedPayoffTree.tree.data = choice.toTreeData :=
  rfl

@[simp]
theorem toTimedPayoffTree_assignment {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toTimedPayoffTree.assignment = choice.toAssignment :=
  rfl

/-- The root partition recovered from a forward payoff tree is the partition selected by the
expansion choice. -/
theorem toTimedPayoffTree_childPartition {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.toTimedPayoffTree.tree.childPartition = choice.partition := by
  apply Finpartition.ext
  rw [LabelledPayoffTree.childPartition_parts]
  change (childSupports choice.toTreeData.children).toFinset =
    choice.partition.parts
  rw [toTreeData_children]
  simp only [childSupports, List.map_map]
  apply Finset.ext
  intro part
  simp only [List.mem_toFinset, List.mem_map, mem_orderedPartitionBlocks,
    Subtype.exists]
  constructor
  · rintro ⟨candidate, hcandidate, _, hsupport⟩
    simp only [Function.comp_apply] at hsupport
    have hexact :=
      DriftExpansionChoice.toTree_support
        (choice.children ⟨candidate, hcandidate⟩)
    rw [hexact] at hsupport
    rwa [← hsupport]
  · intro hpart
    refine ⟨part, hpart, True.intro, ?_⟩
    simpa only [Function.comp_apply] using
      DriftExpansionChoice.toTree_support (choice.children ⟨part, hpart⟩)

/-- The forward map from complete payoff expansion choices to timed payoff trees is injective. -/
theorem toTimedPayoffTree_injective {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} :
    Function.Injective
      (@toTimedPayoffTree J noiseDim m u) := by
  intro left right heq
  have htree := congrArg (fun timed => timed.tree) heq
  have hdata := congrArg (fun timed => timed.tree.data) heq
  have hassignment := congrArg (fun timed => timed.assignment) heq
  have hdirect : left.direct = right.direct := by
    exact congrArg PayoffTreeData.direct hdata
  have hpartitionParts : left.partition.parts = right.partition.parts := by
    have hleft := toTimedPayoffTree_childPartition left
    have hright := toTimedPayoffTree_childPartition right
    calc
      left.partition.parts =
          left.toTimedPayoffTree.tree.childPartition.parts :=
        congrArg Finpartition.parts hleft.symm
      _ = right.toTimedPayoffTree.tree.childPartition.parts := by
        exact congrArg (fun tree => tree.childPartition.parts) htree
      _ = right.partition.parts := congrArg Finpartition.parts hright
  have hpartition : HEq left.partition right.partition :=
    finpartition_heq_of_parts_eq left.partition right.partition hpartitionParts
  have htreeChildren :
      ((orderedPartitionBlocks left.partition).map
          (fun block => (left.children block).toTreeTime)).map Prod.fst =
        ((orderedPartitionBlocks right.partition).map
          (fun block => (right.children block).toTreeTime)).map Prod.fst := by
    exact congrArg PayoffTreeData.children hdata
  have htimeChildren :
      ((orderedPartitionBlocks left.partition).map
          (fun block => (left.children block).toTreeTime)).map Prod.snd =
        ((orderedPartitionBlocks right.partition).map
          (fun block => (right.children block).toTreeTime)).map Prod.snd := by
    exact congrArg TimeAssignment.children hassignment
  have hpairs :
      (orderedPartitionBlocks left.partition).map
          (fun block => (left.children block).toTreeTime) =
        (orderedPartitionBlocks right.partition).map
          (fun block => (right.children block).toTreeTime) :=
    list_prod_eq_of_map_fst_snd_eq htreeChildren htimeChildren
  have hchildren : HEq left.children right.children := by
    exact children_heq_of_pair_lists hdirect hpartition hpairs
  exact ext hdirect hpartition hchildren

/-- The forward map agrees with the explicit root-only timed tree.  This is the base case of
the two inverse proofs. -/
theorem rootOnly_toTimedPayoffTree {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    (rootOnly u hendpoint m).toTimedPayoffTree =
      TimedPayoffTree.rootOnly u hendpoint m := by
  have hblocks : orderedPartitionBlocks (rootOnly u hendpoint m).partition = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro block _
    have hpart : block.1 ∈ (∅ : Finset (Finset (Index J noiseDim))) := by
      rw [← rootOnly_partition_parts u hendpoint m]
      exact block.2
    simp at hpart
  ext <;> simp only [toTimedPayoffTree, toTreeData, toAssignment] <;>
    rw [hblocks] <;> simp [TimeAssignment.rootOnly]

/-- Reverse half of the construction: recover the unordered complete expansion choices from a
valid timed canonical payoff tree. -/
noncomputable def ofTimedPayoffTree {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} (timed : TimedPayoffTree J noiseDim u m) :
    PayoffExpansionChoice J noiseDim u m := by
  classical
  let root := timed.tree
  let partition := root.childPartition
  have hsubset : root.data.direct ⊆ u := by
    intro j hj
    rw [← root.valid.1]
    exact Finset.mem_union_left _ hj
  refine
    { direct := root.data.direct
      direct_subset := hsubset
      direct_endpoint := root.valid.2.1
      partition := partition
      children := ?_ }
  intro block
  let index := root.childBlockIndex block
  let child := root.data.children.get index
  have hchild : child ∈ root.data.children := List.get_mem root.data.children index
  have hsupport : child.support = block.1 := root.childBlockIndex_support block
  have hlength :=
    DriftTimeData.validChildren_length_eq timed.assignmentValid.2
  let timeIndex : Fin timed.assignment.children.length :=
    ⟨index.val, by rw [← hlength]; exact index.isLt⟩
  let childTime := timed.assignment.children.get timeIndex
  have hchildTimeValid : childTime.Valid m child := by
    exact DriftTimeData.validChildren_get timed.assignmentValid.2 index
  have hchildValid : child.Valid := root.valid.2.2.2.2.2 child hchild
  exact hsupport ▸ DriftExpansionChoice.ofTreeTime child childTime hchildValid
    hchildTimeValid

/-- Reconstructing expansion choices from a valid timed payoff tree and applying the forward map
recovers the original timed tree. -/
theorem ofTimedPayoffTree_toTimedPayoffTree {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)}
    (timed : TimedPayoffTree J noiseDim u m) :
    (ofTimedPayoffTree timed).toTimedPayoffTree = timed := by
  let root := timed.tree
  let partition := root.childPartition
  let recoveredTree : root.childPartition.parts → DriftTreeData J noiseDim :=
    fun block => root.data.children.get (root.childBlockIndex block)
  let recoveredTime : root.childPartition.parts → DriftTimeData :=
    fun block =>
      let index := root.childBlockIndex block
      let timeIndex : Fin timed.assignment.children.length :=
        ⟨index.val, by
          rw [← DriftTimeData.validChildren_length_eq timed.assignmentValid.2]
          exact index.isLt⟩
      timed.assignment.children.get timeIndex
  let recoveredChoice : ∀ block : root.childPartition.parts,
      DriftExpansionChoice J noiseDim m block.1 := fun block => by
    let index := root.childBlockIndex block
    let child := root.data.children.get index
    have hchild : child ∈ root.data.children :=
      List.get_mem root.data.children index
    have hsupport : child.support = block.1 :=
      root.childBlockIndex_support block
    let timeIndex : Fin timed.assignment.children.length :=
      ⟨index.val, by
        rw [← DriftTimeData.validChildren_length_eq timed.assignmentValid.2]
        exact index.isLt⟩
    let childTime := timed.assignment.children.get timeIndex
    have hchildTimeValid : childTime.Valid m child :=
      DriftTimeData.validChildren_get timed.assignmentValid.2 index
    have hchildValid : child.Valid := root.valid.2.2.2.2.2 child hchild
    exact hsupport ▸ DriftExpansionChoice.ofTreeTime child childTime
      hchildValid hchildTimeValid
  have hpairs : ∀ block, (recoveredChoice block).toTreeTime =
      (recoveredTree block, recoveredTime block) := by
    intro block
    dsimp only [recoveredChoice, recoveredTree, recoveredTime]
    let index := root.childBlockIndex block
    let child := root.data.children.get index
    have hsupport : child.support = block.1 :=
      root.childBlockIndex_support block
    let timeIndex : Fin timed.assignment.children.length :=
      ⟨index.val, by
        rw [← DriftTimeData.validChildren_length_eq timed.assignmentValid.2]
        exact index.isLt⟩
    let childTime := timed.assignment.children.get timeIndex
    have hchild : child ∈ root.data.children :=
      List.get_mem root.data.children index
    have hchildValid : child.Valid := root.valid.2.2.2.2.2 child hchild
    have hchildTimeValid : childTime.Valid m child :=
      DriftTimeData.validChildren_get timed.assignmentValid.2 index
    change
      (hsupport ▸ DriftExpansionChoice.ofTreeTime child childTime
        hchildValid hchildTimeValid).toTreeTime = (child, childTime)
    rw [DriftExpansionChoice.toTreeTime_cast_support]
    exact DriftExpansionChoice.ofTreeTime_toTreeTime child childTime
      hchildValid hchildTimeValid
  have hblocks : orderedPartitionBlocks partition = root.childBlocks := by
    exact root.ordered_childPartition_eq_childBlocks
  have hpairList :
      root.childBlocks.map (fun block => (recoveredChoice block).toTreeTime) =
        root.childBlocks.map fun block =>
          (recoveredTree block, recoveredTime block) := by
    apply List.map_congr_left
    intro block hblock
    exact hpairs block
  apply TimedPayoffTree.ext
  · apply LabelledPayoffTree.ext
    change
      PayoffTreeData.mk root.data.direct
          (((orderedPartitionBlocks partition).map fun block =>
            (recoveredChoice block).toTreeTime).map Prod.fst) = root.data
    rw [hblocks, hpairList]
    simp only [List.map_map]
    change
      PayoffTreeData.mk root.data.direct
          (root.childBlocks.map recoveredTree) = root.data
    dsimp only [recoveredTree]
    rw [root.map_childBlockIndex_get]
  · change
      TimeAssignment.mk m
          (((orderedPartitionBlocks partition).map fun block =>
            (recoveredChoice block).toTreeTime).map Prod.snd) = timed.assignment
    rw [hblocks, hpairList]
    simp only [List.map_map]
    change
      TimeAssignment.mk m (root.childBlocks.map recoveredTime) =
        timed.assignment
    dsimp only [recoveredTime]
    rw [root.map_childBlockIndex_get_time timed.assignment.children
      timed.assignmentValid.2]
    calc
      TimeAssignment.mk m timed.assignment.children =
          TimeAssignment.mk timed.assignment.rootTime
            timed.assignment.children := by
        rw [timed.assignmentValid.1]
      _ = timed.assignment := by
        cases timed.assignment
        rfl

/-- The inverse construction is a right inverse of the forward construction. -/
theorem ofTimedPayoffTree_rightInverse {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} :
    Function.RightInverse
      (ofTimedPayoffTree (J := J) (noiseDim := noiseDim) (m := m) (u := u))
      toTimedPayoffTree :=
  ofTimedPayoffTree_toTimedPayoffTree

/-- Applying the inverse construction to the timed tree generated by a complete payoff expansion
choice recovers that choice. -/
theorem ofTimedPayoffTree_leftInverse {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)}
    (choice : PayoffExpansionChoice J noiseDim u m) :
    ofTimedPayoffTree choice.toTimedPayoffTree = choice := by
  apply toTimedPayoffTree_injective
  exact ofTimedPayoffTree_toTimedPayoffTree choice.toTimedPayoffTree

/-- Complete recursive expansion choices are equivalent to admissible timed payoff trees. -/
noncomputable def equivTimedPayoffTree {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} :
    PayoffExpansionChoice J noiseDim u m ≃
      TimedPayoffTree J noiseDim u m where
  toFun := toTimedPayoffTree
  invFun := ofTimedPayoffTree
  left_inv := ofTimedPayoffTree_leftInverse
  right_inv := ofTimedPayoffTree_toTimedPayoffTree

/-- Admissible timed payoff trees form a finite family because complete expansion choices do. -/
noncomputable instance instFiniteTimedPayoffTree {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} :
    Finite (TimedPayoffTree J noiseDim u m) :=
  Finite.of_injective
    (equivTimedPayoffTree (J := J) (noiseDim := noiseDim) (m := m) (u := u)).symm
    (equivTimedPayoffTree (J := J) (noiseDim := noiseDim) (m := m) (u := u)).symm.injective

noncomputable instance instFintypeTimedPayoffTree {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} :
    Fintype (TimedPayoffTree J noiseDim u m) :=
  Fintype.ofFinite _

/-- Every admissible timed payoff tree is produced by a complete expansion choice. -/
theorem toTimedPayoffTree_surjective {J noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)} :
    Function.Surjective
      (toTimedPayoffTree : PayoffExpansionChoice J noiseDim u m →
        TimedPayoffTree J noiseDim u m) :=
  ofTimedPayoffTree_rightInverse.surjective

end PayoffExpansionChoice

end

end TimeDependentLattice.Trees
