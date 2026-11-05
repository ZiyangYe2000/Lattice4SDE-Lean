/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.Correspondence
import TimeDependentLattice.Analysis.Finpartition

/-!
# Local direct-set and partition choices

The block derivatives in Faà di Bruno split only on singleton blocks.  This file proves that
choosing some singleton blocks as direct Brownian-bridge inputs is equivalent to the paper's
description by a direct coordinate set and a partition of its complement.
-/

namespace TimeDependentLattice.Trees
noncomputable section
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Analysis

/-- Block indices at which the linear bridge term is nonzero. -/
abbrev SingletonBlockIndex {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :=
  {i : Fin (orderedPartitionBlocks partition).length //
    ((orderedPartitionBlocksEquiv partition i).1.card = 1)}

/-- Coordinates which occur as singleton blocks of a fixed partition. -/
abbrev SingletonCoordinate {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :=
  {j : Index J noiseDim // {j} ∈ partition.parts}

/-- A singleton block and its unique coordinate carry the same information. -/
noncomputable def singletonBlockIndexEquivCoordinate {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    SingletonBlockIndex partition ≃ SingletonCoordinate partition where
  toFun index :=
    ⟨finpartitionSingletonCoordinate
      (orderedPartitionBlocksEquiv partition index.1) index.2, by
      rw [← finpartitionBlock_eq_singleton
        (orderedPartitionBlocksEquiv partition index.1) index.2]
      exact (orderedPartitionBlocksEquiv partition index.1).2⟩
  invFun coordinate :=
    ⟨(orderedPartitionBlocksEquiv partition).symm ⟨{coordinate.1}, coordinate.2⟩, by
      simp⟩
  left_inv index := by
    apply Subtype.ext
    apply (orderedPartitionBlocksEquiv partition).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact (finpartitionBlock_eq_singleton
      (orderedPartitionBlocksEquiv partition index.1) index.2).symm
  right_inv coordinate := by
    apply Subtype.ext
    have hmember := finpartitionSingletonCoordinate_mem
      ((⟨{coordinate.1}, coordinate.2⟩ : partition.parts)) (by simp)
    have hcoordinate : finpartitionSingletonCoordinate
        ((⟨{coordinate.1}, coordinate.2⟩ : partition.parts)) (by simp) =
        coordinate.1 := Finset.mem_singleton.mp hmember
    simpa only [Equiv.apply_symm_apply] using hcoordinate

/-- A subset of the singleton blocks, expressed in the canonical block coordinates used by the
multilinear Faà di Bruno term. -/
abbrev SingletonBlockSelection {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :=
  {selected : Finset (Fin (orderedPartitionBlocks partition).length) //
    ∀ i ∈ selected,
      (orderedPartitionBlocksEquiv partition i).1.card = 1}

/-- The direct coordinates selected from a fixed partition. -/
structure DirectChoiceForPartition {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) where
  direct : Finset (Index J noiseDim)
  direct_subset : direct ⊆ support
  singleton_parts : ∀ j ∈ direct, {j} ∈ partition.parts
  deriving DecidableEq

@[ext]
theorem DirectChoiceForPartition.ext {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} {partition : Finpartition support}
    {left right : DirectChoiceForPartition partition}
    (h : left.direct = right.direct) : left = right := by
  cases left
  cases right
  simp_all

/-- Selecting canonical singleton-block indices is the same as selecting elements of the subtype
of singleton-block indices. -/
private noncomputable def blockSelectionEquivFinsetSingletonIndex {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    SingletonBlockSelection partition ≃ Finset (SingletonBlockIndex partition) where
  toFun selected := selected.1.subtype fun i ↦
    (orderedPartitionBlocksEquiv partition i).1.card = 1
  invFun selected :=
    ⟨selected.map (Function.Embedding.subtype fun i ↦
      (orderedPartitionBlocksEquiv partition i).1.card = 1), by
      intro i hi
      obtain ⟨index, _, rfl⟩ := Finset.mem_map.mp hi
      exact index.2⟩
  left_inv selected := by
    apply Subtype.ext
    ext i
    constructor
    · intro hi
      obtain ⟨index, hindex, hvalue⟩ := Finset.mem_map.mp hi
      rw [← hvalue]
      simpa using hindex
    · intro hi
      let index : SingletonBlockIndex partition := ⟨i, selected.2 i hi⟩
      apply Finset.mem_map.mpr
      exact ⟨index, by simp [index, hi], rfl⟩
  right_inv selected := by
    ext index
    constructor
    · intro hi
      have hmap : index.1 ∈ selected.map
          (Function.Embedding.subtype fun i ↦
            (orderedPartitionBlocksEquiv partition i).1.card = 1) :=
        Finset.mem_subtype.mp hi
      obtain ⟨source, hsource, hvalue⟩ := Finset.mem_map.mp hmap
      have : source = index := by
        apply Subtype.ext
        exact hvalue
      exact this ▸ hsource
    · intro hi
      exact Finset.mem_subtype.mpr (Finset.mem_map.mpr ⟨index, hi, rfl⟩)

/-- Finsets of singleton coordinates are precisely the direct choices available inside one fixed
partition. -/
private noncomputable def finsetSingletonCoordinateEquivDirectChoice {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    Finset (SingletonCoordinate partition) ≃ DirectChoiceForPartition partition where
  toFun selected :=
    { direct := selected.map (Function.Embedding.subtype fun j ↦ {j} ∈ partition.parts)
      direct_subset := by
        intro j hj
        obtain ⟨coordinate, hcoordinate, rfl⟩ := Finset.mem_map.mp hj
        exact partition.subset coordinate.2 (by simp)
      singleton_parts := by
        intro j hj
        obtain ⟨coordinate, _, rfl⟩ := Finset.mem_map.mp hj
        exact coordinate.2 }
  invFun choice := choice.direct.subtype fun j ↦ {j} ∈ partition.parts
  left_inv selected := by
    ext coordinate
    simp [coordinate.2]
  right_inv choice := by
    apply DirectChoiceForPartition.ext
    ext j
    constructor
    · intro hj
      obtain ⟨coordinate, hcoordinate, hvalue⟩ := Finset.mem_map.mp hj
      rw [← hvalue]
      exact Finset.mem_subtype.mp hcoordinate
    · intro hj
      exact Finset.mem_map.mpr
        ⟨⟨j, choice.singleton_parts j hj⟩, by simp [hj], rfl⟩

/-- The subsets occurring in multilinear expansion are exactly the direct coordinate choices in
the paper's local notation. -/
noncomputable def singletonBlockSelectionEquivDirectChoice {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    SingletonBlockSelection partition ≃ DirectChoiceForPartition partition :=
  (blockSelectionEquivFinsetSingletonIndex partition).trans
    ((singletonBlockIndexEquivCoordinate partition).finsetCongr.trans
      (finsetSingletonCoordinateEquivDirectChoice partition))

noncomputable instance instFintypeDirectChoiceForPartition {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support) :
    Fintype (DirectChoiceForPartition partition) :=
  Fintype.ofEquiv (SingletonBlockSelection partition)
    (singletonBlockSelectionEquivDirectChoice partition)

/-- Membership is preserved by the conversion from a selected singleton block to its direct
coordinate. -/
theorem singletonBlockSelectionEquivDirectChoice_coordinate_mem {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (partition : Finpartition support)
    (selection : SingletonBlockSelection partition)
    (i : Fin (orderedPartitionBlocks partition).length)
    (hi : (orderedPartitionBlocksEquiv partition i).1.card = 1) :
    finpartitionSingletonCoordinate (orderedPartitionBlocksEquiv partition i) hi ∈
        (singletonBlockSelectionEquivDirectChoice partition selection).direct ↔
      i ∈ selection.1 := by
  change _ ∈ Finset.map _
      ((singletonBlockIndexEquivCoordinate partition).finsetCongr
        ((blockSelectionEquivFinsetSingletonIndex partition) selection)) ↔ _
  simp only [Equiv.finsetCongr_apply, Finset.mem_map]
  constructor
  · rintro ⟨coordinate, hcoordinate, hvalue⟩
    obtain ⟨index, hindex, hcoordinateValue⟩ := hcoordinate
    have hindexValue : index.1 = i := by
      have hsubtype : index = (⟨i, hi⟩ : SingletonBlockIndex partition) := by
        apply (singletonBlockIndexEquivCoordinate partition).injective
        apply Subtype.ext
        exact (congrArg Subtype.val hcoordinateValue).trans hvalue
      exact congrArg Subtype.val hsubtype
    rw [← hindexValue]
    exact Finset.mem_subtype.mp hindex
  · intro hselected
    let index : SingletonBlockIndex partition := ⟨i, hi⟩
    let coordinate := singletonBlockIndexEquivCoordinate partition index
    refine ⟨coordinate, ?_, rfl⟩
    exact ⟨index, Finset.mem_subtype.mpr hselected, rfl⟩

/-- A partition together with a selected set of its singleton blocks. -/
structure PartitionDirectChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) where
  partition : Finpartition support
  direct : Finset (Index J noiseDim)
  direct_subset : direct ⊆ support
  singleton_parts : ∀ j ∈ direct, {j} ∈ partition.parts
  deriving DecidableEq

@[ext]
theorem PartitionDirectChoice.ext {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    {left right : PartitionDirectChoice J noiseDim support}
    (hpartition : left.partition = right.partition)
    (hdirect : left.direct = right.direct) : left = right := by
  cases left
  cases right
  simp_all

/-- The unique first-order local choice: one block carrying the whole support and no direct bridge
coordinate. -/
noncomputable def linearPartitionDirectChoice {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (hsupport : support.Nonempty) :
    PartitionDirectChoice J noiseDim support where
  partition := Finpartition.indiscrete hsupport.ne_empty
  direct := ∅
  direct_subset := Finset.empty_subset _
  singleton_parts := by simp

/-- On support of cardinality at least two, every local choice which is not nonlinear is the
unique linear choice. -/
theorem PartitionDirectChoice.eq_linear_of_not_two_le {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (hcard : 2 ≤ support.card)
    (choice : PartitionDirectChoice J noiseDim support)
    (hlinear : ¬2 ≤ choice.partition.parts.card) :
    choice = linearPartitionDirectChoice (Finset.card_pos.mp (by omega)) := by
  have hsupport : support.Nonempty := Finset.card_pos.mp (by omega)
  have hpartsNonempty := choice.partition.parts_nonempty hsupport.ne_empty
  have hpartsPositive := Finset.card_pos.mpr hpartsNonempty
  have hpartsCard : choice.partition.parts.card = 1 := by omega
  obtain ⟨block, hparts⟩ := Finset.card_eq_one.mp hpartsCard
  have hblock : block = support := by
    have hsup := choice.partition.sup_parts
    rw [hparts] at hsup
    simpa using hsup
  have hpartition :
      choice.partition = Finpartition.indiscrete hsupport.ne_empty := by
    apply Finpartition.ext
    ext candidate
    rw [hparts, hblock]
    simp
  have hdirect : choice.direct = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hsingleton := choice.singleton_parts j hj
    rw [hparts] at hsingleton
    have hsingletonBlock : ({j} : Finset (Index J noiseDim)) = support := by
      exact (Finset.mem_singleton.mp hsingleton).trans hblock
    have hsingletonCard := congrArg Finset.card hsingletonBlock
    simp at hsingletonCard
    omega
  apply PartitionDirectChoice.ext hpartition hdirect

/-- Splitting off the partition field exposes the local singleton selection independently for
each partition. -/
def sigmaDirectChoiceEquivPartitionDirectChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :
    (Σ partition : Finpartition support, DirectChoiceForPartition partition) ≃
      PartitionDirectChoice J noiseDim support where
  toFun choice :=
    { partition := choice.1
      direct := choice.2.direct
      direct_subset := choice.2.direct_subset
      singleton_parts := choice.2.singleton_parts }
  invFun choice :=
    ⟨choice.partition,
      { direct := choice.direct
        direct_subset := choice.direct_subset
        singleton_parts := choice.singleton_parts }⟩
  left_inv choice := by rcases choice with ⟨partition, directChoice⟩; cases directChoice; rfl
  right_inv choice := by cases choice; rfl

/-- The full local multilinear selections, first partition by partition and then globally, are
equivalent to `PartitionDirectChoice`. -/
noncomputable def sigmaBlockSelectionEquivPartitionDirectChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :
    (Σ partition : Finpartition support, SingletonBlockSelection partition) ≃
      PartitionDirectChoice J noiseDim support :=
  (Equiv.sigmaCongrRight fun partition ↦
    singletonBlockSelectionEquivDirectChoice partition).trans
      (sigmaDirectChoiceEquivPartitionDirectChoice J noiseDim support)

noncomputable instance instFintypePartitionDirectChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    Fintype (PartitionDirectChoice J noiseDim support) :=
  Fintype.ofEquiv
    (Σ partition : Finpartition support, SingletonBlockSelection partition)
    (sigmaBlockSelectionEquivPartitionDirectChoice J noiseDim support)

/-- A block remaining after the selected singleton coordinates are removed was already a block of
the original partition. -/
theorem PartitionDirectChoice.avoid_part_mem_partition {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : PartitionDirectChoice J noiseDim support)
    (block : (choice.partition.avoid choice.direct).parts) :
    block.1 ∈ choice.partition.parts := by
  have hpartition := finpartitionInsertSingletons_avoid_of_singleton_parts
    choice.partition choice.direct_subset choice.singleton_parts
  have hmember : block.1 ∈
      (finpartitionInsertSingletons choice.direct_subset
        (choice.partition.avoid choice.direct)).parts := by
    rw [finpartitionInsertSingletons_parts]
    exact Finset.mem_union_left _ block.2
  exact (congrArg Finpartition.parts hpartition) ▸ hmember

/-- The blocks of the original partition split into selected singleton blocks and the blocks of
the partition of the complement.  This equivalence is the exact local reordering used by the
paper: direct inputs first, recursive children second. -/
noncomputable def PartitionDirectChoice.directSumAvoidEquivParts {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : PartitionDirectChoice J noiseDim support) :
    choice.direct ⊕ (choice.partition.avoid choice.direct).parts ≃
      choice.partition.parts := by
  let toPart : choice.direct ⊕ (choice.partition.avoid choice.direct).parts →
      choice.partition.parts
    | .inl coordinate =>
        ⟨{coordinate.1}, choice.singleton_parts coordinate.1 coordinate.2⟩
    | .inr block => ⟨block.1, choice.avoid_part_mem_partition block⟩
  apply Equiv.ofBijective toPart
  constructor
  · intro left right heq
    cases left with
    | inl leftCoordinate =>
        cases right with
        | inl rightCoordinate =>
            simp only [toPart] at heq
            apply congrArg Sum.inl
            apply Subtype.ext
            exact Finset.singleton_injective (congrArg Subtype.val heq)
        | inr rightBlock =>
            simp only [toPart] at heq
            exfalso
            have hmember : leftCoordinate.1 ∈ rightBlock.1 := by
              rw [← congrArg Subtype.val heq]
              exact Finset.mem_singleton_self _
            exact (Finset.mem_sdiff.mp
              ((choice.partition.avoid choice.direct).subset rightBlock.2 hmember)).2
                leftCoordinate.2
    | inr leftBlock =>
        cases right with
        | inl rightCoordinate =>
            simp only [toPart] at heq
            exfalso
            have hmember : rightCoordinate.1 ∈ leftBlock.1 := by
              rw [congrArg Subtype.val heq]
              exact Finset.mem_singleton_self _
            exact (Finset.mem_sdiff.mp
              ((choice.partition.avoid choice.direct).subset leftBlock.2 hmember)).2
                rightCoordinate.2
        | inr rightBlock =>
            simp only [toPart] at heq
            apply congrArg Sum.inr
            apply Subtype.ext
            exact congrArg (fun block : choice.partition.parts ↦ block.1) heq
  · intro block
    have hpartition := finpartitionInsertSingletons_avoid_of_singleton_parts
      choice.partition choice.direct_subset choice.singleton_parts
    have hparts : block.1 ∈
        (choice.partition.avoid choice.direct).parts ∪ choice.direct.image ({·}) := by
      rw [← finpartitionInsertSingletons_parts choice.direct_subset
        (choice.partition.avoid choice.direct)]
      rw [hpartition]
      exact block.2
    rcases Finset.mem_union.mp hparts with hremaining | hsingleton
    · exact ⟨Sum.inr ⟨block.1, hremaining⟩, Subtype.ext rfl⟩
    · obtain ⟨coordinate, hcoordinate, hblock⟩ := Finset.mem_image.mp hsingleton
      exact ⟨Sum.inl ⟨coordinate, hcoordinate⟩, Subtype.ext hblock⟩

/-- The permutation from the paper's direct-first convention to the canonical block order of the
original Faà di Bruno partition. -/
noncomputable def PartitionDirectChoice.directionEquiv {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : PartitionDirectChoice J noiseDim support) :
    Fin (choice.direct.card +
      (orderedPartitionBlocks (choice.partition.avoid choice.direct)).length) ≃
      Fin (orderedPartitionBlocks choice.partition).length :=
  finSumFinEquiv.symm |>.trans
    ((Equiv.sumCongr choice.direct.equivFin.symm
      (orderedPartitionBlocksEquiv (choice.partition.avoid choice.direct))).trans
        (choice.directSumAvoidEquivParts.trans
          (orderedPartitionBlocksEquiv choice.partition).symm))

@[simp]
theorem PartitionDirectChoice.directionEquiv_castAdd_block {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : PartitionDirectChoice J noiseDim support)
    (k : Fin choice.direct.card) :
    orderedPartitionBlocksEquiv choice.partition
        (choice.directionEquiv (Fin.castAdd
          (orderedPartitionBlocks (choice.partition.avoid choice.direct)).length k)) =
      ⟨{(choice.direct.equivFin.symm k).1},
        choice.singleton_parts _ (choice.direct.equivFin.symm k).2⟩ := by
  simp [PartitionDirectChoice.directionEquiv,
    PartitionDirectChoice.directSumAvoidEquivParts]
  rfl

@[simp]
theorem PartitionDirectChoice.directionEquiv_natAdd_block {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : PartitionDirectChoice J noiseDim support)
    (k : Fin (orderedPartitionBlocks
      (choice.partition.avoid choice.direct)).length) :
    (orderedPartitionBlocksEquiv choice.partition
        (choice.directionEquiv (Fin.natAdd choice.direct.card k))).1 =
      (orderedPartitionBlocksEquiv
        (choice.partition.avoid choice.direct) k).1 := by
  simp [PartitionDirectChoice.directionEquiv,
    PartitionDirectChoice.directSumAvoidEquivParts]
  rfl

/-- A direct coordinate set together with a partition of the remaining coordinates. -/
structure DirectPartitionChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) where
  direct : Finset (Index J noiseDim)
  direct_subset : direct ⊆ support
  partition : Finpartition (support \ direct)
  deriving DecidableEq

/-- Selecting singleton blocks of a partition is equivalent to removing those blocks and
remembering their coordinates as the direct set. -/
noncomputable def partitionDirectEquivDirectPartition (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :
    PartitionDirectChoice J noiseDim support ≃
      DirectPartitionChoice J noiseDim support where
  toFun choice :=
    ⟨choice.direct, choice.direct_subset,
      choice.partition.avoid choice.direct⟩
  invFun choice :=
    { partition := finpartitionInsertSingletons choice.direct_subset choice.partition
      direct := choice.direct
      direct_subset := choice.direct_subset
      singleton_parts := by
        intro j hj
        rw [finpartitionInsertSingletons_parts]
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨j, hj, rfl⟩) }
  left_inv choice := by
    cases choice with
    | mk partition direct direct_subset singleton_parts =>
        dsimp
        have hpartition := finpartitionInsertSingletons_avoid_of_singleton_parts
          partition direct_subset singleton_parts
        rw [PartitionDirectChoice.mk.injEq]
        exact ⟨hpartition, rfl⟩
  right_inv choice := by
    cases choice with
    | mk direct direct_subset partition =>
        dsimp
        have hpartition := finpartitionInsertSingletons_avoid direct_subset partition
        rw [DirectPartitionChoice.mk.injEq]
        exact ⟨rfl, heq_of_eq hpartition⟩

end
end TimeDependentLattice.Trees

namespace TimeDependentLattice.Trees
noncomputable section
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Analysis

/-- Removing selected singleton blocks preserves the total local derivative order. -/
theorem partitionDirectEquiv_localOrder {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : PartitionDirectChoice J noiseDim support) :
    let converted := partitionDirectEquivDirectPartition J noiseDim support choice
    converted.direct.card + converted.partition.parts.card =
      choice.partition.parts.card := by
  dsimp only
  change choice.direct.card + (choice.partition.avoid choice.direct).parts.card =
    choice.partition.parts.card
  have hpartition := finpartitionInsertSingletons_avoid_of_singleton_parts
    choice.partition choice.direct_subset choice.singleton_parts
  have hcard := finpartitionInsertSingletons_card choice.direct_subset
    (choice.partition.avoid choice.direct)
  rw [hpartition] at hcard
  omega

/-- Choices in the local expansion whose total derivative order is nonlinear. -/
abbrev NonlinearPartitionDirectChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :=
  {choice : PartitionDirectChoice J noiseDim support //
    2 ≤ choice.partition.parts.card}

/-- For support of order at least two, all local choices consist of the unique linear term plus
the nonlinear choices used as drift-tree roots. -/
noncomputable def partitionDirectChoiceEquivOptionNonlinear {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} (hcard : 2 ≤ support.card) :
    PartitionDirectChoice J noiseDim support ≃
      Option (NonlinearPartitionDirectChoice J noiseDim support) where
  toFun choice :=
    if hnonlinear : 2 ≤ choice.partition.parts.card then some ⟨choice, hnonlinear⟩
    else none
  invFun
    | none => linearPartitionDirectChoice (Finset.card_pos.mp (by omega))
    | some choice => choice.1
  left_inv choice := by
    by_cases hnonlinear : 2 ≤ choice.partition.parts.card
    · simp [hnonlinear]
    · rw [choice.eq_linear_of_not_two_le hcard hnonlinear]
      have hlinear : ¬2 ≤
          (linearPartitionDirectChoice
            (Finset.card_pos.mp (by omega : 0 < support.card)) :
              PartitionDirectChoice J noiseDim support).partition.parts.card := by
        simp [linearPartitionDirectChoice]
      simp [hlinear]
  right_inv choice := by
    cases choice with
    | none =>
        simp [linearPartitionDirectChoice]
    | some choice =>
        simp [choice.2]

private abbrev NonlinearDirectPartitionChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :=
  {choice : DirectPartitionChoice J noiseDim support //
    2 ≤ choice.direct.card + choice.partition.parts.card}

private noncomputable def nonlinearPartitionDirectEquivDirectPartition
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    NonlinearPartitionDirectChoice J noiseDim support ≃
      NonlinearDirectPartitionChoice J noiseDim support :=
  Equiv.subtypeEquiv (partitionDirectEquivDirectPartition J noiseDim support)
    (fun choice ↦ by
      rw [partitionDirectEquiv_localOrder choice])

private def nonlinearDirectPartitionEquivDriftRootChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    NonlinearDirectPartitionChoice J noiseDim support ≃
      DriftRootChoice J noiseDim support where
  toFun choice :=
    { direct := choice.1.direct
      direct_subset := choice.1.direct_subset
      partition := choice.1.partition
      local_order := choice.2 }
  invFun root :=
    ⟨⟨root.direct, root.direct_subset, root.partition⟩, root.local_order⟩
  left_inv choice := by cases choice; rfl
  right_inv root := by cases root; rfl

/-- The nonlinear terms produced by singleton-block expansion are exactly the paper's drift-root
choices. -/
noncomputable def nonlinearPartitionDirectEquivDriftRootChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    NonlinearPartitionDirectChoice J noiseDim support ≃
      DriftRootChoice J noiseDim support :=
  (nonlinearPartitionDirectEquivDirectPartition J noiseDim support).trans
    (nonlinearDirectPartitionEquivDriftRootChoice J noiseDim support)

noncomputable instance instFintypeNonlinearPartitionDirectChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    Fintype (NonlinearPartitionDirectChoice J noiseDim support) :=
  Fintype.ofEquiv (DriftRootChoice J noiseDim support)
    (nonlinearPartitionDirectEquivDriftRootChoice J noiseDim support).symm

/-- Every recursive child block of a nonlinear drift root has strictly smaller support.  This is
the well-founded measure used in the tree-expansion induction. -/
theorem DriftRootChoice.block_card_lt_support {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)}
    (root : DriftRootChoice J noiseDim support) (block : root.partition.parts) :
    block.1.card < support.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro j hj
    exact (Finset.mem_sdiff.mp (root.partition.subset block.2 hj)).1
  · intro hblock
    have hdirect : root.direct = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hjSupport := root.direct_subset hj
      have hjBlock : j ∈ block.1 := by
        rw [hblock]
        exact hjSupport
      exact (Finset.mem_sdiff.mp (root.partition.subset block.2 hjBlock)).2 hj
    have hpartsLe : root.partition.parts.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro left right hleft hright
      obtain ⟨x, hx⟩ := root.partition.nonempty_of_mem_parts hleft
      have hxSupport : x ∈ support := by
        exact (Finset.mem_sdiff.mp (root.partition.subset hleft hx)).1
      have hxBlock : x ∈ block.1 := by
        rw [hblock]
        exact hxSupport
      have hleftBlock := root.partition.eq_of_mem_parts hleft block.2 hx hxBlock
      obtain ⟨y, hy⟩ := root.partition.nonempty_of_mem_parts hright
      have hySupport : y ∈ support := by
        exact (Finset.mem_sdiff.mp (root.partition.subset hright hy)).1
      have hyBlock : y ∈ block.1 := by
        rw [hblock]
        exact hySupport
      have hrightBlock := root.partition.eq_of_mem_parts hright block.2 hy hyBlock
      exact hleftBlock.trans hrightBlock.symm
    have hpartsPositive : 0 < root.partition.parts.card :=
      Finset.card_pos.mpr ⟨block.1, block.2⟩
    have hpartsCard : root.partition.parts.card = 1 := by omega
    have horder := root.local_order
    have hdirectCard : root.direct.card = 0 := by rw [hdirect, Finset.card_empty]
    rw [hdirectCard, hpartsCard, zero_add] at horder
    omega

end
end TimeDependentLattice.Trees

