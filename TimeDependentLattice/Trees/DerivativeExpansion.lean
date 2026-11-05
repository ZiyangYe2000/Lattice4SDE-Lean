/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.Value

/-!
# Derivative tree expansion

This module proves the paper's main combinatorial identity for derivatives of the terminal
Euler payoff.  It first expands each Faà di Bruno block into a direct bridge direction or a
compensated state derivative, removes the bridge directions which vanish at the terminal time,
recursively applies the state-derivative expansion, and finally reindexes the resulting sum by
the admissible timed payoff trees.
-/

namespace TimeDependentLattice.Trees
noncomputable section
open scoped BigOperators ContDiff
open TimeDependentLattice
open TimeDependentLattice.Analysis
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Euler

/-! ## Reordering one payoff-root partition -/

/-- A block left after removing the chosen singleton direct blocks is still a block of the
original Faà di Bruno partition. -/
theorem DirectChoiceForPartition.avoid_part_mem_partition
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    {partition : Finpartition support} (choice : DirectChoiceForPartition partition)
    (block : (partition.avoid choice.direct).parts) :
    block.1 ∈ partition.parts := by
  let bundled : PartitionDirectChoice J noiseDim support :=
    { partition := partition
      direct := choice.direct
      direct_subset := choice.direct_subset
      singleton_parts := choice.singleton_parts }
  exact bundled.avoid_part_mem_partition block

/-- The local multilinear term obtained after putting the selected direct singleton blocks
first and leaving the other partition blocks as recursive child directions. -/
def DirectChoiceForPartition.genericTerm
    {J noiseDim : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {support : Finset (Index J noiseDim)}
    {partition : Finpartition support} (choice : DirectChoiceForPartition partition)
    (outer : E → F) (point : E)
    (directValue : Index J noiseDim → E)
    (childValue : partition.parts → E) : F :=
  let remaining := partition.avoid choice.direct
  let blocks := orderedPartitionBlocks remaining
  iteratedFDeriv ℝ (choice.direct.card + blocks.length) outer point
    (Fin.addCases
      (fun k ↦ directValue (choice.direct.equivFin.symm k).val)
      (fun i ↦ childValue ⟨(orderedPartitionBlocksEquiv remaining i).1,
        choice.avoid_part_mem_partition
          (orderedPartitionBlocksEquiv remaining i)⟩))

/-- The direct direction offered by a singleton block of a fixed partition. -/
def genericPartitionDirectDirection
    {J noiseDim : ℕ} {E : Type*} [Zero E]
    {support : Finset (Index J noiseDim)}
    (partition : Finpartition support) (directValue : Index J noiseDim → E) :
    Fin (orderedPartitionBlocks partition).length → E := fun i ↦
  if hcard : (orderedPartitionBlocksEquiv partition i).1.card = 1 then
    directValue
      (finpartitionSingletonCoordinate (orderedPartitionBlocksEquiv partition i) hcard)
  else 0

/-- The recursive child direction carried by a block of a fixed partition. -/
def genericPartitionChildDirection
    {J noiseDim : ℕ} {E : Type*}
    {support : Finset (Index J noiseDim)}
    (partition : Finpartition support) (childValue : partition.parts → E) :
    Fin (orderedPartitionBlocks partition).length → E := fun i ↦
  childValue (orderedPartitionBlocksEquiv partition i)

/-- Symmetry of smooth iterated derivatives identifies the canonical partition order with the
paper's convention in which direct directions precede recursive children. -/
theorem DirectChoiceForPartition.genericExpandedTerm_eq_genericTerm
    {J noiseDim : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {support : Finset (Index J noiseDim)}
    (partition : Finpartition support)
    (choice : DirectChoiceForPartition partition)
    (outer : E → F) (point : E)
    (directValue : Index J noiseDim → E)
    (childValue : partition.parts → E) (hOuter : ContDiff ℝ ∞ outer) :
    let selection :=
      (singletonBlockSelectionEquivDirectChoice partition).symm choice
    iteratedFDeriv ℝ (orderedPartitionBlocks partition).length outer point
        (selection.1.piecewise
          (genericPartitionDirectDirection partition directValue)
          (genericPartitionChildDirection partition childValue)) =
      choice.genericTerm outer point directValue childValue := by
  dsimp only
  let selection :=
    (singletonBlockSelectionEquivDirectChoice partition).symm choice
  let bundled : PartitionDirectChoice J noiseDim support :=
    { partition := partition
      direct := choice.direct
      direct_subset := choice.direct_subset
      singleton_parts := choice.singleton_parts }
  let originalDirections := selection.1.piecewise
    (genericPartitionDirectDirection partition directValue)
    (genericPartitionChildDirection partition childValue)
  let remaining := partition.avoid choice.direct
  let targetDirections : Fin (choice.direct.card +
      (orderedPartitionBlocks remaining).length) → E :=
    Fin.addCases
      (fun k ↦ directValue (choice.direct.equivFin.symm k).val)
      (fun i ↦ childValue
        ⟨(orderedPartitionBlocksEquiv remaining i).1,
          choice.avoid_part_mem_partition
            (orderedPartitionBlocksEquiv remaining i)⟩)
  have hdirections :
      originalDirections ∘ bundled.directionEquiv = targetDirections := by
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro k
      simp only [Function.comp_apply, targetDirections]
      rw [Fin.addCases_left]
      let originalIndex := bundled.directionEquiv
        (Fin.castAdd (orderedPartitionBlocks remaining).length k)
      have hblock := bundled.directionEquiv_castAdd_block k
      have hblockValue := congrArg Subtype.val hblock
      have hblockValue' :
          (orderedPartitionBlocksEquiv partition originalIndex).1 =
            {(choice.direct.equivFin.symm k).1} := by
        simpa [bundled, originalIndex, remaining] using hblockValue
      have hcard :
          (orderedPartitionBlocksEquiv partition originalIndex).1.card = 1 := by
        rw [hblockValue']
        simp
      have hcoordinate :
          finpartitionSingletonCoordinate
              (orderedPartitionBlocksEquiv partition originalIndex) hcard =
            (choice.direct.equivFin.symm k).1 := by
        apply Finset.mem_singleton.mp
        rw [← hblockValue']
        exact finpartitionSingletonCoordinate_mem _ hcard
      have hchoice :
          singletonBlockSelectionEquivDirectChoice partition selection = choice := by
        exact (singletonBlockSelectionEquivDirectChoice partition).apply_symm_apply choice
      have hselected : originalIndex ∈ selection.1 := by
        apply (singletonBlockSelectionEquivDirectChoice_coordinate_mem
          partition selection originalIndex hcard).mp
        rw [hchoice, hcoordinate]
        exact (choice.direct.equivFin.symm k).2
      change selection.1.piecewise
        (genericPartitionDirectDirection partition directValue)
        (genericPartitionChildDirection partition childValue) originalIndex = _
      rw [Finset.piecewise_eq_of_mem selection.1 _ _ hselected]
      simp only [genericPartitionDirectDirection, hcard, dite_true, hcoordinate]
    · intro k
      simp only [Function.comp_apply, targetDirections]
      rw [Fin.addCases_right]
      let originalIndex := bundled.directionEquiv (Fin.natAdd choice.direct.card k)
      have hblock := bundled.directionEquiv_natAdd_block k
      have hblock' :
          (orderedPartitionBlocksEquiv partition originalIndex).1 =
            (orderedPartitionBlocksEquiv remaining k).1 := by
        simpa [bundled, originalIndex, remaining] using hblock
      have hnotSelected : originalIndex ∉ selection.1 := by
        intro hselected
        have hcard := selection.2 originalIndex hselected
        have hchoice :
            singletonBlockSelectionEquivDirectChoice partition selection = choice := by
          exact (singletonBlockSelectionEquivDirectChoice partition).apply_symm_apply choice
        have hdirect := (singletonBlockSelectionEquivDirectChoice_coordinate_mem
          partition selection originalIndex hcard).mpr hselected
        rw [hchoice] at hdirect
        have hcoordinateMember :
            finpartitionSingletonCoordinate
                (orderedPartitionBlocksEquiv partition originalIndex) hcard ∈
              (orderedPartitionBlocksEquiv remaining k).1 := by
          rw [← hblock']
          exact finpartitionSingletonCoordinate_mem _ hcard
        exact (Finset.mem_sdiff.mp
          (remaining.subset (orderedPartitionBlocksEquiv remaining k).2
            hcoordinateMember)).2 hdirect
      change selection.1.piecewise
        (genericPartitionDirectDirection partition directValue)
        (genericPartitionChildDirection partition childValue) originalIndex = _
      rw [Finset.piecewise_eq_of_notMem selection.1 _ _ hnotSelected]
      simp only [genericPartitionChildDirection]
      congr
      apply Subtype.ext
      exact hblock'
  have hperm := iteratedFDeriv_comp_equiv_directions_of_contDiff
    outer point originalDirections bundled.directionEquiv hOuter
  rw [hdirections] at hperm
  exact hperm.symm

/-! ## Terminal payoff root -/

/-- At the terminal Euler time, each payoff Faà di Bruno block splits into its compensated
state derivative and, for singleton blocks, its direct bridge coefficient. -/
theorem paperFinpartitionChainTerm_payoff_terminal_eq
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (payoff : Payoff stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    {u : Finset (Index J noiseDim)} (partition : Finpartition u)
    (z : Input J noiseDim) :
    paperFinpartitionChainTerm payoff
        (fun y ↦ stateNat drift diffusion T x₀ y (numSteps J)) partition z =
      let blocks := orderedPartitionBlocks partition
      let blockEquiv := orderedPartitionBlocksEquiv partition
      iteratedFDeriv ℝ blocks.length payoff
        (stateNat drift diffusion T x₀ z (numSteps J)) fun i ↦
          compensatedStateDerivative drift diffusion T x₀ (numSteps J)
              (blockEquiv i).1 z +
            if hcard : (blockEquiv i).1.card = 1 then
              diffusionCoefficient diffusion T
                (finpartitionSingletonCoordinate (blockEquiv i) hcard) T
            else 0 := by
  unfold paperFinpartitionChainTerm
  dsimp only
  congr 1
  funext i
  have hfun :
      (fun y : Input J noiseDim ↦
        stateNat drift diffusion T x₀ y (numSteps J)) =
        eulerDriftInput (J := J) drift diffusion T x₀ (numSteps J) := by
    funext y
    exact (eulerDriftInput_eq_stateNat
      drift diffusion T x₀ (numSteps J) y).symm
  rw [hfun]
  rw [mixedDerivative_eulerDriftInput_partitionBlock
    drift diffusion T x₀ hDrift (numSteps J) partition
      (orderedPartitionBlocksEquiv partition i) z]
  rw [gridTime_terminal]

/-- Multilinearity expands one payoff partition term over all choices of direct singleton
blocks. -/
theorem paperFinpartitionChainTerm_payoff_eq_sum_directChoices
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (payoff : Payoff stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (hPayoff : ContDiff ℝ ∞ payoff)
    {u : Finset (Index J noiseDim)} (partition : Finpartition u)
    (z : Input J noiseDim) :
    paperFinpartitionChainTerm payoff
        (fun y ↦ stateNat drift diffusion T x₀ y (numSteps J)) partition z =
      ∑ choice : DirectChoiceForPartition partition,
        choice.genericTerm payoff
          (stateNat drift diffusion T x₀ z (numSteps J))
          (fun j ↦ diffusionCoefficient diffusion T j T)
          (fun block ↦ compensatedStateDerivative drift diffusion T x₀
            (numSteps J) block.1 z) := by
  rw [paperFinpartitionChainTerm_payoff_terminal_eq
    drift payoff diffusion T x₀ hDrift partition z]
  dsimp only
  let derivative := iteratedFDeriv ℝ (orderedPartitionBlocks partition).length
    payoff (stateNat drift diffusion T x₀ z (numSteps J))
  let directValue := fun j : Index J noiseDim ↦
    diffusionCoefficient diffusion T j T
  let childValue := fun block : partition.parts ↦
    compensatedStateDerivative drift diffusion T x₀ (numSteps J) block.1 z
  let direct := genericPartitionDirectDirection partition directValue
  let child := genericPartitionChildDirection partition childValue
  change derivative (child + direct) = _
  rw [add_comm]
  rw [map_add_eq_sum_eligibleSelections derivative direct child
    (fun i ↦ (orderedPartitionBlocksEquiv partition i).1.card = 1)]
  · let equivalence := singletonBlockSelectionEquivDirectChoice partition
    calc
      (∑ selection : SingletonBlockSelection partition,
          derivative (selection.1.piecewise direct child)) =
          ∑ choice : DirectChoiceForPartition partition,
            derivative (((equivalence.symm choice).1).piecewise direct child) :=
        (equivalence.symm.sum_comp
          (fun selection ↦ derivative
            (selection.1.piecewise direct child))).symm
      _ = _ := by
        apply Fintype.sum_congr
        intro choice
        exact choice.genericExpandedTerm_eq_genericTerm partition payoff
          (stateNat drift diffusion T x₀ z (numSteps J)) directValue childValue hPayoff
  · intro i hi
    unfold direct genericPartitionDirectDirection
    split
    · rename_i hcard
      exact (hi hcard).elim
    · rfl

/-- A local direct choice all of whose selected coordinates are endpoint coordinates. -/
abbrev EndpointDirectChoiceForPartition
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (partition : Finpartition support) :=
  {choice : DirectChoiceForPartition partition //
    ∀ j ∈ choice.direct, IsEndpoint j}

/-- Any local payoff term selecting a detail coordinate directly vanishes at terminal time. -/
theorem DirectChoiceForPartition.payoff_genericTerm_eq_zero_of_not_endpoint
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    {partition : Finpartition support} (choice : DirectChoiceForPartition partition)
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (hT : T ≠ 0)
    (x₀ : State stateDim) (z : Input J noiseDim)
    (hbad : ¬∀ j ∈ choice.direct, IsEndpoint j) :
    choice.genericTerm payoff
        (stateNat drift diffusion T x₀ z (numSteps J))
        (fun j ↦ diffusionCoefficient diffusion T j T)
        (fun block ↦ compensatedStateDerivative drift diffusion T x₀
          (numSteps J) block.1 z) = 0 := by
  push Not at hbad
  obtain ⟨j, hj, hdetail⟩ := hbad
  cases j with
  | inl endpoint => simp [IsEndpoint] at hdetail
  | inr detail =>
      let k := choice.direct.equivFin ⟨Sum.inr detail, hj⟩
      unfold DirectChoiceForPartition.genericTerm
      apply (iteratedFDeriv ℝ
        (choice.direct.card +
          (orderedPartitionBlocks
            (partition.avoid choice.direct)).length)
        payoff (stateNat drift diffusion T x₀ z (numSteps J))).map_coord_zero
          (Fin.castAdd
            (orderedPartitionBlocks (partition.avoid choice.direct)).length k)
      rw [Fin.addCases_left]
      simp [k, diffusionCoefficient, coefficient_detail_terminal hT detail]

/-- Consequently the local sum can be restricted to endpoint direct choices. -/
theorem sum_payoff_genericTerm_eq_sum_endpointChoices
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (partition : Finpartition support)
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (hT : T ≠ 0)
    (x₀ : State stateDim) (z : Input J noiseDim) :
    (∑ choice : DirectChoiceForPartition partition,
      choice.genericTerm payoff
        (stateNat drift diffusion T x₀ z (numSteps J))
        (fun j ↦ diffusionCoefficient diffusion T j T)
        (fun block ↦ compensatedStateDerivative drift diffusion T x₀
          (numSteps J) block.1 z)) =
      ∑ choice : EndpointDirectChoiceForPartition partition,
        choice.1.genericTerm payoff
          (stateNat drift diffusion T x₀ z (numSteps J))
          (fun j ↦ diffusionCoefficient diffusion T j T)
          (fun block ↦ compensatedStateDerivative drift diffusion T x₀
            (numSteps J) block.1 z) := by
  let endpoint : DirectChoiceForPartition partition → Prop := fun choice ↦
    ∀ j ∈ choice.direct, IsEndpoint j
  let term : DirectChoiceForPartition partition → ℝ := fun choice ↦
    choice.genericTerm payoff
      (stateNat drift diffusion T x₀ z (numSteps J))
      (fun j ↦ diffusionCoefficient diffusion T j T)
      (fun block ↦ compensatedStateDerivative drift diffusion T x₀
        (numSteps J) block.1 z)
  have hinvalid :
      (∑ choice : {choice : DirectChoiceForPartition partition // ¬endpoint choice},
        term choice.1) = 0 := by
    apply Fintype.sum_eq_zero
    intro choice
    exact choice.1.payoff_genericTerm_eq_zero_of_not_endpoint
      drift payoff diffusion T hT x₀ z choice.2
  have hsplit := Fintype.sum_subtype_add_sum_subtype endpoint term
  rw [hinvalid, add_zero] at hsplit
  exact hsplit.symm

/-! ## Finite codes for complete payoff expansions -/

/-- A Faà di Bruno partition together with an endpoint-only direct singleton selection. -/
abbrev EndpointPartitionDirectChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :=
  {choice : PartitionDirectChoice J noiseDim support //
    ∀ j ∈ choice.direct, IsEndpoint j}

/-- Bundling the partition and its endpoint direct choice does not change the indexing set. -/
def sigmaEndpointDirectChoiceEquivEndpointPartitionDirectChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    (Σ partition : Finpartition support,
      EndpointDirectChoiceForPartition partition) ≃
        EndpointPartitionDirectChoice J noiseDim support where
  toFun choice :=
    ⟨{ partition := choice.1
       direct := choice.2.1.direct
       direct_subset := choice.2.1.direct_subset
       singleton_parts := choice.2.1.singleton_parts }, choice.2.2⟩
  invFun choice :=
    ⟨choice.1.partition,
      ⟨{ direct := choice.1.direct
         direct_subset := choice.1.direct_subset
         singleton_parts := choice.1.singleton_parts }, choice.2⟩⟩
  left_inv choice := by
    rcases choice with ⟨partition, directChoice, endpoint⟩
    cases directChoice
    rfl
  right_inv choice := by
    rcases choice with ⟨choice, endpoint⟩
    cases choice
    rfl

noncomputable instance instFintypeEndpointPartitionDirectChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    Fintype (EndpointPartitionDirectChoice J noiseDim support) :=
  Fintype.ofEquiv
    (Σ partition : Finpartition support,
      EndpointDirectChoiceForPartition partition)
    (sigmaEndpointDirectChoiceEquivEndpointPartitionDirectChoice
      J noiseDim support)

/-- The paper's payoff-root data: endpoint direct labels and a partition of their complement. -/
abbrev PayoffRootChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :=
  {root : DirectPartitionChoice J noiseDim support //
    ∀ j ∈ root.direct, IsEndpoint j}

/-- Removing the selected singleton blocks converts an expanded Faà di Bruno partition into
exactly the paper's payoff-root data. -/
noncomputable def endpointPartitionDirectEquivPayoffRootChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    EndpointPartitionDirectChoice J noiseDim support ≃
      PayoffRootChoice J noiseDim support :=
  Equiv.subtypeEquiv
    (partitionDirectEquivDirectPartition J noiseDim support)
    (fun _ ↦ Iff.rfl)

noncomputable instance instFintypePayoffRootChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    Fintype (PayoffRootChoice J noiseDim support) :=
  Fintype.ofEquiv (EndpointPartitionDirectChoice J noiseDim support)
    (endpointPartitionDirectEquivPayoffRootChoice J noiseDim support)

/-- A payoff-root choice and a complete recursive drift expansion for every child block. -/
def PayoffExpansionCode (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) (m : ℕ) :=
  Σ root : PayoffRootChoice J noiseDim support,
    ∀ block : root.1.partition.parts,
      DriftExpansionChoice J noiseDim m block.1

/-- Forget the auxiliary root bundling and obtain the project's complete payoff choice. -/
def PayoffExpansionCode.toChoice
    {J noiseDim m : ℕ} {support : Finset (Index J noiseDim)} :
    PayoffExpansionCode J noiseDim support m →
      PayoffExpansionChoice J noiseDim support m
  | ⟨root, children⟩ =>
      { direct := root.1.direct
        direct_subset := root.1.direct_subset
        direct_endpoint := root.2
        partition := root.1.partition
        children := children }

/-- Bundle a complete payoff choice into its payoff-root code. -/
def PayoffExpansionChoice.toCode
    {J noiseDim m : ℕ} {support : Finset (Index J noiseDim)} :
    PayoffExpansionChoice J noiseDim support m →
      PayoffExpansionCode J noiseDim support m
  | choice =>
      ⟨⟨⟨choice.direct, choice.direct_subset, choice.partition⟩,
        choice.direct_endpoint⟩, choice.children⟩

/-- Complete payoff codes and complete payoff expansion choices are equivalent. -/
def payoffExpansionCodeEquivChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) (m : ℕ) :
    PayoffExpansionCode J noiseDim support m ≃
      PayoffExpansionChoice J noiseDim support m where
  toFun := PayoffExpansionCode.toChoice
  invFun := PayoffExpansionChoice.toCode
  left_inv code := by rcases code with ⟨⟨root, endpoint⟩, children⟩; cases root; rfl
  right_inv choice := by cases choice; rfl

noncomputable instance instFintypePayoffRootChildChoices
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) (m : ℕ)
    (root : PayoffRootChoice J noiseDim support) :
    Fintype (∀ block : root.1.partition.parts,
      DriftExpansionChoice J noiseDim m block.1) :=
  Pi.instFintype

noncomputable instance instFintypePayoffExpansionCode
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) (m : ℕ) :
    Fintype (PayoffExpansionCode J noiseDim support m) := by
  unfold PayoffExpansionCode
  infer_instance

/-- The same complete code before selected singleton blocks are removed from the original
Faà di Bruno partition. -/
def EndpointPayoffExpansionCode (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) (m : ℕ) :=
  Σ root : EndpointPartitionDirectChoice J noiseDim support,
    ∀ block : (root.1.partition.avoid root.1.direct).parts,
      DriftExpansionChoice J noiseDim m block.1

/-- Convert the pre-removal code directly to a complete payoff expansion choice. -/
def EndpointPayoffExpansionCode.toChoice
    {J noiseDim m : ℕ} {support : Finset (Index J noiseDim)} :
    EndpointPayoffExpansionCode J noiseDim support m →
      PayoffExpansionChoice J noiseDim support m
  | ⟨root, children⟩ =>
      { direct := root.1.direct
        direct_subset := root.1.direct_subset
        direct_endpoint := root.2
        partition := root.1.partition.avoid root.1.direct
        children := children }

noncomputable instance instFintypeEndpointRootChildChoices
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) (m : ℕ)
    (root : EndpointPartitionDirectChoice J noiseDim support) :
    Fintype (∀ block : (root.1.partition.avoid root.1.direct).parts,
      DriftExpansionChoice J noiseDim m block.1) :=
  Pi.instFintype

noncomputable instance instFintypeEndpointPayoffExpansionCode
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) (m : ℕ) :
    Fintype (EndpointPayoffExpansionCode J noiseDim support m) := by
  unfold EndpointPayoffExpansionCode
  infer_instance

/-- Removing selected singleton blocks gives an equivalence between the two complete codes. -/
noncomputable def endpointPayoffExpansionCodeEquivPayoffExpansionCode
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) (m : ℕ) :
    EndpointPayoffExpansionCode J noiseDim support m ≃
      PayoffExpansionCode J noiseDim support m :=
  Equiv.sigmaCongr
    (endpointPartitionDirectEquivPayoffRootChoice J noiseDim support)
    (fun _ ↦ Equiv.refl _)

/-- Substituting the proved state-derivative expansion into every remaining root block expands
one endpoint root term over all simultaneous recursive child choices. -/
theorem EndpointPartitionDirectChoice.genericTerm_eq_sum_payoffChoices
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (root : EndpointPartitionDirectChoice J noiseDim support)
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Input J noiseDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (hPayoff : ContDiff ℝ ∞ payoff) :
    let localChoice : DirectChoiceForPartition root.1.partition :=
      { direct := root.1.direct
        direct_subset := root.1.direct_subset
        singleton_parts := root.1.singleton_parts }
    localChoice.genericTerm payoff
        (stateNat drift diffusion T x₀ z (numSteps J))
        (fun j ↦ diffusionCoefficient diffusion T j T)
        (fun block ↦ compensatedStateDerivative drift diffusion T x₀
          (numSteps J) block.1 z) =
      ∑ children : ∀ block :
          (root.1.partition.avoid root.1.direct).parts,
          DriftExpansionChoice J noiseDim (numSteps J) block.1,
        (show PayoffExpansionChoice J noiseDim support (numSteps J) from
          { direct := root.1.direct
            direct_subset := root.1.direct_subset
            direct_endpoint := root.2
            partition := root.1.partition.avoid root.1.direct
            children := children }).value drift payoff diffusion T x₀ z := by
  dsimp only
  let remaining := root.1.partition.avoid root.1.direct
  let blocks := orderedPartitionBlocks remaining
  let blockEquiv := orderedPartitionBlocksEquiv remaining
  let derivative := iteratedFDeriv ℝ (root.1.direct.card + blocks.length)
    payoff (stateNat drift diffusion T x₀ z (numSteps J))
  let directValues : Fin root.1.direct.card → State stateDim := fun k ↦
    diffusionCoefficient diffusion T (root.1.direct.equivFin.symm k).val T
  let α : Fin blocks.length → Type := fun i ↦
    DriftExpansionChoice J noiseDim (numSteps J) (blockEquiv i).1
  let g : ∀ i, α i → State stateDim := fun _ choice ↦
    choice.value drift diffusion T x₀ z
  have hchild (i : Fin blocks.length) :
      compensatedStateDerivative drift diffusion T x₀ (numSteps J)
          (blockEquiv i).1 z =
        driftExpansionSum (parentTime := numSteps J)
          (support := (blockEquiv i).1) drift diffusion T x₀ z := by
    apply compensatedStateDerivative_eq_driftExpansionSum
      drift diffusion T x₀ hDrift
    exact remaining.nonempty_of_mem_parts (blockEquiv i).2
  unfold DirectChoiceForPartition.genericTerm
  dsimp only
  change derivative (Fin.addCases directValues (fun i ↦
    compensatedStateDerivative drift diffusion T x₀ (numSteps J)
      (blockEquiv i).1 z)) = _
  simp_rw [hchild]
  have hmap := map_sum_with_fixed_prefix derivative directValues α g
  have hsum (i : Fin blocks.length) :
      (∑ choice, g i choice) =
        driftExpansionSum (parentTime := numSteps J)
          (support := (blockEquiv i).1) drift diffusion T x₀ z := by
    rfl
  simp_rw [hsum] at hmap
  let childEquiv := Equiv.piCongrLeft
    (fun block : remaining.parts ↦
      DriftExpansionChoice J noiseDim (numSteps J) block.1) blockEquiv
  rw [← childEquiv.sum_comp]
  rw [hmap]
  apply Fintype.sum_congr
  intro selection
  let childValues := blocks.map fun block ↦
    (childEquiv selection block).value drift diffusion T x₀ z
  let targetDirections := vertexDirections root.1.direct
    (fun j ↦ diffusionCoefficient diffusion T j T) childValues
  let reindex : Fin (root.1.direct.card + blocks.length) ≃
      Fin (root.1.direct.card + childValues.length) :=
    finCongr (by simp [childValues])
  have hdirections :
      targetDirections ∘ reindex =
        Fin.addCases directValues (fun i ↦ g i (selection i)) := by
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro k
      have hreindex : reindex (Fin.castAdd blocks.length k) =
          Fin.castAdd childValues.length k := by
        apply Fin.ext
        simp only [reindex, finCongr_apply, Fin.val_cast, Fin.val_castAdd]
      rw [Function.comp_apply, hreindex]
      unfold targetDirections vertexDirections
      rw [Fin.addCases_left, Fin.addCases_left]
    · intro k
      let targetIndex : Fin childValues.length :=
        ⟨k.val, by simp [childValues]⟩
      have hreindex : reindex (Fin.natAdd root.1.direct.card k) =
          Fin.natAdd root.1.direct.card targetIndex := by
        apply Fin.ext
        simp only [reindex, finCongr_apply, Fin.val_cast, Fin.val_natAdd,
          targetIndex]
      rw [Function.comp_apply, hreindex]
      unfold targetDirections vertexDirections
      rw [Fin.addCases_right, Fin.addCases_right]
      rw [List.get_eq_getElem]
      unfold childValues
      rw [List.getElem_map]
      have hblock : blocks[k.val] = blockEquiv k := by
        change (orderedPartitionBlocks remaining)[k.val] = blockEquiv k
        rw [← List.get_eq_getElem]
        exact (orderedPartitionBlocksEquiv_apply remaining k).symm
      rw [hblock]
      have hchoice : childEquiv selection (blockEquiv k) = selection k := by
        simp [childEquiv]
      rw [hchoice]
  have hperm := iteratedFDeriv_comp_equiv_directions_of_contDiff
    payoff (stateNat drift diffusion T x₀ z (numSteps J))
    targetDirections reindex hPayoff
  rw [hdirections] at hperm
  exact hperm

/-- The terminal payoff derivative is the finite sum over complete recursive payoff
expansion choices. -/
theorem mixedDerivative_terminalPayoff_eq_payoffExpansionSum
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (hT : T ≠ 0)
    (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (hPayoff : ContDiff ℝ ∞ payoff)
    (z : Input J noiseDim) (support : Finset (Index J noiseDim)) :
    mixedDerivative
        (fun y ↦ payoff (stateNat drift diffusion T x₀ y (numSteps J)))
        support z =
      payoffExpansionSum (m := numSteps J) (u := support)
        drift payoff diffusion T x₀ z := by
  rw [mixedDerivative_payoff_state_eq_sum_finpartitions
    drift payoff diffusion T x₀ hDrift hPayoff (numSteps J) support z]
  simp_rw [paperFinpartitionChainTerm_payoff_eq_sum_directChoices
    drift payoff diffusion T x₀ hDrift hPayoff]
  simp_rw [sum_payoff_genericTerm_eq_sum_endpointChoices
    (drift := drift) (payoff := payoff) (diffusion := diffusion)
    (T := T) (hT := hT) (x₀ := x₀) (z := z)]
  rw [← Fintype.sum_sigma']
  let firstEquiv :=
    sigmaEndpointDirectChoiceEquivEndpointPartitionDirectChoice
      J noiseDim support
  rw [← firstEquiv.symm.sum_comp]
  simp only [firstEquiv]
  calc
    (∑ root : EndpointPartitionDirectChoice J noiseDim support,
        let localChoice : DirectChoiceForPartition root.1.partition :=
          { direct := root.1.direct
            direct_subset := root.1.direct_subset
            singleton_parts := root.1.singleton_parts }
        localChoice.genericTerm payoff
          (stateNat drift diffusion T x₀ z (numSteps J))
          (fun j ↦ diffusionCoefficient diffusion T j T)
          (fun block ↦ compensatedStateDerivative drift diffusion T x₀
            (numSteps J) block.1 z)) =
      ∑ root : EndpointPartitionDirectChoice J noiseDim support,
        ∑ children : ∀ block :
            (root.1.partition.avoid root.1.direct).parts,
            DriftExpansionChoice J noiseDim (numSteps J) block.1,
          (show PayoffExpansionChoice J noiseDim support (numSteps J) from
            { direct := root.1.direct
              direct_subset := root.1.direct_subset
              direct_endpoint := root.2
              partition := root.1.partition.avoid root.1.direct
              children := children }).value
                drift payoff diffusion T x₀ z := by
        apply Fintype.sum_congr
        intro root
        exact root.genericTerm_eq_sum_payoffChoices
          drift payoff diffusion T x₀ z hDrift hPayoff
    _ = ∑ code : EndpointPayoffExpansionCode J noiseDim support (numSteps J),
        code.toChoice.value drift payoff diffusion T x₀ z := by
      exact (Fintype.sum_sigma
        (fun code : EndpointPayoffExpansionCode J noiseDim support (numSteps J) ↦
          code.toChoice.value drift payoff diffusion T x₀ z)).symm
    _ = ∑ code : PayoffExpansionCode J noiseDim support (numSteps J),
        code.toChoice.value drift payoff diffusion T x₀ z := by
      let equivalence :=
        endpointPayoffExpansionCodeEquivPayoffExpansionCode
          J noiseDim support (numSteps J)
      calc
        (∑ code : EndpointPayoffExpansionCode J noiseDim support (numSteps J),
            code.toChoice.value drift payoff diffusion T x₀ z) =
          ∑ code : EndpointPayoffExpansionCode J noiseDim support (numSteps J),
            (equivalence code).toChoice.value drift payoff diffusion T x₀ z := by
              apply Fintype.sum_congr
              intro code
              rfl
        _ = _ := equivalence.sum_comp
          (fun code ↦ code.toChoice.value drift payoff diffusion T x₀ z)
    _ = payoffExpansionSum (m := numSteps J) (u := support)
        drift payoff diffusion T x₀ z := by
      let equivalence :=
        payoffExpansionCodeEquivChoice J noiseDim support (numSteps J)
      unfold payoffExpansionSum
      exact equivalence.sum_comp
        (fun choice ↦ choice.value drift payoff diffusion T x₀ z)


/-- Paper: Lemma `lem:correspondence`.

Every mixed derivative of the terminal Euler integrand is exactly the sum of the analytic
values of all admissible timed payoff trees.  The paper uses nonempty `support`; the Lean
statement also includes the harmless empty-support case, where both sides are the zero-order
payoff term.  The hypothesis `T ≠ 0` follows from the paper's standing assumption `T > 0`. -/
theorem mixedDerivative_integrand_eq_treeExpansionSum
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (hT : T ≠ 0)
    (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (hPayoff : ContDiff ℝ ∞ payoff)
    (z : Input J noiseDim) (support : Finset (Index J noiseDim)) :
    mixedDerivative (integrand drift diffusion payoff T x₀) support z =
      treeExpansionSum (m := numSteps J) (u := support)
        drift payoff diffusion T x₀ z := by
  change mixedDerivative
    (fun y ↦ payoff (stateNat drift diffusion T x₀ y (numSteps J))) support z = _
  calc
    _ = payoffExpansionSum (m := numSteps J) (u := support)
        drift payoff diffusion T x₀ z :=
      mixedDerivative_terminalPayoff_eq_payoffExpansionSum
        drift payoff diffusion T hT x₀ hDrift hPayoff z support
    _ = treeExpansionSum (m := numSteps J) (u := support)
        drift payoff diffusion T x₀ z :=
      payoffExpansionSum_eq_treeExpansionSum drift payoff diffusion T x₀ z

end
end TimeDependentLattice.Trees
