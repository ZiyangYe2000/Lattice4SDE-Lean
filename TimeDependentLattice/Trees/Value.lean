/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Euler.Propagator
import TimeDependentLattice.Trees.LocalExpansion
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Values of timed labelled payoff trees

This file begins the analytic layer of the payoff-tree formalization.  It implements the recursive
vectors `V_y` and the root value `𝒢(𝔗, r)` from Definition `def:tree-value`.

The paper treats direct inputs and children as unordered because the derivatives are symmetric.
Lean needs an explicit order to evaluate `iteratedFDeriv`: direct labels use the canonical
enumeration of their `Finset`, and child values use the canonical child order already imposed by
`PayoffTreeData.Valid`.  Proving independence from these representation orders is a later theorem;
the definitions here do not assume it.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open scoped BigOperators ContDiff
open TimeDependentLattice
open TimeDependentLattice.Analysis
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Euler

/-- A multilinear map distributes over independent finite sums in its final coordinates while
the initial coordinates are held fixed.  This is the algebraic step used when recursively
expanding every state-derivative child of a tree vertex. -/
theorem map_sum_with_fixed_prefix
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p n : ℕ} (f : E [×(p + n)]→L[ℝ] F) (direct : Fin p → E)
    (α : Fin n → Type*) [∀ i, Fintype (α i)] (g : ∀ i, α i → E) :
    f (Fin.addCases direct (fun i ↦ ∑ a, g i a)) =
      ∑ selection : ∀ i, α i,
        f (Fin.addCases direct (fun i ↦ g i (selection i))) := by
  let fsum := f.domDomCongr finSumFinEquiv.symm
  let childMap := fsum.currySum direct
  have h := childMap.map_sum g
  simp only [childMap, fsum, ContinuousMultilinearMap.currySum_apply,
    ContinuousMultilinearMap.domDomCongr_apply] at h
  have hadd (a : Fin p → E) (b : Fin n → E) :
      Fin.addCases a b = fun i ↦ Sum.elim a b (finSumFinEquiv.symm i) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · simp
    · simp
  rw [hadd direct (fun i ↦ ∑ a, g i a)]
  rw [h]
  apply Fintype.sum_congr
  intro selection
  rw [hadd direct (fun i ↦ g i (selection i))]

/-- If one summand in each multilinear coordinate vanishes outside an eligible set of indices,
the full multilinear expansion is indexed exactly by subsets of eligible coordinates. -/
theorem map_add_eq_sum_eligibleSelections
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (f : E [×n]→L[ℝ] F) (direct child : Fin n → E)
    (eligible : Fin n → Prop) [DecidablePred eligible]
    (hdirect : ∀ i, ¬eligible i → direct i = 0) :
    f (direct + child) =
      ∑ selection : {s : Finset (Fin n) // ∀ i ∈ s, eligible i},
        f (selection.1.piecewise direct child) := by
  rw [f.map_add_univ]
  let valid : Finset (Fin n) → Prop := fun s ↦ ∀ i ∈ s, eligible i
  have hinvalid :
      (∑ selection : {s : Finset (Fin n) // ¬valid s},
        f (selection.1.piecewise direct child)) = 0 := by
    apply Fintype.sum_eq_zero
    intro selection
    have hbad := selection.2
    change ¬∀ i ∈ selection.1, eligible i at hbad
    push Not at hbad
    obtain ⟨i, hi, hineligible⟩ := hbad
    apply f.map_coord_zero i
    rw [Finset.piecewise_eq_of_mem selection.1 direct child hi]
    exact hdirect i hineligible
  have hsplit := Fintype.sum_subtype_add_sum_subtype valid
    (fun s : Finset (Fin n) ↦ f (s.piecewise direct child))
  rw [hinvalid, add_zero] at hsplit
  exact hsplit.symm

/-- The first analytic layer of the payoff expansion: Faà di Bruno expresses the mixed payoff
derivative as a finite sum over partitions of the coordinate set. -/
theorem mixedDerivative_payoff_state_eq_sum
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (payoff : Payoff stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (hPayoff : ContDiff ℝ ∞ payoff)
    (m : ℕ) (u : Finset (Index J noiseDim)) (z : Input J noiseDim) :
    mixedDerivative (fun y ↦ payoff (stateNat drift diffusion T x₀ y m)) u z =
      ∑ c : OrderedFinpartition u.card,
        partitionChainTerm payoff (fun y ↦ stateNat drift diffusion T x₀ y m) u c z := by
  apply mixedDerivative_comp
  · exact hPayoff.contDiffAt.of_le (by simp)
  · exact (contDiff_stateNat drift diffusion T x₀ hDrift m).contDiffAt.of_le (by simp)

/-- The payoff Faà di Bruno formula written with the paper's unordered derivative blocks. -/
theorem mixedDerivative_payoff_state_eq_sum_blocks
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (payoff : Payoff stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (hPayoff : ContDiff ℝ ∞ payoff)
    (m : ℕ) (u : Finset (Index J noiseDim)) (z : Input J noiseDim) :
    mixedDerivative (fun y ↦ payoff (stateNat drift diffusion T x₀ y m)) u z =
      ∑ c : OrderedFinpartition u.card,
        iteratedFDeriv ℝ c.length payoff (stateNat drift diffusion T x₀ z m)
          fun i ↦ mixedDerivative
            (fun y ↦ stateNat drift diffusion T x₀ y m) (partitionBlock u c i) z := by
  rw [mixedDerivative_payoff_state_eq_sum drift payoff diffusion T x₀
    hDrift hPayoff m u z]
  apply Finset.sum_congr rfl
  intro c _
  exact partitionChainTerm_eq_mixedDerivative_blocks payoff
    (fun y ↦ stateNat drift diffusion T x₀ y m) u c z
    (contDiff_stateNat drift diffusion T x₀ hDrift m)

/-- One Faà di Bruno term in the paper's canonical enumeration of an unordered partition. -/
def paperFinpartitionChainTerm {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F)
    {u : Finset (Index J noiseDim)} (p : CoordinatePartition u)
    (z : Input J noiseDim) : G :=
  let blocks := orderedPartitionBlocks p
  let blockEquiv := orderedPartitionBlocksEquiv p
  iteratedFDeriv ℝ blocks.length g (f z) fun i ↦
    mixedDerivative f (blockEquiv i).1 z

/-- The unordered Faà di Bruno term is independent of the canonical block order. -/
theorem finpartitionChainTerm_eq_paperFinpartitionChainTerm
    {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F)
    (u : Finset (Index J noiseDim)) (p : CoordinatePartition u)
    (z : Input J noiseDim) (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) :
    finpartitionChainTerm g f u p z =
      paperFinpartitionChainTerm g f p z := by
  let c := (orderedFinpartitionEquivCoordinateFinpartition u).symm p
  let q := orderedFinpartitionToFinpartition u c
  have hp : q = p := by
    change orderedFinpartitionEquivCoordinateFinpartition u c = p
    exact (orderedFinpartitionEquivCoordinateFinpartition u).apply_symm_apply p
  let partsEquiv : q.parts ≃ p.parts :=
    { toFun := fun block ↦ ⟨block.1, by rw [← hp]; exact block.2⟩
      invFun := fun block ↦ ⟨block.1, by rw [hp]; exact block.2⟩
      left_inv := fun block ↦ by rfl
      right_inv := fun block ↦ by rfl }
  let blocks := orderedPartitionBlocks p
  let blockEquiv := orderedPartitionBlocksEquiv p
  let reindex : Fin c.length ≃ Fin blocks.length :=
    (partitionBlockIndexEquivParts u c).trans
      (partsEquiv.trans blockEquiv.symm)
  have hreindex (i : Fin c.length) :
      (blockEquiv (reindex i)).1 = partitionBlock u c i := by
    change (blockEquiv (blockEquiv.symm
      (partsEquiv (partitionBlockIndexEquivParts u c i)))).1 = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hdirections :
      (fun i : Fin c.length ↦ mixedDerivative f (partitionBlock u c i) z) =
        (fun i : Fin blocks.length ↦ mixedDerivative f (blockEquiv i).1 z) ∘
          reindex := by
    funext i
    simp only [Function.comp_apply]
    rw [hreindex]
  have hderiv := iteratedFDeriv_comp_equiv_directions_of_contDiff
    g (f z)
    (fun i : Fin blocks.length ↦ mixedDerivative f (blockEquiv i).1 z)
    reindex hg
  unfold finpartitionChainTerm
  change partitionChainTerm g f u c z = _
  rw [partitionChainTerm_eq_mixedDerivative_blocks g f u c z hf]
  rw [hdirections]
  exact hderiv

/-- In one paper partition term, each singleton block offers the two alternatives that become a
direct bridge label or a recursive derivative child. -/
theorem paperFinpartitionChainTerm_eulerDriftInput_eq
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    {u : Finset (Index J noiseDim)} (p : CoordinatePartition u)
    (z : Input J noiseDim) :
    paperFinpartitionChainTerm (drift (gridTime T J step))
        (eulerDriftInput drift diffusion T x₀ step) p z =
      let blocks := orderedPartitionBlocks p
      let blockEquiv := orderedPartitionBlocksEquiv p
      iteratedFDeriv ℝ blocks.length (drift (gridTime T J step))
        (stateNat drift diffusion T x₀ z step) fun i ↦
          compensatedStateDerivative drift diffusion T x₀ step
              (blockEquiv i).1 z +
            if hcard : (blockEquiv i).1.card = 1 then
              diffusionCoefficient diffusion T
                (finpartitionSingletonCoordinate (blockEquiv i) hcard)
                (gridTime T J step)
            else 0 := by
  unfold paperFinpartitionChainTerm
  rw [eulerDriftInput_eq_stateNat]
  dsimp only
  congr 1
  funext i
  exact mixedDerivative_eulerDriftInput_partitionBlock
    drift diffusion T x₀ hDrift step p
      (orderedPartitionBlocksEquiv p i) z

/-- One local term after choosing which singleton blocks contribute their direct bridge
coefficient.  The remaining blocks carry compensated state derivatives. -/
def DirectChoiceForPartition.localTerm
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    {partition : Finpartition support} (choice : DirectChoiceForPartition partition)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (step : ℕ) :
    State stateDim :=
  let remaining := partition.avoid choice.direct
  let blocks := orderedPartitionBlocks remaining
  let blockEquiv := orderedPartitionBlocksEquiv remaining
  iteratedFDeriv ℝ (choice.direct.card + blocks.length)
    (drift (gridTime T J step)) (stateNat drift diffusion T x₀ z step)
    (Fin.addCases
      (fun k ↦ diffusionCoefficient diffusion T
        (choice.direct.equivFin.symm k).val (gridTime T J step))
      (fun i ↦ compensatedStateDerivative drift diffusion T x₀ step
        (blockEquiv i).1 z))

/-- The same local term with the partition bundled into the global choice type. -/
def PartitionDirectChoice.localTerm
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (choice : PartitionDirectChoice J noiseDim support)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (step : ℕ) :
    State stateDim :=
  (show DirectChoiceForPartition choice.partition from
    { direct := choice.direct
      direct_subset := choice.direct_subset
      singleton_parts := choice.singleton_parts }).localTerm
        drift diffusion T x₀ z step

/-- The direct bridge direction attached to a canonical partition block; it is zero on every
non-singleton block. -/
def partitionBlockDirectDirection
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (partition : Finpartition support) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (step : ℕ) :
    Fin (orderedPartitionBlocks partition).length → State stateDim := fun i ↦
  if hcard : (orderedPartitionBlocksEquiv partition i).1.card = 1 then
    diffusionCoefficient diffusion T
      (finpartitionSingletonCoordinate (orderedPartitionBlocksEquiv partition i) hcard)
      (gridTime T J step)
  else 0

/-- The compensated derivative direction attached to a canonical partition block. -/
def partitionBlockChildDirection
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (partition : Finpartition support) (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (step : ℕ) :
    Fin (orderedPartitionBlocks partition).length → State stateDim := fun i ↦
  compensatedStateDerivative drift diffusion T x₀ step
    (orderedPartitionBlocksEquiv partition i).1 z

/-- Reordering one expanded partition term to put direct directions first gives exactly the
paper's local direct-set/remaining-partition term. -/
theorem DirectChoiceForPartition.expandedTerm_eq_localTerm
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (partition : Finpartition support)
    (choice : DirectChoiceForPartition partition)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (step : ℕ)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) :
    let selection :=
      (singletonBlockSelectionEquivDirectChoice partition).symm choice
    iteratedFDeriv ℝ (orderedPartitionBlocks partition).length
        (drift (gridTime T J step)) (stateNat drift diffusion T x₀ z step)
        (selection.1.piecewise
          (partitionBlockDirectDirection partition diffusion T step)
          (partitionBlockChildDirection partition drift diffusion T x₀ z step)) =
      choice.localTerm drift diffusion T x₀ z step := by
  dsimp only
  let selection :=
    (singletonBlockSelectionEquivDirectChoice partition).symm choice
  let bundled : PartitionDirectChoice J noiseDim support :=
    { partition := partition
      direct := choice.direct
      direct_subset := choice.direct_subset
      singleton_parts := choice.singleton_parts }
  let originalDirections := selection.1.piecewise
    (partitionBlockDirectDirection partition diffusion T step)
    (partitionBlockChildDirection partition drift diffusion T x₀ z step)
  let remaining := partition.avoid choice.direct
  let targetDirections : Fin (choice.direct.card +
      (orderedPartitionBlocks remaining).length) → State stateDim :=
    Fin.addCases
      (fun k ↦ diffusionCoefficient diffusion T
        (choice.direct.equivFin.symm k).val (gridTime T J step))
      (fun i ↦ compensatedStateDerivative drift diffusion T x₀ step
        (orderedPartitionBlocksEquiv remaining i).1 z)
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
        (partitionBlockDirectDirection partition diffusion T step)
        (partitionBlockChildDirection partition drift diffusion T x₀ z step)
        originalIndex = _
      rw [Finset.piecewise_eq_of_mem selection.1 _ _ hselected]
      simp only [partitionBlockDirectDirection, hcard, dite_true, hcoordinate]
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
        (partitionBlockDirectDirection partition diffusion T step)
        (partitionBlockChildDirection partition drift diffusion T x₀ z step)
        originalIndex = _
      rw [Finset.piecewise_eq_of_notMem selection.1 _ _ hnotSelected]
      simp only [partitionBlockChildDirection]
      rw [hblock']
  have hperm := iteratedFDeriv_comp_equiv_directions_of_contDiff
    (drift (gridTime T J step)) (stateNat drift diffusion T x₀ z step)
    originalDirections bundled.directionEquiv (hDrift (gridTime T J step))
  rw [hdirections] at hperm
  exact hperm.symm

/-- Multilinearity expands one Faà di Bruno partition term into all choices of direct singleton
blocks. -/
theorem paperFinpartitionChainTerm_eq_sum_directChoices
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    {support : Finset (Index J noiseDim)} (partition : Finpartition support)
    (z : Input J noiseDim) :
    paperFinpartitionChainTerm (drift (gridTime T J step))
        (eulerDriftInput drift diffusion T x₀ step) partition z =
      ∑ choice : DirectChoiceForPartition partition,
        choice.localTerm drift diffusion T x₀ z step := by
  rw [paperFinpartitionChainTerm_eulerDriftInput_eq
    drift diffusion T x₀ hDrift step partition z]
  dsimp only
  let derivative := iteratedFDeriv ℝ (orderedPartitionBlocks partition).length
    (drift (gridTime T J step)) (stateNat drift diffusion T x₀ z step)
  let direct := partitionBlockDirectDirection partition diffusion T step
  let child := partitionBlockChildDirection partition drift diffusion T x₀ z step
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
          (fun selection ↦ derivative (selection.1.piecewise direct child))).symm
      _ = ∑ choice : DirectChoiceForPartition partition,
          choice.localTerm drift diffusion T x₀ z step := by
        apply Fintype.sum_congr
        intro choice
        exact choice.expandedTerm_eq_localTerm partition drift diffusion T x₀ z step
          hDrift
  · intro i hi
    unfold direct partitionBlockDirectDirection
    split
    · rename_i hcard
      exfalso
      apply hi
      simpa only [orderedPartitionBlocksEquiv_apply] using hcard
    · rfl

/-- Summing the preceding partitionwise expansion and reindexing the sigma type gives exactly the
global local-choice sum. -/
theorem sum_paperFinpartitionChainTerm_eq_sum_partitionDirectChoices
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (step : ℕ)
    (support : Finset (Index J noiseDim)) (z : Input J noiseDim) :
    (∑ partition : Finpartition support,
      paperFinpartitionChainTerm (drift (gridTime T J step))
        (eulerDriftInput drift diffusion T x₀ step) partition z) =
      ∑ choice : PartitionDirectChoice J noiseDim support,
        choice.localTerm drift diffusion T x₀ z step := by
  simp_rw [paperFinpartitionChainTerm_eq_sum_directChoices
    drift diffusion T x₀ hDrift step]
  rw [← Fintype.sum_sigma']
  let equivalence := sigmaDirectChoiceEquivPartitionDirectChoice J noiseDim support
  calc
    (∑ choice : Σ partition : Finpartition support,
        DirectChoiceForPartition partition,
      choice.2.localTerm drift diffusion T x₀ z step) =
        ∑ choice : Σ partition : Finpartition support,
          DirectChoiceForPartition partition,
          (equivalence choice).localTerm drift diffusion T x₀ z step := by
      apply Fintype.sum_congr
      intro choice
      rfl
    _ = ∑ choice : PartitionDirectChoice J noiseDim support,
        choice.localTerm drift diffusion T x₀ z step := by
      exact Fintype.sum_equiv equivalence _ _ (fun _ ↦ rfl)

/-- The unique non-nonlinear local choice is precisely the Jacobian term subtracted in
`nonlinearStateForcing`. -/
theorem linearPartitionDirectChoice_localTerm
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (step : ℕ) (support : Finset (Index J noiseDim)) (hcard : 2 ≤ support.card)
    (z : Input J noiseDim) :
    (linearPartitionDirectChoice (Finset.card_pos.mp (by omega)) :
      PartitionDirectChoice J noiseDim support).localTerm
        drift diffusion T x₀ z step =
      (fderiv ℝ (drift (gridTime T J step))
        (stateNat drift diffusion T x₀ z step))
        (compensatedStateDerivative drift diffusion T x₀ step support z) := by
  have hsupport : support.Nonempty := Finset.card_pos.mp (by omega)
  let partition := Finpartition.indiscrete hsupport.ne_empty
  let fixed : DirectChoiceForPartition partition :=
    { direct := ∅
      direct_subset := Finset.empty_subset _
      singleton_parts := by simp }
  let selection := (singletonBlockSelectionEquivDirectChoice partition).symm fixed
  have hselection : selection.1 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hsingleton := selection.2 i hi
    have hpart := (orderedPartitionBlocksEquiv partition i).2
    have hwhole : (orderedPartitionBlocksEquiv partition i).1 = support := by
      simpa [partition] using Finset.mem_singleton.mp hpart
    rw [hwhole] at hsingleton
    omega
  have hexpanded := fixed.expandedTerm_eq_localTerm partition drift diffusion T x₀ z step
    hDrift
  dsimp only at hexpanded
  change (iteratedFDeriv ℝ (orderedPartitionBlocks partition).length
    (drift (gridTime T J step)) (stateNat drift diffusion T x₀ z step))
    (selection.1.piecewise
      (partitionBlockDirectDirection partition diffusion T step)
      (partitionBlockChildDirection partition drift diffusion T x₀ z step)) = _ at hexpanded
  rw [hselection] at hexpanded
  simp only [Finset.piecewise_empty] at hexpanded
  have hlength : (orderedPartitionBlocks partition).length = 1 := by
    simp [orderedPartitionBlocks, partition]
  rw [iteratedFDeriv_eq_fderiv_of_eq_one _ hlength] at hexpanded
  let blockIndex : Fin (orderedPartitionBlocks partition).length :=
    Fin.cast hlength.symm (0 : Fin 1)
  have hdirection :
      (partitionBlockChildDirection partition drift diffusion T x₀ z step) blockIndex =
        compensatedStateDerivative drift diffusion T x₀ step support z := by
    unfold partitionBlockChildDirection
    congr 2
    have hpart := (orderedPartitionBlocksEquiv partition blockIndex).2
    simpa [partition] using Finset.mem_singleton.mp hpart
  rw [hdirection] at hexpanded
  simpa [PartitionDirectChoice.localTerm, linearPartitionDirectChoice, fixed, partition]
    using hexpanded.symm

/-- The complete local-choice sum is the Jacobian term plus the nonlinear local choices. -/
theorem sum_partitionDirectChoices_eq_linear_add_nonlinear
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (step : ℕ) (support : Finset (Index J noiseDim)) (hcard : 2 ≤ support.card)
    (z : Input J noiseDim) :
    (∑ choice : PartitionDirectChoice J noiseDim support,
      choice.localTerm drift diffusion T x₀ z step) =
      (linearPartitionDirectChoice (Finset.card_pos.mp (by omega)) :
        PartitionDirectChoice J noiseDim support).localTerm
          drift diffusion T x₀ z step +
        ∑ choice : NonlinearPartitionDirectChoice J noiseDim support,
          choice.1.localTerm drift diffusion T x₀ z step := by
  let equivalence := partitionDirectChoiceEquivOptionNonlinear hcard
  calc
    (∑ choice : PartitionDirectChoice J noiseDim support,
        choice.localTerm drift diffusion T x₀ z step) =
      ∑ choice : Option (NonlinearPartitionDirectChoice J noiseDim support),
        (equivalence.symm choice).localTerm drift diffusion T x₀ z step := by
      apply Fintype.sum_equiv equivalence
      intro choice
      rw [Equiv.symm_apply_apply]
    _ = (linearPartitionDirectChoice (Finset.card_pos.mp (by omega)) :
        PartitionDirectChoice J noiseDim support).localTerm
          drift diffusion T x₀ z step +
        ∑ choice : NonlinearPartitionDirectChoice J noiseDim support,
          choice.1.localTerm drift diffusion T x₀ z step := by
      rw [Fintype.sum_option]
      rfl

/-- The analytic term at one nonlinear drift root before its child derivatives are recursively
expanded. -/
def DriftRootChoice.localTerm
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (root : DriftRootChoice J noiseDim support)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (step : ℕ) :
    State stateDim :=
  let blocks := orderedPartitionBlocks root.partition
  let blockEquiv := orderedPartitionBlocksEquiv root.partition
  iteratedFDeriv ℝ (root.direct.card + blocks.length)
    (drift (gridTime T J step)) (stateNat drift diffusion T x₀ z step)
    (Fin.addCases
      (fun k ↦ diffusionCoefficient diffusion T
        (root.direct.equivFin.symm k).val (gridTime T J step))
      (fun i ↦ compensatedStateDerivative drift diffusion T x₀ step
        (blockEquiv i).1 z))

/-- The local term is preserved by the proved equivalence from nonlinear partition selections to
the paper's drift-root choices. -/
theorem NonlinearPartitionDirectChoice.localTerm_eq_rootLocalTerm
    {J stateDim noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (choice : NonlinearPartitionDirectChoice J noiseDim support)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (step : ℕ) :
    choice.1.localTerm drift diffusion T x₀ z step =
      (nonlinearPartitionDirectEquivDriftRootChoice J noiseDim support choice).localTerm
        drift diffusion T x₀ z step := by
  rfl

/-- The local Faà di Bruno calculation: after the linear Jacobian term is removed, the forcing is
exactly the sum over the paper's nonlinear drift-root choices. -/
theorem nonlinearStateForcing_eq_sum_driftRootChoices
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (step : ℕ)
    (support : Finset (Index J noiseDim)) (hcard : 2 ≤ support.card) :
    nonlinearStateForcing drift diffusion T x₀ z step support =
      stepSize T J • ∑ root : DriftRootChoice J noiseDim support,
        root.localTerm drift diffusion T x₀ z step := by
  have hinput : ContDiff ℝ ∞
      (eulerDriftInput (J := J) drift diffusion T x₀ step) := by
    have hfun : eulerDriftInput (J := J) drift diffusion T x₀ step =
        fun y ↦ stateNat drift diffusion T x₀ y step := by
      funext y
      exact eulerDriftInput_eq_stateNat drift diffusion T x₀ step y
    rw [hfun]
    exact contDiff_stateNat drift diffusion T x₀ hDrift step
  have hsum :
      (∑ c : OrderedFinpartition support.card,
        partitionChainTerm (drift (gridTime T J step))
          (eulerDriftInput drift diffusion T x₀ step) support c z) =
        ∑ choice : PartitionDirectChoice J noiseDim support,
          choice.localTerm drift diffusion T x₀ z step := by
    rw [sum_partitionChainTerm_eq_sum_finpartitionChainTerm]
    calc
      (∑ partition : Finpartition support,
          finpartitionChainTerm (drift (gridTime T J step))
            (eulerDriftInput drift diffusion T x₀ step) support partition z) =
          ∑ partition : Finpartition support,
            paperFinpartitionChainTerm (drift (gridTime T J step))
              (eulerDriftInput drift diffusion T x₀ step) partition z := by
        apply Fintype.sum_congr
        intro partition
        exact finpartitionChainTerm_eq_paperFinpartitionChainTerm
          (drift (gridTime T J step))
          (eulerDriftInput drift diffusion T x₀ step) support partition z
          (hDrift _) hinput
      _ = _ := sum_paperFinpartitionChainTerm_eq_sum_partitionDirectChoices
        drift diffusion T x₀ hDrift step support z
  rw [sum_partitionDirectChoices_eq_linear_add_nonlinear
    drift diffusion T x₀ step support hcard z] at hsum
  rw [linearPartitionDirectChoice_localTerm
    drift diffusion T x₀ hDrift step support hcard z] at hsum
  have hnonlinear :
      (∑ choice : NonlinearPartitionDirectChoice J noiseDim support,
        choice.1.localTerm drift diffusion T x₀ z step) =
        ∑ root : DriftRootChoice J noiseDim support,
          root.localTerm drift diffusion T x₀ z step := by
    let equivalence := nonlinearPartitionDirectEquivDriftRootChoice J noiseDim support
    calc
      (∑ choice : NonlinearPartitionDirectChoice J noiseDim support,
        choice.1.localTerm drift diffusion T x₀ z step) =
          ∑ choice : NonlinearPartitionDirectChoice J noiseDim support,
            (equivalence choice).localTerm drift diffusion T x₀ z step := by
        apply Fintype.sum_congr
        intro choice
        exact choice.localTerm_eq_rootLocalTerm drift diffusion T x₀ z step
      _ = _ := by
        apply Fintype.sum_equiv equivalence
        intro choice
        rfl
  unfold nonlinearStateForcing
  rw [eulerDriftInput_eq_stateNat]
  rw [hsum, hnonlinear]
  rw [smul_add]
  abel

/-- The payoff Faà di Bruno formula in exactly the paper's unordered-partition notation. -/
theorem mixedDerivative_payoff_state_eq_sum_finpartitions
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (payoff : Payoff stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t)) (hPayoff : ContDiff ℝ ∞ payoff)
    (m : ℕ) (u : Finset (Index J noiseDim)) (z : Input J noiseDim) :
    mixedDerivative (fun y ↦ payoff (stateNat drift diffusion T x₀ y m)) u z =
      ∑ p : CoordinatePartition u,
        paperFinpartitionChainTerm payoff
          (fun y ↦ stateNat drift diffusion T x₀ y m) p z := by
  change mixedDerivative (payoff ∘
    fun y ↦ stateNat drift diffusion T x₀ y m) u z = _
  rw [mixedDerivative_comp_finpartition payoff
    (fun y ↦ stateNat drift diffusion T x₀ y m) u z]
  · apply Finset.sum_congr rfl
    intro p _
    exact finpartitionChainTerm_eq_paperFinpartitionChainTerm payoff
      (fun y ↦ stateNat drift diffusion T x₀ y m) u p z hPayoff
      (contDiff_stateNat drift diffusion T x₀ hDrift m)
  · exact hPayoff.contDiffAt.of_le (by simp)
  · exact (contDiff_stateNat drift diffusion T x₀ hDrift m).contDiffAt.of_le (by simp)

/-- The ordered family consisting first of the direct bridge inputs and then of the recursively
evaluated child vectors at a tree vertex. -/
def vertexDirections {J stateDim noiseDim : ℕ}
    (direct : Finset (Index J noiseDim))
    (directValue : Index J noiseDim → State stateDim)
    (childValues : List (State stateDim)) :
    Fin (direct.card + childValues.length) → State stateDim :=
  Fin.addCases
    (fun k ↦ directValue (direct.equivFin.symm k).val)
    (fun k ↦ childValues.get k)

/-- Mapping values over the canonical block list gives the same directions as indexing the
children directly by the unordered partition parts. -/
theorem vertexDirections_map_orderedPartitionBlocks
    {J stateDim noiseDim : ℕ}
    (direct : Finset (Index J noiseDim))
    (directValue : Index J noiseDim → State stateDim)
    {support : Finset (Index J noiseDim)}
    (partition : Finpartition support)
    (childValue : partition.parts → State stateDim) :
    let blocks := orderedPartitionBlocks partition
    let blockEquiv := orderedPartitionBlocksEquiv partition
    let reindex := finCongr (by simp :
      direct.card + blocks.length =
        direct.card + (blocks.map childValue).length)
    vertexDirections direct directValue (blocks.map childValue) ∘ reindex =
      Fin.addCases
        (fun k ↦ directValue (direct.equivFin.symm k).val)
        (fun i ↦ childValue (blockEquiv i)) := by
  dsimp only
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp [vertexDirections]
  · intro k
    have hcast :
        finCongr (by simp : direct.card +
            (orderedPartitionBlocks partition).length = direct.card +
              ((orderedPartitionBlocks partition).map childValue).length)
            (Fin.natAdd direct.card k) =
          Fin.natAdd direct.card (Fin.cast (by simp) k) := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [hcast]
    simp [vertexDirections, orderedPartitionBlocksEquiv_apply]

@[simp]
theorem vertexDirections_nil {J stateDim noiseDim : ℕ}
    (direct : Finset (Index J noiseDim))
    (directValue : Index J noiseDim → State stateDim) :
    vertexDirections direct directValue [] =
      fun k ↦ directValue (direct.equivFin.symm k).val := by
  funext k
  exact Fin.addCases_left k

@[simp]
theorem singleton_equivFin_symm_val {J noiseDim : ℕ} (j : Index J noiseDim)
    (k : Fin ({j} : Finset (Index J noiseDim)).card) :
    (({j} : Finset (Index J noiseDim)).equivFin.symm k).val = j :=
  Finset.mem_singleton.mp (({j} : Finset (Index J noiseDim)).equivFin.symm k).property

mutual
  /-- The recursive vector `V_y` at a drift vertex in Equation `eq:tree-value`.

  The definition is total on raw data.  If tree and time children have different lengths,
  `driftTreeValues` stops at the shorter list.  This case is excluded by `TimeAssignment.Valid`,
  and `driftTreeValues_length_eq_of_validChildren` below records the exact arity used for valid
  timed trees. -/
  def driftTreeValue {J stateDim noiseDim : ℕ}
      (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
      (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (parentTime : ℕ) :
      DriftTreeData J noiseDim → DriftTimeData → State stateDim
    | .node direct children, .node time timeChildren =>
        let childValues := driftTreeValues drift diffusion T x₀ z time children timeChildren
        propagator (stepJacobian drift diffusion T x₀ z) parentTime time
          (stepSize T J •
            iteratedFDeriv ℝ (direct.card + childValues.length)
              (drift (gridTime T J time))
              (stateNat drift diffusion T x₀ z time)
              (vertexDirections direct
                (fun j ↦ diffusionCoefficient diffusion T j (gridTime T J time))
                childValues))

  /-- Recursive values of aligned lists of child trees and child time assignments. -/
  def driftTreeValues {J stateDim noiseDim : ℕ}
      (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
      (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (parentTime : ℕ) :
      List (DriftTreeData J noiseDim) → List DriftTimeData → List (State stateDim)
    | tree :: trees, assignment :: assignments =>
        driftTreeValue drift diffusion T x₀ z parentTime tree assignment ::
          driftTreeValues drift diffusion T x₀ z parentTime trees assignments
    | _, _ => []
end

/-- Valid child time data produce exactly one recursive value for every child tree. -/
theorem driftTreeValues_length_eq_of_validChildren {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) (parentTime : ℕ)
    (trees : List (DriftTreeData J noiseDim)) (assignments : List DriftTimeData)
    (hvalid : DriftTimeData.ValidChildren parentTime trees assignments) :
    (driftTreeValues drift diffusion T x₀ z parentTime trees assignments).length =
      trees.length := by
  induction trees generalizing assignments with
  | nil =>
      cases assignments <;> simp [driftTreeValues]
  | cons tree trees ih =>
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          simp [driftTreeValues, ih assignments hvalid.2]

/-- The recursively evaluated analytic term selected by one complete drift expansion choice. -/
def DriftExpansionChoice.value {J stateDim noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) :
    DriftExpansionChoice J noiseDim parentTime support → State stateDim
  | .singleton time j _ =>
      propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J •
          iteratedFDeriv ℝ 1 (drift (gridTime T J time))
            (stateNat drift diffusion T x₀ z time)
            (vertexDirections {j}
              (fun k ↦ diffusionCoefficient diffusion T k (gridTime T J time)) []))
  | .higher time _ direct _ partition _ children =>
      let childValues := (orderedPartitionBlocks partition).map fun block =>
        value drift diffusion T x₀ z (children block)
      propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J •
          iteratedFDeriv ℝ (direct.card + childValues.length)
            (drift (gridTime T J time))
            (stateNat drift diffusion T x₀ z time)
            (vertexDirections direct
              (fun j ↦ diffusionCoefficient diffusion T j (gridTime T J time))
              childValues))

/-- The finite sum of all complete recursive expansions of one compensated state derivative. -/
noncomputable def driftExpansionSum {J stateDim noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) : State stateDim :=
  ∑ choice : DriftExpansionChoice J noiseDim parentTime support,
    choice.value drift diffusion T x₀ z

/-- A higher expansion choice can be evaluated directly with its children indexed by the
unordered partition parts.  Smoothness removes the auxiliary canonical list order. -/
theorem DriftExpansionChoice.higher_value_eq_explicit
    {J stateDim noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (time : ℕ) (htime : time < parentTime)
    (root : DriftRootChoice J noiseDim support)
    (children : ∀ block : root.partition.parts,
      DriftExpansionChoice J noiseDim time block.1) :
    (DriftExpansionChoice.higher time htime root.direct root.direct_subset
      root.partition root.local_order children).value drift diffusion T x₀ z =
      let blocks := orderedPartitionBlocks root.partition
      let blockEquiv := orderedPartitionBlocksEquiv root.partition
      propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J •
          iteratedFDeriv ℝ (root.direct.card + blocks.length)
            (drift (gridTime T J time))
            (stateNat drift diffusion T x₀ z time)
            (Fin.addCases
              (fun k ↦ diffusionCoefficient diffusion T
                (root.direct.equivFin.symm k).val (gridTime T J time))
              (fun i ↦ (children (blockEquiv i)).value
                drift diffusion T x₀ z))) := by
  dsimp only [DriftExpansionChoice.value]
  let blocks := orderedPartitionBlocks root.partition
  let childValue : root.partition.parts → State stateDim := fun block ↦
    (children block).value drift diffusion T x₀ z
  let directValue : Index J noiseDim → State stateDim := fun j ↦
    diffusionCoefficient diffusion T j (gridTime T J time)
  let reindex := finCongr (by simp :
    root.direct.card + blocks.length =
      root.direct.card + (blocks.map childValue).length)
  have hdirections := vertexDirections_map_orderedPartitionBlocks
    root.direct directValue root.partition childValue
  have hderiv := iteratedFDeriv_comp_equiv_directions_of_contDiff
    (drift (gridTime T J time)) (stateNat drift diffusion T x₀ z time)
    (vertexDirections root.direct directValue (blocks.map childValue))
    reindex (hDrift (gridTime T J time))
  rw [hdirections] at hderiv
  rw [hderiv]

/-- At a fixed higher-order root, multilinearity expands the sum attached to every child block
into the sum over all simultaneous complete child choices. -/
theorem iteratedFDeriv_root_driftExpansionSum
    {J stateDim noiseDim : ℕ} (drift : Drift stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Input J noiseDim) (time : ℕ)
    {support : Finset (Index J noiseDim)}
    (root : DriftRootChoice J noiseDim support) :
    let blocks := orderedPartitionBlocks root.partition
    let blockEquiv := orderedPartitionBlocksEquiv root.partition
    iteratedFDeriv ℝ (root.direct.card + blocks.length)
        (drift (gridTime T J time)) (stateNat drift diffusion T x₀ z time)
        (Fin.addCases
          (fun k ↦ diffusionCoefficient diffusion T
            (root.direct.equivFin.symm k).val (gridTime T J time))
          (fun i ↦ driftExpansionSum (parentTime := time)
            (support := (blockEquiv i).1) drift diffusion T x₀ z)) =
      ∑ children : ∀ block : root.partition.parts,
          DriftExpansionChoice J noiseDim time block.1,
        iteratedFDeriv ℝ (root.direct.card + blocks.length)
          (drift (gridTime T J time)) (stateNat drift diffusion T x₀ z time)
          (Fin.addCases
            (fun k ↦ diffusionCoefficient diffusion T
              (root.direct.equivFin.symm k).val (gridTime T J time))
            (fun i ↦ (children (blockEquiv i)).value
              drift diffusion T x₀ z)) := by
  dsimp only
  let blocks := orderedPartitionBlocks root.partition
  let blockEquiv := orderedPartitionBlocksEquiv root.partition
  let derivative := iteratedFDeriv ℝ (root.direct.card + blocks.length)
    (drift (gridTime T J time)) (stateNat drift diffusion T x₀ z time)
  let directValues : Fin root.direct.card → State stateDim := fun k ↦
    diffusionCoefficient diffusion T (root.direct.equivFin.symm k).val
      (gridTime T J time)
  let α : Fin blocks.length → Type := fun i ↦
    DriftExpansionChoice J noiseDim time (blockEquiv i).1
  let g : ∀ i, α i → State stateDim := fun _ choice ↦
    choice.value drift diffusion T x₀ z
  have hmap := map_sum_with_fixed_prefix derivative directValues α g
  have hsum (i : Fin blocks.length) :
      (∑ choice, g i choice) =
        driftExpansionSum (parentTime := time)
          (support := (blockEquiv i).1) drift diffusion T x₀ z := by
    rfl
  simp_rw [hsum] at hmap
  let childEquiv := Equiv.piCongrLeft
    (fun block : root.partition.parts ↦
      DriftExpansionChoice J noiseDim time block.1) blockEquiv
  rw [← childEquiv.sum_comp]
  rw [hmap]
  apply Fintype.sum_congr
  intro selection
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    rw [Fin.addCases_left, Fin.addCases_left]
  · intro k
    rw [Fin.addCases_right, Fin.addCases_right]
    simp [g, α, childEquiv, blockEquiv, blocks]

/-- If every child derivative has already been expanded, one propagated local root term is the
sum of all complete higher expansion choices with that time and root. -/
theorem DriftRootChoice.propagated_localTerm_eq_sum_higherChoices
    {J stateDim noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (time : ℕ) (htime : time < parentTime)
    (root : DriftRootChoice J noiseDim support)
    (hchildren : ∀ block : root.partition.parts,
      compensatedStateDerivative drift diffusion T x₀ time block.1 z =
        driftExpansionSum (parentTime := time) (support := block.1)
          drift diffusion T x₀ z) :
    propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J • root.localTerm drift diffusion T x₀ z time) =
      ∑ children : ∀ block : root.partition.parts,
          DriftExpansionChoice J noiseDim time block.1,
        (DriftExpansionChoice.higher time htime root.direct root.direct_subset
          root.partition root.local_order children).value drift diffusion T x₀ z := by
  let blocks := orderedPartitionBlocks root.partition
  let blockEquiv := orderedPartitionBlocksEquiv root.partition
  have hlocal : root.localTerm drift diffusion T x₀ z time =
      iteratedFDeriv ℝ (root.direct.card + blocks.length)
        (drift (gridTime T J time)) (stateNat drift diffusion T x₀ z time)
        (Fin.addCases
          (fun k ↦ diffusionCoefficient diffusion T
            (root.direct.equivFin.symm k).val (gridTime T J time))
          (fun i ↦ driftExpansionSum (parentTime := time)
            (support := (blockEquiv i).1) drift diffusion T x₀ z)) := by
    unfold DriftRootChoice.localTerm
    dsimp only
    congr 1
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      rw [Fin.addCases_left, Fin.addCases_left]
    · intro k
      rw [Fin.addCases_right, Fin.addCases_right]
      exact hchildren (blockEquiv k)
  rw [hlocal]
  rw [iteratedFDeriv_root_driftExpansionSum]
  rw [Finset.smul_sum, map_sum]
  apply Fintype.sum_congr
  intro children
  exact (DriftExpansionChoice.higher_value_eq_explicit
    drift diffusion T x₀ z hDrift time htime root children).symm

/-- On support of size at least two, the complete expansion sum separates into the earlier
root time, the local direct-set/partition choice, and the recursive child choices. -/
theorem driftExpansionSum_eq_sum_higherCode
    {J stateDim noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)} (hcard : 2 ≤ support.card)
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim) :
    driftExpansionSum (parentTime := parentTime) (support := support)
        drift diffusion T x₀ z =
      ∑ code : DriftHigherCode J noiseDim parentTime support,
        code.toChoice.value drift diffusion T x₀ z := by
  let equivalence :=
    DriftExpansionChoice.higherEquiv
      (J := J) (noiseDim := noiseDim) (parentTime := parentTime) hcard
  unfold driftExpansionSum
  exact (equivalence.symm.sum_comp
    (fun choice ↦ choice.value drift diffusion T x₀ z)).symm

/-- A drift expansion choice and its corresponding timed drift tree have the same recursively
evaluated vector. -/
theorem DriftExpansionChoice.value_eq_driftTreeValue
    {J stateDim noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    choice.value drift diffusion T x₀ z =
      driftTreeValue drift diffusion T x₀ z parentTime choice.toTree choice.toTime := by
  induction choice with
  | singleton time j htime =>
      rfl
  | higher time htime direct hsubset partition horder children ih =>
      let blocks := orderedPartitionBlocks partition
      have hvalues :
          driftTreeValues drift diffusion T x₀ z time
              (blocks.map fun block => (children block).toTree)
              (blocks.map fun block => (children block).toTime) =
            blocks.map fun block =>
              (children block).value drift diffusion T x₀ z := by
        induction blocks with
        | nil => simp [driftTreeValues]
        | cons block tail ihTail =>
            simp only [List.map, driftTreeValues]
            rw [← ih block]
            rw [ihTail]
      have htreeList :
          blocks.map (Prod.fst ∘ fun block => (children block).toTreeTime) =
            blocks.map fun block => (children block).toTree := rfl
      have htimeList :
          blocks.map (Prod.snd ∘ fun block => (children block).toTreeTime) =
            blocks.map fun block => (children block).toTime := rfl
      simp only [DriftExpansionChoice.value, DriftExpansionChoice.toTree,
        DriftExpansionChoice.toTime, DriftExpansionChoice.toTreeTime,
        driftTreeValue, List.map_map]
      rw [htreeList, htimeList, hvalues]

/-- Definition `def:tree-value`: the scalar value `𝒢(𝔗, r)` of a valid timed payoff tree. -/
def TimedPayoffTree.value {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) {u : Finset (Index J noiseDim)} {m : ℕ}
    (timedTree : TimedPayoffTree J noiseDim u m) : ℝ :=
  let childValues := driftTreeValues drift diffusion T x₀ z m
    timedTree.tree.data.children timedTree.assignment.children
  iteratedFDeriv ℝ (timedTree.tree.data.direct.card + childValues.length)
    payoff (stateNat drift diffusion T x₀ z m)
    (vertexDirections timedTree.tree.data.direct
      (fun j ↦ diffusionCoefficient diffusion T j T) childValues)

/-- The analytic term selected at the payoff root by one complete expansion choice. -/
def PayoffExpansionChoice.value {J stateDim noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Input J noiseDim)
    (choice : PayoffExpansionChoice J noiseDim u m) : ℝ :=
  let childValues := (orderedPartitionBlocks choice.partition).map fun block =>
    (choice.children block).value drift diffusion T x₀ z
  iteratedFDeriv ℝ (choice.direct.card + childValues.length)
    payoff (stateNat drift diffusion T x₀ z m)
    (vertexDirections choice.direct
      (fun j ↦ diffusionCoefficient diffusion T j T) childValues)

/-- A complete payoff expansion choice and its corresponding timed payoff tree have the same
scalar value. -/
theorem PayoffExpansionChoice.value_eq_timedPayoffTree
    {J stateDim noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Input J noiseDim)
    (choice : PayoffExpansionChoice J noiseDim u m) :
    choice.value drift payoff diffusion T x₀ z =
      choice.toTimedPayoffTree.value drift payoff diffusion T x₀ z := by
  let blocks := orderedPartitionBlocks choice.partition
  have hvalues :
      driftTreeValues drift diffusion T x₀ z m
          (blocks.map fun block => (choice.children block).toTree)
          (blocks.map fun block => (choice.children block).toTime) =
        blocks.map fun block =>
          (choice.children block).value drift diffusion T x₀ z := by
    induction blocks with
    | nil => simp [driftTreeValues]
    | cons block tail ihTail =>
        simp only [List.map, driftTreeValues]
        rw [← DriftExpansionChoice.value_eq_driftTreeValue]
        rw [ihTail]
  have htreeList :
      blocks.map (Prod.fst ∘ fun block => (choice.children block).toTreeTime) =
        blocks.map fun block => (choice.children block).toTree := rfl
  have htimeList :
      blocks.map (Prod.snd ∘ fun block => (choice.children block).toTreeTime) =
        blocks.map fun block => (choice.children block).toTime := rfl
  have htreeList' :
      (blocks.map fun block => (choice.children block).toTreeTime).map Prod.fst =
        blocks.map fun block => (choice.children block).toTree := by
    simpa only [List.map_map] using htreeList
  have htimeList' :
      (blocks.map fun block => (choice.children block).toTreeTime).map Prod.snd =
        blocks.map fun block => (choice.children block).toTime := by
    simpa only [List.map_map] using htimeList
  have htreeValues :
      driftTreeValues drift diffusion T x₀ z m
          ((blocks.map fun block =>
            (choice.children block).toTreeTime).map Prod.fst)
          ((blocks.map fun block =>
            (choice.children block).toTreeTime).map Prod.snd) =
        blocks.map fun block =>
          (choice.children block).value drift diffusion T x₀ z := by
    rw [htreeList', htimeList']
    exact hvalues
  let rootValue : List (State stateDim) → ℝ := fun childValues =>
    iteratedFDeriv ℝ (choice.direct.card + childValues.length)
      payoff (stateNat drift diffusion T x₀ z m)
      (vertexDirections choice.direct
        (fun j ↦ diffusionCoefficient diffusion T j T) childValues)
  simp only [PayoffExpansionChoice.value, TimedPayoffTree.value,
    PayoffExpansionChoice.toTimedPayoffTree,
    PayoffExpansionChoice.toTreeData, PayoffExpansionChoice.toAssignment]
  change rootValue
      (blocks.map fun block ↦
        (choice.children block).value drift diffusion T x₀ z) =
    rootValue
      (driftTreeValues drift diffusion T x₀ z m
        ((blocks.map fun block ↦
          (choice.children block).toTreeTime).map Prod.fst)
        ((blocks.map fun block ↦
          (choice.children block).toTreeTime).map Prod.snd))
  exact congrArg rootValue htreeValues.symm

/-- The finite sum of the fully expanded terms indexed by complete payoff choices. -/
noncomputable def payoffExpansionSum {J stateDim noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Input J noiseDim) : ℝ :=
  ∑ choice : PayoffExpansionChoice J noiseDim u m,
    choice.value drift payoff diffusion T x₀ z

/-- The finite sum of the analytic values of all admissible timed payoff trees. -/
noncomputable def treeExpansionSum {J stateDim noiseDim m : ℕ}
    {u : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Input J noiseDim) : ℝ :=
  ∑ timedTree : TimedPayoffTree J noiseDim u m,
    timedTree.value drift payoff diffusion T x₀ z

/-- Reindexing complete expansion choices by the proved bijection gives exactly the timed-tree
sum, with equality of the corresponding analytic terms. -/
theorem payoffExpansionSum_eq_treeExpansionSum
    {J stateDim noiseDim m : ℕ} {u : Finset (Index J noiseDim)}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (x₀ : State stateDim) (z : Input J noiseDim) :
    payoffExpansionSum (m := m) (u := u) drift payoff diffusion T x₀ z =
      treeExpansionSum (m := m) (u := u) drift payoff diffusion T x₀ z := by
  let equivalence :=
    PayoffExpansionChoice.equivTimedPayoffTree
      (J := J) (noiseDim := noiseDim) (m := m) (u := u)
  unfold payoffExpansionSum treeExpansionSum
  calc
    (∑ choice : PayoffExpansionChoice J noiseDim u m,
        choice.value drift payoff diffusion T x₀ z) =
        ∑ choice : PayoffExpansionChoice J noiseDim u m,
          (equivalence choice).value drift payoff diffusion T x₀ z := by
      apply Fintype.sum_congr
      intro choice
      exact choice.value_eq_timedPayoffTree drift payoff diffusion T x₀ z
    _ = ∑ timedTree : TimedPayoffTree J noiseDim u m,
        timedTree.value drift payoff diffusion T x₀ z :=
      equivalence.sum_comp _

/-- For the special valid drift leaf `(|S(y)|, c_y) = (1, 0)`, the recursive definition reduces
to the first-derivative summand in Equation `eq:partition-first`. -/
theorem driftTreeValue_singletonLeaf {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    (parentTime time : ℕ) (j : Index J noiseDim) :
    driftTreeValue drift diffusion T x₀ z parentTime
        (.node {j} []) (.node time []) =
      propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J •
          (fderiv ℝ (drift (gridTime T J time))
            (stateNat drift diffusion T x₀ z time))
            (diffusionCoefficient diffusion T j (gridTime T J time))) := by
  let f := drift (gridTime T J time)
  let x := stateNat drift diffusion T x₀ z time
  let directValue : Index J noiseDim → State stateDim :=
    fun k ↦ diffusionCoefficient diffusion T k (gridTime T J time)
  have hderiv :
      iteratedFDeriv ℝ ({j} : Finset (Index J noiseDim)).card f x
          (vertexDirections {j} directValue []) =
        fderiv ℝ f x (directValue j) := by
    rw [iteratedFDeriv_eq_fderiv_of_eq_one f (by simp)]
    simp
  change
    propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J •
          iteratedFDeriv ℝ ({j} : Finset (Index J noiseDim)).card f x
            (vertexDirections {j} directValue [])) =
      propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (stepSize T J • fderiv ℝ f x (directValue j))
  rw [hderiv]

/-- The value of a singleton expansion choice is the corresponding propagated coordinate
forcing. -/
theorem DriftExpansionChoice.singleton_value
    {J stateDim noiseDim parentTime : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    (time : ℕ) (j : Index J noiseDim) (htime : time < parentTime) :
    (DriftExpansionChoice.singleton time j htime).value
        drift diffusion T x₀ z =
      propagator (stepJacobian drift diffusion T x₀ z) parentTime time
        (coordinateForcing drift diffusion T x₀ z time j) := by
  rw [DriftExpansionChoice.value_eq_driftTreeValue]
  rw [DriftExpansionChoice.singleton_toTree]
  rw [DriftExpansionChoice.singleton_toTime]
  rw [driftTreeValue_singletonLeaf]
  unfold coordinateForcing
  rw [eulerDriftInput_eq_stateNat]

/-- The first state-derivative expansion is exactly the sum over complete singleton choices. -/
theorem compensatedStateCoordinateDerivative_eq_sum_singletonChoices
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (parentTime : ℕ) (j : Index J noiseDim) :
    compensatedStateCoordinateDerivative drift diffusion T x₀ parentTime j z =
      ∑ choice : DriftExpansionChoice J noiseDim parentTime {j},
        choice.value drift diffusion T x₀ z := by
  rw [compensatedStateCoordinateDerivative_eq_sum_propagator
    drift diffusion T x₀ hDrift z parentTime j]
  rw [← Fin.sum_univ_eq_sum_range]
  let equivalence :=
    DriftExpansionChoice.singletonEquivFin (parentTime := parentTime) j
  rw [← equivalence.sum_comp]
  apply Fintype.sum_congr
  intro choice
  obtain ⟨time, htime, rfl⟩ := DriftExpansionChoice.singleton_cases j choice
  exact (DriftExpansionChoice.singleton_value
    drift diffusion T x₀ z time j htime).symm

/-- The compensated state derivative is the sum of all complete drift-tree expansions.
This is the recursive state part of the paper's derivative tree formula. -/
theorem compensatedStateDerivative_eq_driftExpansionSum
    {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim)
    (hDrift : ∀ t, ContDiff ℝ ∞ (drift t))
    (z : Input J noiseDim) (parentTime : ℕ)
    (support : Finset (Index J noiseDim)) (hsupport : support.Nonempty) :
    compensatedStateDerivative drift diffusion T x₀ parentTime support z =
      driftExpansionSum (parentTime := parentTime) (support := support)
        drift diffusion T x₀ z := by
  generalize hcardEq : support.card = n
  induction n using Nat.strong_induction_on generalizing support parentTime with
  | h n ih =>
      by_cases hone : n = 1
      · have hcard : support.card = 1 := hcardEq.trans hone
        obtain ⟨j, hsupportEq⟩ := Finset.card_eq_one.mp hcard
        subst support
        unfold compensatedStateDerivative
        rw [mixedDerivative_singleton]
        exact compensatedStateCoordinateDerivative_eq_sum_singletonChoices
          drift diffusion T x₀ hDrift z parentTime j
      · have hpositive : 0 < n := by
          rw [← hcardEq]
          exact Finset.card_pos.mpr hsupport
        have htwo : 2 ≤ support.card := by omega
        rw [compensatedStateDerivative_eq_sum_nonlinearForcing
          drift diffusion T x₀ hDrift z parentTime support hsupport]
        rw [driftExpansionSum_eq_sum_higherCode htwo]
        rw [← Fin.sum_univ_eq_sum_range]
        calc
          (∑ time : Fin parentTime,
              propagator (stepJacobian drift diffusion T x₀ z) parentTime time
                (nonlinearStateForcing drift diffusion T x₀ z time support)) =
            ∑ time : Fin parentTime,
              ∑ root : DriftRootChoice J noiseDim support,
                ∑ children : ∀ block : root.partition.parts,
                    DriftExpansionChoice J noiseDim time block.1,
                  (DriftExpansionChoice.higher time time.isLt root.direct
                    root.direct_subset root.partition root.local_order children).value
                      drift diffusion T x₀ z := by
            apply Fintype.sum_congr
            intro time
            rw [nonlinearStateForcing_eq_sum_driftRootChoices
              drift diffusion T x₀ hDrift z time support htwo]
            rw [Finset.smul_sum, map_sum]
            apply Fintype.sum_congr
            intro root
            apply DriftRootChoice.propagated_localTerm_eq_sum_higherChoices
              drift diffusion T x₀ z hDrift time time.isLt root
            intro block
            apply ih block.val.card
            · rw [← hcardEq]
              exact root.block_card_lt_support block
            · exact root.partition.nonempty_of_mem_parts block.property
            · rfl
          _ = ∑ code : DriftHigherCode J noiseDim parentTime support,
              code.toChoice.value drift diffusion T x₀ z := by
            unfold DriftHigherCode
            rw [Fintype.sum_sigma]
            apply Fintype.sum_congr
            intro time
            rw [Fintype.sum_sigma]
            rfl

/-- For a valid timed payoff tree, the derivative order at the root is exactly
`|S(y_*)| + c_(y_*)`, as in Equation `eq:root-value`. -/
theorem TimedPayoffTree.root_derivative_order {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (diffusion : Diffusion stateDim noiseDim)
    (T : ℝ) (x₀ : State stateDim) (z : Input J noiseDim)
    {u : Finset (Index J noiseDim)} {m : ℕ}
    (timedTree : TimedPayoffTree J noiseDim u m) :
    timedTree.tree.data.direct.card +
        (driftTreeValues drift diffusion T x₀ z m timedTree.tree.data.children
          timedTree.assignment.children).length =
      timedTree.tree.data.direct.card + timedTree.tree.data.children.length := by
  congr 1
  exact driftTreeValues_length_eq_of_validChildren drift diffusion T x₀ z m
    timedTree.tree.data.children timedTree.assignment.children timedTree.assignmentValid.2

/-- The analytic value of the root-only tree is exactly the direct payoff-derivative term in
Equation `eq:root-value`.  This is the first checked small case of the tree-value definition. -/
@[simp]
theorem TimedPayoffTree.rootOnly_value {J stateDim noiseDim : ℕ}
    (drift : Drift stateDim) (payoff : Payoff stateDim)
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ) (x₀ : State stateDim)
    (z : Input J noiseDim) (u : Finset (Index J noiseDim))
    (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    (TimedPayoffTree.rootOnly u hendpoint m).value drift payoff diffusion T x₀ z =
      iteratedFDeriv ℝ u.card payoff (stateNat drift diffusion T x₀ z m)
        (fun k ↦ diffusionCoefficient diffusion T (u.equivFin.symm k).val T) := by
  simp [TimedPayoffTree.value, TimedPayoffTree.rootOnly, TimeAssignment.rootOnly,
    driftTreeValues]
  congr

end


end TimeDependentLattice.Trees
