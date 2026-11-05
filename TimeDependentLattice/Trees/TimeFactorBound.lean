/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import TimeDependentLattice.Regularity.Eta
import TimeDependentLattice.Trees.AnalyticBound

/-!
# Independent time sums for tree vertices

This file formalizes the product-of-sums step in the proof of Proposition 4.3.  Enlarging
admissible tree times to independent choices leaves one factor `eta` for each nonempty direct
block.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open scoped BigOperators
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Euler
open TimeDependentLattice.Regularity
open GevreyBounds

/-- One Brownian-bridge direction factor attached to a direct label at a time index. -/
def directTimeDirectionFactor
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (direct : Finset (Index J noiseDim)) (time : ℕ) : ℝ :=
  ∏ j ∈ direct,
    ‖diffusionCoefficient diffusion T j (gridTime T J time)‖

/-- Direction factors obtained by pairing preorder direct labels with preorder times. -/
def preorderDirectionFactors
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (labels : List (Finset (Index J noiseDim))) (times : List ℕ) : List ℝ :=
  List.zipWith (directTimeDirectionFactor diffusion T) labels times

/-- Recursive timed-tree direction products agree with the preorder label/time pairing. -/
theorem driftTreeDirectionProduct_eq_preorder
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ) :
    ∀ (tree : DriftTreeData J noiseDim) (assignment : DriftTimeData) (parentTime : ℕ),
      assignment.Valid parentTime tree →
        driftTreeDirectionProduct diffusion T tree assignment =
          (preorderDirectionFactors diffusion T tree.directLabels
            assignment.preorderTimes).prod := by
  intro tree
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ ∀ (assignment : DriftTimeData) (parentTime : ℕ),
      assignment.Valid parentTime tree →
        driftTreeDirectionProduct diffusion T tree assignment =
          (preorderDirectionFactors diffusion T tree.directLabels
            assignment.preorderTimes).prod)
    (motive_2 := fun trees ↦ ∀ (assignments : List DriftTimeData) (parentTime : ℕ),
      DriftTimeData.ValidChildren parentTime trees assignments →
        (driftTreeDirectionProducts diffusion T trees assignments).prod =
          (preorderDirectionFactors diffusion T
            (trees.flatMap DriftTreeData.directLabels)
            (assignments.flatMap DriftTimeData.preorderTimes)).prod)
    (fun direct children hchildren assignment parentTime hvalid ↦ by
      cases assignment with
      | node time assignments =>
          simp only [DriftTimeData.Valid] at hvalid
          simp only [driftTreeDirectionProduct, DriftTreeData.directLabels,
            DriftTimeData.preorderTimes, preorderDirectionFactors,
            List.zipWith_cons_cons, List.prod_cons]
          rw [hchildren assignments time hvalid.2]
          rfl)
    (fun assignments _ hvalid ↦ by
      cases assignments <;>
        simp [DriftTimeData.ValidChildren, driftTreeDirectionProducts,
          preorderDirectionFactors] at hvalid ⊢)
    (fun head tail hhead htail assignments parentTime hvalid ↦ by
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          simp only [driftTreeDirectionProducts, List.prod_cons,
            List.flatMap_cons]
          rw [preorderDirectionFactors, List.zipWith_append
            (head.length_directLabels_eq_vertexCount.trans
              (assignment.valid_preorderTimes_length_eq_vertexCount
                head parentTime hvalid.1).symm), List.prod_append,
            hhead assignment parentTime hvalid.1,
            htail assignments parentTime hvalid.2]
          rfl)
    tree

/-- Forest form of `driftTreeDirectionProduct_eq_preorder`. -/
theorem driftTreeDirectionProducts_eq_preorder
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (trees : List (DriftTreeData J noiseDim)) (assignments : List DriftTimeData)
    (parentTime : ℕ)
    (hvalid : DriftTimeData.ValidChildren parentTime trees assignments) :
    (driftTreeDirectionProducts diffusion T trees assignments).prod =
      (preorderDirectionFactors diffusion T
        (trees.flatMap DriftTreeData.directLabels)
        (assignments.flatMap DriftTimeData.preorderTimes)).prod := by
  induction trees generalizing assignments with
  | nil =>
      cases assignments <;>
        simp [DriftTimeData.ValidChildren, driftTreeDirectionProducts,
          preorderDirectionFactors] at hvalid ⊢
  | cons head tail ih =>
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          simp only [driftTreeDirectionProducts, List.prod_cons,
            List.flatMap_cons]
          rw [preorderDirectionFactors, List.zipWith_append
            (head.length_directLabels_eq_vertexCount.trans
              (assignment.valid_preorderTimes_length_eq_vertexCount
                head parentTime hvalid.1).symm), List.prod_append,
            driftTreeDirectionProduct_eq_preorder diffusion T head assignment
              parentTime hvalid.1,
            ih assignments hvalid.2]
          rfl

/-- A paired preorder product can be indexed by any fixed finite type of the common length. -/
theorem preorderDirectionFactors_prod_eq_indexed
    {J stateDim noiseDim n : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (labels : List (Finset (Index J noiseDim))) (times : List ℕ)
    (hlabels : labels.length = n) (htimes : times.length = n) :
    (preorderDirectionFactors diffusion T labels times).prod =
      ∏ vertex : Fin n,
        directTimeDirectionFactor diffusion T
          (labels.get (Fin.cast hlabels.symm vertex))
          (times.get (Fin.cast htimes.symm vertex)) := by
  have hlist : preorderDirectionFactors diffusion T labels times =
      List.ofFn (fun vertex : Fin n ↦
        directTimeDirectionFactor diffusion T
          (labels.get (Fin.cast hlabels.symm vertex))
          (times.get (Fin.cast htimes.symm vertex))) := by
    apply List.ext_get
    · simp [preorderDirectionFactors, hlabels, htimes]
    · intro i hleft hright
      simp [preorderDirectionFactors]
  rw [hlist, List.prod_ofFn]

/-- The number of preorder drift labels is the number of nonroot vertices. -/
theorem PayoffTreeData.length_driftDirectLabels_eq_nonrootVertexCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.driftDirectLabels.length =
      (tree.children.map DriftTreeData.vertexCount).sum := by
  have hcount := tree.length_driftDirectLabels_add_one_eq_vertexCount
  simp only [PayoffTreeData.vertexCount] at hcount
  omega

/-- The product below a payoff root is the product indexed by the independent-time encoding. -/
theorem payoffTreeNonrootDirectionProduct_eq_encoding
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (tree : PayoffTreeData J noiseDim) (assignment : TimeAssignment)
    (hvalid : assignment.Valid (numSteps J) tree) :
    payoffTreeNonrootDirectionProduct diffusion T tree assignment =
      ∏ vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum,
        ∏ j ∈ tree.driftDirectLabels.get
            (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex),
          ‖diffusionCoefficient diffusion T j
            (gridTime T J (assignment.independentTimeEncoding hvalid vertex).val)‖ := by
  rw [payoffTreeNonrootDirectionProduct,
    driftTreeDirectionProducts_eq_preorder diffusion T tree.children
      assignment.children (numSteps J) hvalid.2]
  change (preorderDirectionFactors diffusion T tree.driftDirectLabels
    assignment.driftPreorderTimes).prod = _
  rw [preorderDirectionFactors_prod_eq_indexed diffusion T
      tree.driftDirectLabels assignment.driftPreorderTimes
      tree.length_driftDirectLabels_eq_nonrootVertexCount
      (TimeAssignment.valid_driftPreorderTimes_length hvalid)]
  apply Finset.prod_congr rfl
  intro vertex _
  rfl

/-- Valid time assignments of a fixed tree form a finite family: their preorder encodings are
injective and take values in a finite function type. -/
noncomputable instance instFiniteValidTimeAssignment
    {J noiseDim m : ℕ} {tree : PayoffTreeData J noiseDim} :
    Finite {assignment : TimeAssignment // assignment.Valid m tree} :=
  Finite.of_injective
    (fun assignment ↦ assignment.1.independentTimeEncoding assignment.2)
    TimeAssignment.independentTimeEncoding_injective

noncomputable instance instFintypeValidTimeAssignment
    {J noiseDim m : ℕ} {tree : PayoffTreeData J noiseDim} :
    Fintype {assignment : TimeAssignment // assignment.Valid m tree} :=
  Fintype.ofFinite _

/-- Indexed form of the independent-time factorization.  The index type may be the set of
drift vertices of a fixed tree, so repeated labels (in particular several empty labels) are
retained. -/
theorem independent_time_sum_eq_eta_product_indexed
    {J stateDim noiseDim : ℕ} {Vertex : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (label : Vertex → Finset (Index J noiseDim)) :
    stepSize T J ^ Fintype.card Vertex *
        ∑ times : Vertex → Fin (numSteps J),
          ∏ vertex : Vertex,
            ∏ j ∈ label vertex,
              ‖diffusionCoefficient diffusion T j
                (gridTime T J (times vertex).val)‖ =
      ∏ vertex : Vertex, eta diffusion T (label vertex) := by
  let f : Vertex → Fin (numSteps J) → ℝ := fun vertex time ↦
    ∏ j ∈ label vertex,
      ‖diffusionCoefficient diffusion T j (gridTime T J time.val)‖
  calc
    stepSize T J ^ Fintype.card Vertex *
        ∑ times : Vertex → Fin (numSteps J),
          ∏ vertex : Vertex,
            ∏ j ∈ label vertex,
              ‖diffusionCoefficient diffusion T j
                (gridTime T J (times vertex).val)‖ =
      (∏ _vertex : Vertex, stepSize T J) *
        ∑ times : Vertex → Fin (numSteps J),
          ∏ vertex : Vertex, f vertex (times vertex) := by
      simp only [f]
      congr 1
      simp [Finset.prod_const]
    _ = (∏ _vertex : Vertex, stepSize T J) *
        ∏ vertex : Vertex, ∑ time : Fin (numSteps J), f vertex time := by
      rw [Fintype.prod_sum]
    _ = ∏ vertex : Vertex,
        (stepSize T J * ∑ time : Fin (numSteps J), f vertex time) := by
      rw [← Finset.prod_mul_distrib]
    _ = ∏ vertex : Vertex, eta diffusion T (label vertex) := by
      apply Fintype.prod_congr
      intro vertex
      unfold eta f
      congr 1
      exact Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ ∏ j ∈ label vertex,
          ‖diffusionCoefficient diffusion T j (gridTime T J i)‖)
        (numSteps J)

/-- Enlarging admissible ordered tree times to independent times bounds the time sum by the
product of the corresponding `eta` factors. -/
theorem timeAssignment_direction_sum_le_independent
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (hT : 0 ≤ T) (tree : PayoffTreeData J noiseDim) :
    stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        ∑ assignment : {assignment : TimeAssignment //
            assignment.Valid (numSteps J) tree},
          payoffTreeNonrootDirectionProduct diffusion T tree assignment.1 ≤
      ∏ vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum,
        eta diffusion T (tree.driftDirectLabels.get
          (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex)) := by
  let encode : {assignment : TimeAssignment //
      assignment.Valid (numSteps J) tree} →
      (Fin (tree.children.map DriftTreeData.vertexCount).sum → Fin (numSteps J)) :=
    fun assignment ↦ assignment.1.independentTimeEncoding assignment.2
  let summand :
      (Fin (tree.children.map DriftTreeData.vertexCount).sum → Fin (numSteps J)) → ℝ :=
    fun times ↦
      ∏ vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum,
        ∏ j ∈ tree.driftDirectLabels.get
            (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex),
          ‖diffusionCoefficient diffusion T j
            (gridTime T J (times vertex).val)‖
  have hencode : Function.Injective encode := by
    exact TimeAssignment.independentTimeEncoding_injective
  have hrewrite :
      (∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree},
        payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) =
      ∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree}, summand (encode assignment) := by
    apply Fintype.sum_congr
    intro assignment
    exact payoffTreeNonrootDirectionProduct_eq_encoding diffusion T tree
      assignment.1 assignment.2
  have hsum :
      (∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree}, summand (encode assignment)) ≤
        ∑ times : Fin (tree.children.map DriftTreeData.vertexCount).sum →
          Fin (numSteps J), summand times := by
    calc
      (∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree}, summand (encode assignment)) =
          ∑ times ∈ Finset.image encode Finset.univ, summand times := by
            symm
            exact Finset.sum_image (Set.injOn_of_injective hencode)
      _ ≤ ∑ times : Fin (tree.children.map DriftTreeData.vertexCount).sum →
          Fin (numSteps J), summand times := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro times _ _
            dsimp [summand]
            positivity
  rw [hrewrite]
  calc
    stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        ∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree}, summand (encode assignment) ≤
      stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        ∑ times : Fin (tree.children.map DriftTreeData.vertexCount).sum →
          Fin (numSteps J), summand times :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (stepSize_nonneg hT J) _)
    _ = ∏ vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum,
        eta diffusion T (tree.driftDirectLabels.get
          (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex)) := by
      simpa [summand] using
        (independent_time_sum_eq_eta_product_indexed diffusion T
          (fun vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum ↦
            tree.driftDirectLabels.get
              (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex)))

/-- The indexed eta product is exactly the preorder-list eta product. -/
theorem PayoffTreeData.eta_indexed_product_eq_list_product
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (tree : PayoffTreeData J noiseDim) :
    (∏ vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum,
        eta diffusion T (tree.driftDirectLabels.get
          (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex))) =
      (tree.driftDirectLabels.map (eta diffusion T)).prod := by
  calc
    (∏ vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum,
        eta diffusion T (tree.driftDirectLabels.get
          (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex))) =
      ∏ vertex : Fin tree.driftDirectLabels.length,
        eta diffusion T (tree.driftDirectLabels.get vertex) := by
          exact Fintype.prod_equiv
            (finCongr tree.length_driftDirectLabels_eq_nonrootVertexCount.symm)
            (fun vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum ↦
              eta diffusion T (tree.driftDirectLabels.get
                (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex)))
            (fun vertex : Fin tree.driftDirectLabels.length ↦
              eta diffusion T (tree.driftDirectLabels.get vertex))
            (fun _ ↦ rfl)
    _ = (tree.driftDirectLabels.map (eta diffusion T)).prod := by
      exact Fin.prod_univ_fun_getElem tree.driftDirectLabels (eta diffusion T)

/-- Independent choices of one Euler time for every block factor exactly into the product of
the paper's `η_m(S)` quantities. -/
theorem independent_time_sum_eq_eta_product
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (blocks : Finset (Finset (Index J noiseDim))) :
    stepSize T J ^ blocks.card *
        ∑ times : (block : ↥blocks) → Fin (numSteps J),
          ∏ block : ↥blocks,
            ∏ j ∈ block.1,
              ‖diffusionCoefficient diffusion T j
                (gridTime T J (times block).val)‖ =
      ∏ block ∈ blocks, eta diffusion T block := by
  let f : (block : ↥blocks) → Fin (numSteps J) → ℝ := fun block time ↦
    ∏ j ∈ block.1,
      ‖diffusionCoefficient diffusion T j (gridTime T J time.val)‖
  calc
    stepSize T J ^ blocks.card *
        ∑ times : (block : ↥blocks) → Fin (numSteps J),
          ∏ block : ↥blocks,
            ∏ j ∈ block.1,
              ‖diffusionCoefficient diffusion T j
                (gridTime T J (times block).val)‖ =
      (∏ _block : ↥blocks, stepSize T J) *
        ∑ times : (block : ↥blocks) → Fin (numSteps J),
          ∏ block : ↥blocks, f block (times block) := by
        simp only [f]
        congr 1
        simp [Finset.prod_const]
    _ = (∏ _block : ↥blocks, stepSize T J) *
        ∏ block : ↥blocks, ∑ time : Fin (numSteps J), f block time := by
      rw [Fintype.prod_sum]
    _ = ∏ block : ↥blocks,
        (stepSize T J * ∑ time : Fin (numSteps J), f block time) := by
      rw [← Finset.prod_mul_distrib]
    _ = ∏ block : ↥blocks, eta diffusion T block.1 := by
      apply Fintype.prod_congr
      intro block
      unfold eta f
      congr 1
      exact Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ ∏ j ∈ block.1,
          ‖diffusionCoefficient diffusion T j (gridTime T J i)‖)
        (numSteps J)
    _ = ∏ block ∈ blocks, eta diffusion T block := by
      exact Finset.prod_attach blocks (eta diffusion T)

private theorem eta_directLabels_product
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (labels : List (Finset (Index J noiseDim))) :
    (labels.map (eta diffusion T)).prod =
      T ^ (labels.filter fun direct ↦ decide (direct = ∅)).length *
        ((labels.filter fun direct ↦ decide direct.Nonempty).map
          (eta diffusion T)).prod := by
  induction labels with
  | nil => simp
  | cons direct labels ih =>
      by_cases hdirect : direct.Nonempty
      · have hne : direct ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hdirect
        simp [hdirect, hne, ih]
        ring
      · have hempty : direct = ∅ := Finset.not_nonempty_iff_eq_empty.mp hdirect
        subst direct
        simp [ih, pow_succ]
        ring

/-- The independent time factors of all drift vertices split into `T^k₀` for empty direct
labels and one `η_m(S)` for every block of `π`. -/
theorem PayoffTreeData.eta_driftDirectLabels_product_eq
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (tree : PayoffTreeData J noiseDim)
    (blocks : Finset (Finset (Index J noiseDim)))
    (hblocks : tree.nonemptyDirectLabels.Perm blocks.toList) :
    (tree.driftDirectLabels.map (eta diffusion T)).prod =
      T ^ tree.emptyDriftCount * ∏ block ∈ blocks, eta diffusion T block := by
  rw [eta_directLabels_product diffusion T tree.driftDirectLabels]
  change T ^ tree.emptyDirectLabels.length *
      (tree.nonemptyDirectLabels.map (eta diffusion T)).prod = _
  rw [tree.length_emptyDirectLabels_eq_emptyDriftCount]
  have hperm := hblocks.map (eta diffusion T)
  rw [hperm.prod_eq]
  simp

/-- Fixed-tree time-sum bound in the exact form used in paper Lemma B.8.  Empty direct labels
contribute powers of `T`; the nonempty labels contribute the partition-block eta factors. -/
theorem timeAssignment_direction_sum_le_eta_factors
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim) (T : ℝ)
    (hT : 0 ≤ T) (tree : PayoffTreeData J noiseDim)
    (blocks : Finset (Finset (Index J noiseDim)))
    (hblocks : tree.nonemptyDirectLabels.Perm blocks.toList) :
    stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        ∑ assignment : {assignment : TimeAssignment //
            assignment.Valid (numSteps J) tree},
          payoffTreeNonrootDirectionProduct diffusion T tree assignment.1 ≤
      T ^ tree.emptyDriftCount * ∏ block ∈ blocks, eta diffusion T block := by
  calc
    stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        ∑ assignment : {assignment : TimeAssignment //
            assignment.Valid (numSteps J) tree},
          payoffTreeNonrootDirectionProduct diffusion T tree assignment.1 ≤
      ∏ vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum,
        eta diffusion T (tree.driftDirectLabels.get
          (Fin.cast tree.length_driftDirectLabels_eq_nonrootVertexCount.symm vertex)) :=
      timeAssignment_direction_sum_le_independent diffusion T hT tree
    _ = (tree.driftDirectLabels.map (eta diffusion T)).prod :=
      tree.eta_indexed_product_eq_list_product diffusion T
    _ = T ^ tree.emptyDriftCount * ∏ block ∈ blocks, eta diffusion T block :=
      tree.eta_driftDirectLabels_product_eq diffusion T blocks hblocks

/-- The factored majorants of all valid time assignments of one fixed tree. -/
theorem timeAssignment_factoredMajorant_sum_le_eta_factors
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    (tree : PayoffTreeData J noiseDim)
    (blocks : Finset (Finset (Index J noiseDim)))
    (hblocks : tree.nonemptyDirectLabels.Perm blocks.toList) :
    (∑ assignment : {assignment : TimeAssignment //
        assignment.Valid (numSteps J) tree},
      stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion tree *
        payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) ≤
      PayoffTreeData.analyticCoefficient bounds diffusion tree *
        (T ^ tree.emptyDriftCount * ∏ block ∈ blocks, eta diffusion T block) := by
  have htime := timeAssignment_direction_sum_le_eta_factors
    diffusion T hT tree blocks hblocks
  have hcoefficient :=
    GevreyBounds.PayoffTreeData.analyticCoefficient_nonneg bounds diffusion tree
  calc
    (∑ assignment : {assignment : TimeAssignment //
        assignment.Valid (numSteps J) tree},
      stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion tree *
        payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) =
      ∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree},
        PayoffTreeData.analyticCoefficient bounds diffusion tree *
          (stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
            payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) := by
      apply Fintype.sum_congr
      intro assignment
      ring
    _ = PayoffTreeData.analyticCoefficient bounds diffusion tree *
        (∑ assignment : {assignment : TimeAssignment //
            assignment.Valid (numSteps J) tree},
          stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
            payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) := by
      conv_rhs => rw [Finset.mul_sum]
    _ =
      PayoffTreeData.analyticCoefficient bounds diffusion tree *
        (stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
          ∑ assignment : {assignment : TimeAssignment //
              assignment.Valid (numSteps J) tree},
            payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) := by
      congr 1
      rw [Finset.mul_sum]
    _ ≤ PayoffTreeData.analyticCoefficient bounds diffusion tree *
        (T ^ tree.emptyDriftCount * ∏ block ∈ blocks, eta diffusion T block) :=
      mul_le_mul_of_nonneg_left htime hcoefficient

/-- Lemma B.8 combined with the time relaxation, for an arbitrary finite realization of the
paper's family `Γ(E, π)`. -/
theorem fixedPartition_factoredMajorant_sum_le
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (support root : Finset (Index J noiseDim))
    (hblocksNonempty : blocks.Nonempty)
    (hvalid : ∀ tree ∈ family, tree.Valid support)
    (hroot : ∀ tree ∈ family, tree.direct = root)
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList) :
    (∑ tree ∈ family,
      ∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree},
        stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
          PayoffTreeData.analyticCoefficient bounds diffusion tree *
          payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) ≤
      (max 1 T ^ blocks.card * ∏ block ∈ blocks, eta diffusion T block) *
        (bounds.coefficientCountBase ^ (support.card + blocks.card) *
          ((root.card.factorial : ℝ) ^ bounds.τ *
            ∏ j ∈ root, ‖diffusionCoefficient diffusion T j T‖) *
          (∏ block ∈ blocks, (block.card.factorial : ℝ) ^ bounds.τ) *
          (64 : ℝ) ^ blocks.card *
          (blocks.card.factorial : ℝ) ^ bounds.τ) := by
  let timeFactor : ℝ :=
    max 1 T ^ blocks.card * ∏ block ∈ blocks, eta diffusion T block
  let coefficientBound : ℝ :=
    bounds.coefficientCountBase ^ (support.card + blocks.card) *
      ((root.card.factorial : ℝ) ^ bounds.τ *
        ∏ j ∈ root, ‖diffusionCoefficient diffusion T j T‖) *
      (∏ block ∈ blocks, (block.card.factorial : ℝ) ^ bounds.τ) *
      (64 : ℝ) ^ blocks.card *
      (blocks.card.factorial : ℝ) ^ bounds.τ
  have htreeTime : ∀ tree ∈ family,
      (∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree},
        stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
          PayoffTreeData.analyticCoefficient bounds diffusion tree *
          payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) ≤
        PayoffTreeData.analyticCoefficient bounds diffusion tree * timeFactor := by
    intro tree htree
    have hfixed := timeAssignment_factoredMajorant_sum_le_eta_factors
      bounds diffusion hT tree blocks (hblocks tree htree)
    have hcount : tree.nonemptyDriftCount = blocks.card := by
      have hlength := (hblocks tree htree).length_eq
      rw [tree.length_nonemptyDirectLabels_eq_nonemptyDriftCount] at hlength
      simpa using hlength
    have hchildren : tree.children ≠ [] := by
      intro hempty
      have hzero : tree.nonemptyDriftCount = 0 := by
        simp [PayoffTreeData.nonemptyDriftCount, hempty]
      have hblocksZero : blocks.card = 0 := by omega
      exact hblocksNonempty.ne_empty (Finset.card_eq_zero.mp hblocksZero)
    have hempty : tree.emptyDriftCount ≤ blocks.card := by
      have hlt := tree.emptyDriftCount_lt_nonemptyDriftCount
        (hvalid tree htree) hchildren
      rw [hcount] at hlt
      omega
    have hTpow : T ^ tree.emptyDriftCount ≤ max 1 T ^ blocks.card := by
      exact (pow_le_pow_left₀ hT (le_max_right 1 T) tree.emptyDriftCount).trans
        (pow_le_pow_right₀ (le_max_left 1 T) hempty)
    have heta : 0 ≤ ∏ block ∈ blocks, eta diffusion T block :=
      Finset.prod_nonneg fun block _ ↦ eta_nonneg diffusion hT block
    have hfactor :
        T ^ tree.emptyDriftCount * ∏ block ∈ blocks, eta diffusion T block ≤
          timeFactor := by
      dsimp [timeFactor]
      exact mul_le_mul_of_nonneg_right hTpow heta
    exact hfixed.trans (mul_le_mul_of_nonneg_left hfactor
      (GevreyBounds.PayoffTreeData.analyticCoefficient_nonneg
        bounds diffusion tree))
  have htimeFactor : 0 ≤ timeFactor := by
    dsimp [timeFactor]
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (Finset.prod_nonneg fun block _ ↦ eta_nonneg diffusion hT block)
  have hcoefficient := analyticCoefficient_sum_le bounds diffusion
    family blocks support root hblocksNonempty hvalid hroot hblocks
  change _ ≤ timeFactor * coefficientBound
  calc
    (∑ tree ∈ family,
      ∑ assignment : {assignment : TimeAssignment //
          assignment.Valid (numSteps J) tree},
        stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
          PayoffTreeData.analyticCoefficient bounds diffusion tree *
          payoffTreeNonrootDirectionProduct diffusion T tree assignment.1) ≤
      ∑ tree ∈ family,
        PayoffTreeData.analyticCoefficient bounds diffusion tree * timeFactor := by
      exact Finset.sum_le_sum fun tree htree ↦ htreeTime tree htree
    _ = timeFactor *
        (∑ tree ∈ family,
          PayoffTreeData.analyticCoefficient bounds diffusion tree) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tree _
      ring
    _ ≤ timeFactor * coefficientBound := by
      exact mul_le_mul_of_nonneg_left hcoefficient htimeFactor

end

end TimeDependentLattice.Trees
