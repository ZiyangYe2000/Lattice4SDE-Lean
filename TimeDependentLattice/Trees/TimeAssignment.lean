/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.Counting

/-!
# Admissible time assignments for payoff trees

A time assignment has the same recursive shape as a payoff tree.  The payoff root is fixed at
the terminal Euler index `m`, and every drift vertex has a strictly smaller time than its parent.
-/

namespace TimeDependentLattice.Trees

noncomputable section

/-- Time labels on a drift subtree. -/
inductive DriftTimeData where
  | node (time : ℕ) (children : List DriftTimeData)

noncomputable instance : DecidableEq DriftTimeData := Classical.decEq _

/-- A time label for the payoff root together with labels for its drift subtrees. -/
structure TimeAssignment where
  rootTime : ℕ
  children : List DriftTimeData

noncomputable instance : DecidableEq TimeAssignment := Classical.decEq _

def DriftTimeData.time : DriftTimeData → ℕ
  | .node time _ => time

def DriftTimeData.children : DriftTimeData → List DriftTimeData
  | .node _ children => children

/-- Drift-vertex times in the same preorder used by `DriftTreeData.directLabels`. -/
def DriftTimeData.preorderTimes : DriftTimeData → List ℕ
  | .node time children => time :: children.flatMap DriftTimeData.preorderTimes

/-- All nonroot times of a payoff assignment, in preorder within the root forest. -/
def TimeAssignment.driftPreorderTimes (assignment : TimeAssignment) : List ℕ :=
  assignment.children.flatMap DriftTimeData.preorderTimes

/- Validity of one drift time label and, mutually, of the time labels on a list of children. -/
mutual
  def DriftTimeData.Valid {J noiseDim : ℕ} (parentTime : ℕ) :
      DriftTreeData J noiseDim → DriftTimeData → Prop
    | .node _ treeChildren, .node time timeChildren =>
        time < parentTime ∧ ValidChildren time treeChildren timeChildren
  termination_by tree _ => sizeOf tree

  def DriftTimeData.ValidChildren {J noiseDim : ℕ} (parentTime : ℕ) :
      List (DriftTreeData J noiseDim) → List DriftTimeData → Prop
    | [], [] => True
    | child :: children, assignment :: assignments =>
        assignment.Valid parentTime child ∧
          ValidChildren parentTime children assignments
    | _, _ => False
  termination_by trees _ => sizeOf trees
end

/-- The root is at `m`, the time data have exactly the tree shape, and all edge inequalities are
strict. -/
def TimeAssignment.Valid {J noiseDim : ℕ} (assignment : TimeAssignment) (m : ℕ)
    (tree : PayoffTreeData J noiseDim) : Prop :=
  assignment.rootTime = m ∧
    DriftTimeData.ValidChildren m tree.children assignment.children

/-- A pair `(𝔗, r)` with `𝔗 ∈ 𝒯(u)` and `r ∈ ℛ_m(𝔗)` in the notation of Definitions
`def:tree` and `def:time-assignment`.

The recursive validity predicate forces the time data to have exactly the tree shape.  Natural
number-valued times supply the lower bound zero, the root equation supplies `r_root = m`, and the
edge conditions supply the strict inequalities at every nonroot vertex. -/
structure TimedPayoffTree (J noiseDim : ℕ) (u : Finset (BrownianBridge.Index J noiseDim))
    (m : ℕ) where
  tree : LabelledPayoffTree J noiseDim u
  assignment : TimeAssignment
  assignmentValid : assignment.Valid m tree.data

namespace TimedPayoffTree

@[ext]
theorem ext {J noiseDim : ℕ} {u : Finset (BrownianBridge.Index J noiseDim)} {m : ℕ}
    {left right : TimedPayoffTree J noiseDim u m}
    (htree : left.tree = right.tree) (hassignment : left.assignment = right.assignment) :
    left = right := by
  cases left
  cases right
  simp_all

@[simp]
theorem rootTime_eq {J noiseDim : ℕ} {u : Finset (BrownianBridge.Index J noiseDim)} {m : ℕ}
    (tree : TimedPayoffTree J noiseDim u m) : tree.assignment.rootTime = m :=
  tree.assignmentValid.1

@[simp]
theorem support_eq {J noiseDim : ℕ} {u : Finset (BrownianBridge.Index J noiseDim)} {m : ℕ}
    (tree : TimedPayoffTree J noiseDim u m) : tree.tree.data.support = u :=
  tree.tree.valid.1

end TimedPayoffTree

/-- The unique shape of a time assignment for a root-only tree. -/
def TimeAssignment.rootOnly (m : ℕ) : TimeAssignment := ⟨m, []⟩

theorem TimeAssignment.rootOnly_valid {J noiseDim : ℕ}
    (m : ℕ) (direct : Finset (BrownianBridge.Index J noiseDim)) :
    (TimeAssignment.rootOnly m).Valid m (PayoffTreeData.mk direct []) := by
  rw [TimeAssignment.Valid, TimeAssignment.rootOnly]
  constructor
  · rfl
  · rw [DriftTimeData.ValidChildren]
    trivial

/-- A valid assignment for a root-only tree is the canonical root-only assignment. -/
theorem TimeAssignment.eq_rootOnly_of_valid {J noiseDim m : ℕ}
    (direct : Finset (BrownianBridge.Index J noiseDim))
    (assignment : TimeAssignment)
    (hvalid : assignment.Valid m (PayoffTreeData.mk direct [])) :
    assignment = TimeAssignment.rootOnly m := by
  cases assignment with
  | mk rootTime children =>
      simp only [TimeAssignment.Valid, PayoffTreeData.children] at hvalid
      have hchildren : children = [] := by
        cases children with
        | nil => rfl
        | cons head tail => simp [DriftTimeData.ValidChildren] at hvalid
      subst children
      simp [TimeAssignment.rootOnly, hvalid.1]

/-- The root-only timed payoff tree.  It represents the exceptional root-only case explicitly
included in Definition `def:tree`. -/
def TimedPayoffTree.rootOnly {J noiseDim : ℕ}
    (u : Finset (BrownianBridge.Index J noiseDim))
    (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    TimedPayoffTree J noiseDim u m where
  tree := LabelledPayoffTree.rootOnly u hendpoint
  assignment := TimeAssignment.rootOnly m
  assignmentValid := TimeAssignment.rootOnly_valid m u

@[simp]
theorem TimedPayoffTree.rootOnly_tree {J noiseDim : ℕ}
    (u : Finset (BrownianBridge.Index J noiseDim))
    (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    (TimedPayoffTree.rootOnly u hendpoint m).tree =
      LabelledPayoffTree.rootOnly u hendpoint :=
  rfl

@[simp]
theorem TimedPayoffTree.rootOnly_assignment {J noiseDim : ℕ}
    (u : Finset (BrownianBridge.Index J noiseDim))
    (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    (TimedPayoffTree.rootOnly u hendpoint m).assignment = TimeAssignment.rootOnly m :=
  rfl

/-- The time at a valid nonroot vertex is smaller than its parent's time. -/
theorem DriftTimeData.valid_time_lt_parent {J noiseDim : ℕ}
    {parentTime : ℕ} {tree : DriftTreeData J noiseDim} {assignment : DriftTimeData}
    (hvalid : assignment.Valid parentTime tree) : assignment.time < parentTime := by
  cases tree with
  | node direct children =>
      cases assignment with
      | node time times =>
          simp only [DriftTimeData.Valid] at hvalid
          exact hvalid.1

/-- No drift vertex can be assigned below parent time zero. -/
theorem DriftTimeData.valid_at_zero_impossible {J noiseDim : ℕ}
    {tree : DriftTreeData J noiseDim} {assignment : DriftTimeData} :
    ¬ assignment.Valid 0 tree := by
  intro hvalid
  exact Nat.not_lt_zero _ (assignment.valid_time_lt_parent hvalid)

/-- Valid child-time data have exactly as many entries as the child-tree list. -/
theorem DriftTimeData.validChildren_length_eq {J noiseDim parentTime : ℕ}
    {trees : List (DriftTreeData J noiseDim)} {assignments : List DriftTimeData}
    (hvalid : DriftTimeData.ValidChildren parentTime trees assignments) :
    trees.length = assignments.length := by
  induction trees generalizing assignments with
  | nil =>
      cases assignments with
      | nil => rfl
      | cons assignment assignments =>
          simp [DriftTimeData.ValidChildren] at hvalid
  | cons tree trees ih =>
      cases assignments with
      | nil =>
          simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          simp [ih hvalid.2]

/-- A valid drift assignment has one preorder time for every drift vertex. -/
theorem DriftTimeData.valid_preorderTimes_length_eq_vertexCount
    {J noiseDim : ℕ} :
    ∀ (tree : DriftTreeData J noiseDim) (assignment : DriftTimeData) (parentTime : ℕ),
      assignment.Valid parentTime tree →
        assignment.preorderTimes.length = tree.vertexCount := by
  intro tree
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ ∀ (assignment : DriftTimeData) (parentTime : ℕ),
      assignment.Valid parentTime tree →
        assignment.preorderTimes.length = tree.vertexCount)
    (motive_2 := fun trees ↦ ∀ (assignments : List DriftTimeData) (parentTime : ℕ),
      DriftTimeData.ValidChildren parentTime trees assignments →
        (assignments.flatMap DriftTimeData.preorderTimes).length =
          (trees.map DriftTreeData.vertexCount).sum)
    (fun direct children hchildren assignment parentTime hvalid ↦ by
      cases assignment with
      | node time assignments =>
          simp only [DriftTimeData.Valid] at hvalid
          simp only [DriftTimeData.preorderTimes, List.length_cons,
            DriftTreeData.vertexCount]
          rw [hchildren assignments time hvalid.2]
          omega)
    (fun assignments _ hvalid ↦ by
      cases assignments <;>
        simp [DriftTimeData.ValidChildren] at hvalid ⊢)
    (fun head tail hhead htail assignments parentTime hvalid ↦ by
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
          rw [hhead assignment parentTime hvalid.1,
            htail assignments parentTime hvalid.2])
    tree

/-- Every time appearing below a valid drift root is smaller than the parent time. -/
theorem DriftTimeData.valid_preorderTimes_lt_parent
    {J noiseDim : ℕ} :
    ∀ (tree : DriftTreeData J noiseDim) (assignment : DriftTimeData) (parentTime : ℕ),
      assignment.Valid parentTime tree →
        ∀ time ∈ assignment.preorderTimes, time < parentTime := by
  intro tree
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦ ∀ (assignment : DriftTimeData) (parentTime : ℕ),
      assignment.Valid parentTime tree →
        ∀ time ∈ assignment.preorderTimes, time < parentTime)
    (motive_2 := fun trees ↦ ∀ (assignments : List DriftTimeData) (parentTime : ℕ),
      DriftTimeData.ValidChildren parentTime trees assignments →
        ∀ time ∈ assignments.flatMap DriftTimeData.preorderTimes,
          time < parentTime)
    (fun direct children hchildren assignment parentTime hvalid ↦ by
      cases assignment with
      | node rootTime assignments =>
          simp only [DriftTimeData.Valid] at hvalid
          intro time htime
          simp only [DriftTimeData.preorderTimes, List.mem_cons] at htime
          rcases htime with rfl | htime
          · exact hvalid.1
          · exact (hchildren assignments rootTime hvalid.2 time htime).trans hvalid.1)
    (fun assignments _ hvalid ↦ by
      cases assignments <;>
        simp [DriftTimeData.ValidChildren] at hvalid ⊢)
    (fun head tail hhead htail assignments parentTime hvalid ↦ by
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          intro time htime
          simp only [List.flatMap_cons, List.mem_append] at htime
          rcases htime with htime | htime
          · exact hhead assignment parentTime hvalid.1 time htime
          · exact htail assignments parentTime hvalid.2 time htime)
    tree

/-- For a fixed tree shape, valid assignments are determined by their preorder time list. -/
theorem DriftTimeData.eq_of_valid_of_preorderTimes_eq
    {J noiseDim : ℕ} :
    ∀ (tree : DriftTreeData J noiseDim) (left right : DriftTimeData) (parentTime : ℕ),
      left.Valid parentTime tree → right.Valid parentTime tree →
        left.preorderTimes = right.preorderTimes → left = right := by
  intro tree
  exact DriftTreeData.rec
    (motive_1 := fun tree ↦
      ∀ (left right : DriftTimeData) (parentTime : ℕ),
        left.Valid parentTime tree → right.Valid parentTime tree →
          left.preorderTimes = right.preorderTimes → left = right)
    (motive_2 := fun trees ↦
      ∀ (left right : List DriftTimeData) (parentTime : ℕ),
        DriftTimeData.ValidChildren parentTime trees left →
        DriftTimeData.ValidChildren parentTime trees right →
        left.flatMap DriftTimeData.preorderTimes =
          right.flatMap DriftTimeData.preorderTimes → left = right)
    (fun direct children hchildren left right parentTime hleft hright htimes ↦ by
      cases left with
      | node leftTime leftChildren =>
          cases right with
          | node rightTime rightChildren =>
              simp only [DriftTimeData.Valid] at hleft hright
              simp only [DriftTimeData.preorderTimes, List.cons.injEq] at htimes
              have hchildrenEq := hchildren leftChildren rightChildren leftTime
                hleft.2 (by simpa [htimes.1] using hright.2) htimes.2
              have htimeEq : leftTime = rightTime := htimes.1
              subst rightTime
              subst rightChildren
              rfl)
    (fun left right _ hleft hright htimes ↦ by
      cases left <;> cases right <;>
        simp [DriftTimeData.ValidChildren] at hleft hright htimes ⊢)
    (fun head tail hhead htail left right parentTime hleft hright htimes ↦ by
      cases left with
      | nil => simp [DriftTimeData.ValidChildren] at hleft
      | cons leftHead leftTail =>
          cases right with
          | nil => simp [DriftTimeData.ValidChildren] at hright
          | cons rightHead rightTail =>
              simp only [DriftTimeData.ValidChildren] at hleft hright
              simp only [List.flatMap_cons] at htimes
              have hlength : leftHead.preorderTimes.length =
                  rightHead.preorderTimes.length := by
                rw [leftHead.valid_preorderTimes_length_eq_vertexCount
                    head parentTime hleft.1,
                  rightHead.valid_preorderTimes_length_eq_vertexCount
                    head parentTime hright.1]
              have hparts := List.append_inj htimes hlength
              have hheadEq := hhead leftHead rightHead parentTime
                hleft.1 hright.1 hparts.1
              have htailEq := htail leftTail rightTail parentTime
                hleft.2 hright.2 hparts.2
              subst rightHead
              subst rightTail
              rfl)
    tree

theorem TimeAssignment.eq_of_valid_of_driftPreorderTimes_eq
    {J noiseDim m : ℕ} {tree : PayoffTreeData J noiseDim}
    {left right : TimeAssignment}
    (hleft : left.Valid m tree) (hright : right.Valid m tree)
    (htimes : left.driftPreorderTimes = right.driftPreorderTimes) :
    left = right := by
  have hchildren : left.children = right.children := by
    unfold TimeAssignment.driftPreorderTimes at htimes
    have hforest : ∀ (trees : List (DriftTreeData J noiseDim))
        (left right : List DriftTimeData) (parentTime : ℕ),
        DriftTimeData.ValidChildren parentTime trees left →
        DriftTimeData.ValidChildren parentTime trees right →
        left.flatMap DriftTimeData.preorderTimes =
          right.flatMap DriftTimeData.preorderTimes → left = right := by
      intro trees
      induction trees with
      | nil =>
          intro left right parentTime hl hr ht
          cases left <;> cases right <;>
            simp [DriftTimeData.ValidChildren] at hl hr ht ⊢
      | cons head tail ih =>
          intro left right parentTime hl hr ht
          cases left with
          | nil => simp [DriftTimeData.ValidChildren] at hl
          | cons leftHead leftTail =>
              cases right with
              | nil => simp [DriftTimeData.ValidChildren] at hr
              | cons rightHead rightTail =>
                  simp only [DriftTimeData.ValidChildren] at hl hr
                  simp only [List.flatMap_cons] at ht
                  have hlength : leftHead.preorderTimes.length =
                      rightHead.preorderTimes.length := by
                    rw [leftHead.valid_preorderTimes_length_eq_vertexCount
                        head parentTime hl.1,
                      rightHead.valid_preorderTimes_length_eq_vertexCount
                        head parentTime hr.1]
                  have hparts := List.append_inj ht hlength
                  have hheadEq := DriftTimeData.eq_of_valid_of_preorderTimes_eq
                    head leftHead rightHead parentTime hl.1 hr.1 hparts.1
                  have htailEq := ih leftTail rightTail parentTime hl.2 hr.2 hparts.2
                  subst rightHead
                  subst rightTail
                  rfl
    exact hforest tree.children left.children right.children m hleft.2 hright.2 htimes
  cases left
  cases right
  simp_all [TimeAssignment.Valid]

theorem TimeAssignment.valid_driftPreorderTimes_length
    {J noiseDim m : ℕ} {tree : PayoffTreeData J noiseDim}
    {assignment : TimeAssignment} (hvalid : assignment.Valid m tree) :
    assignment.driftPreorderTimes.length =
      (tree.children.map DriftTreeData.vertexCount).sum := by
  unfold TimeAssignment.driftPreorderTimes
  have hforest : ∀ (trees : List (DriftTreeData J noiseDim))
      (assignments : List DriftTimeData) (parentTime : ℕ),
      DriftTimeData.ValidChildren parentTime trees assignments →
        (assignments.flatMap DriftTimeData.preorderTimes).length =
          (trees.map DriftTreeData.vertexCount).sum := by
    intro trees
    induction trees with
    | nil =>
        intro assignments parentTime hassignments
        cases assignments <;>
          simp [DriftTimeData.ValidChildren] at hassignments ⊢
    | cons head tail ih =>
        intro assignments parentTime hassignments
        cases assignments with
        | nil => simp [DriftTimeData.ValidChildren] at hassignments
        | cons headTime tailTimes =>
            simp only [DriftTimeData.ValidChildren] at hassignments
            simp only [List.flatMap_cons, List.length_append,
              List.map_cons, List.sum_cons]
            rw [headTime.valid_preorderTimes_length_eq_vertexCount
              head parentTime hassignments.1,
              ih tailTimes parentTime hassignments.2]
  exact hforest tree.children assignment.children m hvalid.2

theorem TimeAssignment.valid_driftPreorderTimes_lt_root
    {J noiseDim m : ℕ} {tree : PayoffTreeData J noiseDim}
    {assignment : TimeAssignment} (hvalid : assignment.Valid m tree) :
    ∀ time ∈ assignment.driftPreorderTimes, time < m := by
  unfold TimeAssignment.driftPreorderTimes
  have hforest : ∀ (trees : List (DriftTreeData J noiseDim))
      (assignments : List DriftTimeData) (parentTime : ℕ),
      DriftTimeData.ValidChildren parentTime trees assignments →
        ∀ time ∈ assignments.flatMap DriftTimeData.preorderTimes,
          time < parentTime := by
    intro trees
    induction trees with
    | nil =>
        intro assignments parentTime hassignments
        cases assignments <;>
          simp [DriftTimeData.ValidChildren] at hassignments ⊢
    | cons head tail ih =>
        intro assignments parentTime hassignments time htime
        cases assignments with
        | nil => simp [DriftTimeData.ValidChildren] at hassignments
        | cons headTime tailTimes =>
            simp only [DriftTimeData.ValidChildren] at hassignments
            simp only [List.flatMap_cons, List.mem_append] at htime
            rcases htime with htime | htime
            · exact headTime.valid_preorderTimes_lt_parent
                head parentTime hassignments.1 time htime
            · exact ih tailTimes parentTime hassignments.2 time htime
  exact hforest tree.children assignment.children m hvalid.2

/-- Forget the edge-order constraints and retain the preorder time at each drift vertex. -/
noncomputable def TimeAssignment.independentTimeEncoding
    {J noiseDim m : ℕ} {tree : PayoffTreeData J noiseDim}
    (assignment : TimeAssignment) (hvalid : assignment.Valid m tree) :
    Fin (tree.children.map DriftTreeData.vertexCount).sum → Fin m := fun vertex ↦
  let index : Fin assignment.driftPreorderTimes.length :=
    Fin.cast (TimeAssignment.valid_driftPreorderTimes_length hvalid).symm vertex
  ⟨assignment.driftPreorderTimes.get index,
    TimeAssignment.valid_driftPreorderTimes_lt_root hvalid _
      (List.get_mem _ index)⟩

theorem TimeAssignment.independentTimeEncoding_injective
    {J noiseDim m : ℕ} {tree : PayoffTreeData J noiseDim} :
    Function.Injective (fun assignment : {assignment : TimeAssignment //
        assignment.Valid m tree} ↦
      assignment.1.independentTimeEncoding assignment.2) := by
  intro left right hencoding
  apply Subtype.ext
  apply TimeAssignment.eq_of_valid_of_driftPreorderTimes_eq left.2 right.2
  apply List.ext_get
  · rw [TimeAssignment.valid_driftPreorderTimes_length left.2,
      TimeAssignment.valid_driftPreorderTimes_length right.2]
  · intro i hleft hright
    let vertex : Fin (tree.children.map DriftTreeData.vertexCount).sum :=
      ⟨i, by
        rw [← TimeAssignment.valid_driftPreorderTimes_length left.2]
        exact hleft⟩
    have hvalue := congrArg Fin.val (congrFun hencoding vertex)
    simpa [TimeAssignment.independentTimeEncoding, vertex] using hvalue

/-- At parent time zero there can be no valid drift child. -/
theorem DriftTimeData.validChildren_at_zero_trees_nil {J noiseDim : ℕ}
    {trees : List (DriftTreeData J noiseDim)} {assignments : List DriftTimeData}
    (hvalid : DriftTimeData.ValidChildren 0 trees assignments) : trees = [] := by
  cases trees with
  | nil => rfl
  | cons tree trees =>
      cases assignments with
      | nil => simp [DriftTimeData.ValidChildren] at hvalid
      | cons assignment assignments =>
          simp only [DriftTimeData.ValidChildren] at hvalid
          exact (DriftTimeData.valid_at_zero_impossible hvalid.1).elim

/-- A vertex assigned time zero is necessarily a leaf. -/
theorem DriftTimeData.valid_time_zero_children_nil {J noiseDim : ℕ}
    {parentTime : ℕ} {tree : DriftTreeData J noiseDim} {assignment : DriftTimeData}
    (hvalid : assignment.Valid parentTime tree) (htime : assignment.time = 0) :
    tree.children = [] := by
  cases tree with
  | node direct children =>
      cases assignment with
      | node time assignments =>
          simp only [DriftTreeData.children, DriftTimeData.time,
            DriftTimeData.Valid] at hvalid htime ⊢
          subst time
          exact DriftTimeData.validChildren_at_zero_trees_nil hvalid.2

end

end TimeDependentLattice.Trees
