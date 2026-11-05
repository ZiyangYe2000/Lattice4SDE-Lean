/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.TimeAssignment
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# Complete recursive expansion choices

This file formalizes the finite set `𝔠_{m,u}` introduced in the proof of
Lemma `lem:correspondence`.  Unlike `DriftTreeData`, the children here are indexed by the parts
of a Mathlib `Finpartition`, so they are genuinely unordered.  The later correspondence maps
these choices to the canonical child lists used by the executable tree representation.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open TimeDependentLattice.BrownianBridge

/-- A complete choice in the recursive expansion of a state derivative `Y_(parentTime,support)`.

The `singleton` constructor selects one summand of `eq:partition-first`.  The `higher`
constructor selects a time, a direct set `S`, a partition of `support \ S`, and recursively a
complete choice for every state-derivative block in `eq:correspondence-reindex`. -/
inductive DriftExpansionChoice (J noiseDim : ℕ) :
    ℕ → Finset (Index J noiseDim) → Type where
  | singleton {parentTime : ℕ} (time : ℕ) (j : Index J noiseDim)
      (time_lt : time < parentTime) :
      DriftExpansionChoice J noiseDim parentTime {j}
  | higher {parentTime : ℕ} {support : Finset (Index J noiseDim)}
      (time : ℕ) (time_lt : time < parentTime)
      (direct : Finset (Index J noiseDim)) (direct_subset : direct ⊆ support)
      (partition : Finpartition (support \ direct))
      (local_order : 2 ≤ direct.card + partition.parts.card)
      (children : ∀ block : partition.parts,
        DriftExpansionChoice J noiseDim time block.1) :
      DriftExpansionChoice J noiseDim parentTime support

/-- A complete choice in the expansion of the payoff derivative `∂_u F_m`.

The root selects `E ⊆ u ∩ 𝓔_w`, equivalently a subset of `u` consisting only of endpoint
coordinates, a partition of `u \ E`, and one complete state-derivative expansion for each block.
-/
structure PayoffExpansionChoice (J noiseDim : ℕ)
    (u : Finset (Index J noiseDim)) (m : ℕ) where
  direct : Finset (Index J noiseDim)
  direct_subset : direct ⊆ u
  direct_endpoint : ∀ j ∈ direct, IsEndpoint j
  partition : Finpartition (u \ direct)
  children : ∀ block : partition.parts,
    DriftExpansionChoice J noiseDim m block.1

/-- One local choice in the higher-order state-derivative expansion, before recursively
expanding the derivative carried by each partition block. -/
structure DriftRootChoice (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) where
  direct : Finset (Index J noiseDim)
  direct_subset : direct ⊆ support
  partition : Finpartition (support \ direct)
  local_order : 2 ≤ direct.card + partition.parts.card
  deriving DecidableEq

private abbrev DriftRootChoiceCode (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :=
  Σ direct : {d : Finset (Index J noiseDim) // d ⊆ support},
    {partition : Finpartition (support \ direct.1) //
      2 ≤ direct.1.card + partition.parts.card}

private def DriftRootChoice.equivCode (J noiseDim : ℕ)
    (support : Finset (Index J noiseDim)) :
    DriftRootChoice J noiseDim support ≃
      DriftRootChoiceCode J noiseDim support where
  toFun root := ⟨⟨root.direct, root.direct_subset⟩,
    ⟨root.partition, root.local_order⟩⟩
  invFun code := ⟨code.1.1, code.1.2, code.2.1, code.2.2⟩
  left_inv root := by cases root; rfl
  right_inv code := by rcases code with ⟨⟨direct, hsubset⟩, partition, horder⟩; rfl

noncomputable instance instFintypeDriftRootChoice
    (J noiseDim : ℕ) (support : Finset (Index J noiseDim)) :
    Fintype (DriftRootChoice J noiseDim support) := by
  letI (direct : {d : Finset (Index J noiseDim) // d ⊆ support}) :
      Fintype (Finpartition (support \ direct.1)) := Fintype.ofFinite _
  letI (direct : {d : Finset (Index J noiseDim) // d ⊆ support}) :
      Fintype {partition : Finpartition (support \ direct.1) //
        2 ≤ direct.1.card + partition.parts.card} := Fintype.ofFinite _
  exact Fintype.ofEquiv (DriftRootChoiceCode J noiseDim support)
    (DriftRootChoice.equivCode J noiseDim support).symm

/-- A higher-order root choice, its earlier time, and a complete recursive choice for every
remaining derivative block. -/
def DriftHigherCode (J noiseDim parentTime : ℕ)
    (support : Finset (Index J noiseDim)) :=
  Σ time : Fin parentTime,
    Σ root : DriftRootChoice J noiseDim support,
      ∀ block : root.partition.parts,
        DriftExpansionChoice J noiseDim time.val block.1

def DriftHigherCode.toChoice {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)} :
    DriftHigherCode J noiseDim parentTime support →
      DriftExpansionChoice J noiseDim parentTime support
  | ⟨time, root, children⟩ => .higher time.val time.isLt root.direct
      root.direct_subset root.partition root.local_order children

def DriftExpansionChoice.toHigherCode {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)} (hcard : 2 ≤ support.card) :
    DriftExpansionChoice J noiseDim parentTime support →
      DriftHigherCode J noiseDim parentTime support
  | .singleton time j htime => by simp at hcard
  | .higher time htime direct hsubset partition horder children =>
      ⟨⟨time, htime⟩, ⟨direct, hsubset, partition, horder⟩, children⟩

/-- For support of size at least two, complete drift choices are exactly a higher-order local
choice together with one complete recursive choice for every partition block. -/
noncomputable def DriftExpansionChoice.higherEquiv
    {J noiseDim parentTime : ℕ} {support : Finset (Index J noiseDim)}
    (hcard : 2 ≤ support.card) :
    DriftExpansionChoice J noiseDim parentTime support ≃
      DriftHigherCode J noiseDim parentTime support where
  toFun := DriftExpansionChoice.toHigherCode hcard
  invFun := DriftHigherCode.toChoice
  left_inv choice := by
    cases choice with
    | singleton time j htime => simp at hcard
    | higher time htime direct hsubset partition horder children => rfl
  right_inv code := by
    rcases code with ⟨time, root, children⟩
    rcases root with ⟨direct, hsubset, partition, horder⟩
    rfl

/-- A finite code for the two constructors of a complete drift expansion choice. -/
private noncomputable def DriftChoiceCode (J noiseDim parentTime : ℕ)
    (support : Finset (Index J noiseDim)) :=
  (Σ time : Fin parentTime, {j : Index J noiseDim // support = {j}}) ⊕
    (Σ time : Fin parentTime,
      Σ direct : {d : Finset (Index J noiseDim) // d ⊆ support},
      Σ partition : {p : Finpartition (support \ direct.1) //
        2 ≤ direct.1.card + p.parts.card},
        ∀ block : partition.1.parts,
          DriftExpansionChoice J noiseDim time.val block.1)

private noncomputable def DriftChoiceCode.toChoice
    {J noiseDim parentTime : ℕ} {support : Finset (Index J noiseDim)} :
    DriftChoiceCode J noiseDim parentTime support →
      DriftExpansionChoice J noiseDim parentTime support
  | .inl ⟨time, ⟨j, hsupport⟩⟩ => by
      rw [hsupport]
      exact .singleton time.val j time.isLt
  | .inr ⟨time, ⟨direct, hsubset⟩, ⟨partition, horder⟩, children⟩ =>
      .higher time.val time.isLt direct hsubset partition horder children

private theorem driftChoiceCode_toChoice_surjective
    {J noiseDim parentTime : ℕ} {support : Finset (Index J noiseDim)} :
    Function.Surjective
      (DriftChoiceCode.toChoice : DriftChoiceCode J noiseDim parentTime support →
        DriftExpansionChoice J noiseDim parentTime support) := by
  intro choice
  cases choice with
  | singleton time j htime =>
      exact ⟨.inl ⟨⟨time, htime⟩, ⟨j, rfl⟩⟩, rfl⟩
  | higher time htime direct hsubset partition horder children =>
      exact ⟨.inr ⟨⟨time, htime⟩, ⟨direct, hsubset⟩,
        ⟨partition, horder⟩, children⟩, rfl⟩

private theorem finitePiOfFinite {α : Type*} [Finite α] (β : α → Type*)
    (h : ∀ a, Finite (β a)) : Finite (∀ a, β a) := by
  letI (a : α) : Finite (β a) := h a
  infer_instance

private theorem finiteSigmaOfFinite {α : Type*} [Finite α] (β : α → Type*)
    (h : ∀ a, Finite (β a)) : Finite (Σ a, β a) := by
  letI : Fintype α := Fintype.ofFinite α
  letI (a : α) : Fintype (β a) := @Fintype.ofFinite (β a) (h a)
  exact Finite.of_fintype _

/-- Complete drift expansion choices form a finite family. -/
theorem driftExpansionChoice_finite (J noiseDim : ℕ) :
    ∀ parentTime support, Finite (DriftExpansionChoice J noiseDim parentTime support) := by
  intro parentTime
  induction parentTime using Nat.strong_induction_on with
  | h parentTime ih =>
      intro support
      letI : ∀ (time : Fin parentTime)
          (childSupport : Finset (Index J noiseDim)),
          Finite (DriftExpansionChoice J noiseDim time.val childSupport) :=
        fun time childSupport => ih time.val time.isLt childSupport
      have hleft : Finite
          (Σ time : Fin parentTime,
            {j : Index J noiseDim // support = {j}}) := by
        infer_instance
      have hright : Finite
          (Σ time : Fin parentTime,
            Σ direct : {d : Finset (Index J noiseDim) // d ⊆ support},
            Σ partition : {p : Finpartition (support \ direct.1) //
              2 ≤ direct.1.card + p.parts.card},
              ∀ block : partition.1.parts,
                DriftExpansionChoice J noiseDim time.val block.1) := by
        apply finiteSigmaOfFinite
        intro time
        apply finiteSigmaOfFinite
        intro direct
        apply finiteSigmaOfFinite
        intro partition
        apply finitePiOfFinite
        intro block
        exact ih time.val time.isLt block.1
      letI : Fintype
          (Σ time : Fin parentTime,
            {j : Index J noiseDim // support = {j}}) :=
        @Fintype.ofFinite _ hleft
      letI : Fintype
          (Σ time : Fin parentTime,
            Σ direct : {d : Finset (Index J noiseDim) // d ⊆ support},
            Σ partition : {p : Finpartition (support \ direct.1) //
              2 ≤ direct.1.card + p.parts.card},
              ∀ block : partition.1.parts,
                DriftExpansionChoice J noiseDim time.val block.1) :=
        @Fintype.ofFinite _ hright
      letI : Finite (DriftChoiceCode J noiseDim parentTime support) := by
        unfold DriftChoiceCode
        exact Finite.of_fintype _
      exact Finite.of_surjective DriftChoiceCode.toChoice
        driftChoiceCode_toChoice_surjective

noncomputable instance instFiniteDriftExpansionChoice
    (J noiseDim parentTime : ℕ) (support : Finset (Index J noiseDim)) :
    Finite (DriftExpansionChoice J noiseDim parentTime support) :=
  driftExpansionChoice_finite J noiseDim parentTime support

noncomputable instance instFintypeDriftExpansionChoice
    (J noiseDim parentTime : ℕ) (support : Finset (Index J noiseDim)) :
    Fintype (DriftExpansionChoice J noiseDim parentTime support) :=
  Fintype.ofFinite _

noncomputable instance instFintypeDriftChildChoices
    (J noiseDim parentTime : ℕ) (support : Finset (Index J noiseDim))
    (time : Fin parentTime) (root : DriftRootChoice J noiseDim support) :
    Fintype (∀ block : root.partition.parts,
      DriftExpansionChoice J noiseDim time.val block.1) :=
  Pi.instFintype

noncomputable instance instFintypeDriftHigherCode
    (J noiseDim parentTime : ℕ) (support : Finset (Index J noiseDim)) :
    Fintype (DriftHigherCode J noiseDim parentTime support) := by
  unfold DriftHigherCode
  infer_instance

/-- A finite code for complete payoff expansion choices. -/
private noncomputable def PayoffChoiceCode (J noiseDim : ℕ)
    (u : Finset (Index J noiseDim)) (m : ℕ) :=
  Σ direct : {d : Finset (Index J noiseDim) // d ⊆ u ∧ ∀ j ∈ d, IsEndpoint j},
    Σ partition : Finpartition (u \ direct.1),
      ∀ block : partition.parts,
        DriftExpansionChoice J noiseDim m block.1

private noncomputable def PayoffChoiceCode.toChoice
    {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)} :
    PayoffChoiceCode J noiseDim u m → PayoffExpansionChoice J noiseDim u m
  | ⟨⟨direct, hsubset, hendpoint⟩, partition, children⟩ =>
      ⟨direct, hsubset, hendpoint, partition, children⟩

private theorem payoffChoiceCode_toChoice_surjective
    {J noiseDim m : ℕ} {u : Finset (Index J noiseDim)} :
    Function.Surjective
      (PayoffChoiceCode.toChoice : PayoffChoiceCode J noiseDim u m →
        PayoffExpansionChoice J noiseDim u m) := by
  rintro ⟨direct, hsubset, hendpoint, partition, children⟩
  exact ⟨⟨⟨direct, hsubset, hendpoint⟩, partition, children⟩, rfl⟩

noncomputable instance instFinitePayoffExpansionChoice
    (J noiseDim m : ℕ) (u : Finset (Index J noiseDim)) :
    Finite (PayoffExpansionChoice J noiseDim u m) := by
  letI : Finite (PayoffChoiceCode J noiseDim u m) := by
    unfold PayoffChoiceCode
    apply finiteSigmaOfFinite
    intro direct
    apply finiteSigmaOfFinite
    intro partition
    apply finitePiOfFinite
    intro block
    infer_instance
  exact Finite.of_surjective PayoffChoiceCode.toChoice
    payoffChoiceCode_toChoice_surjective

noncomputable instance instFintypePayoffExpansionChoice
    (J noiseDim m : ℕ) (u : Finset (Index J noiseDim)) :
    Fintype (PayoffExpansionChoice J noiseDim u m) :=
  Fintype.ofFinite _

namespace DriftExpansionChoice

/-- The selected Euler time at the root of a recursive state-derivative choice. -/
def time {J noiseDim parentTime : ℕ} {support : Finset (Index J noiseDim)} :
    DriftExpansionChoice J noiseDim parentTime support → ℕ
  | .singleton time _ _ => time
  | .higher time _ _ _ _ _ _ => time

/-- Every selected drift time is strictly below its parent time. -/
theorem time_lt_parent {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    choice.time < parentTime := by
  cases choice with
  | singleton time j htime => exact htime
  | higher time htime direct hsubset partition horder children => exact htime

/-- There is no recursive state-derivative expansion below time zero. -/
theorem not_at_parent_zero {J noiseDim : ℕ}
    {support : Finset (Index J noiseDim)} :
    IsEmpty (DriftExpansionChoice J noiseDim 0 support) :=
  ⟨fun choice => (Nat.not_lt_zero choice.time) choice.time_lt_parent⟩

private theorem singleton_cases_general {J noiseDim parentTime : ℕ}
    {support : Finset (Index J noiseDim)}
    (choice : DriftExpansionChoice J noiseDim parentTime support) :
    ∀ (j : Index J noiseDim), support = {j} →
      ∃ (time : ℕ) (htime : time < parentTime),
        HEq choice
          (DriftExpansionChoice.singleton (J := J) (noiseDim := noiseDim)
            time j htime) := by
  induction choice with
  | singleton time k htime =>
      intro j hsupport
      have hk : k = j := Finset.singleton_inj.mp hsupport
      subst j
      exact ⟨time, htime, HEq.rfl⟩
  | higher time htime direct hsubset partition horder children ih =>
      intro j hsupport
      have hparts := partition.card_parts_le_card
      have hparts' : partition.parts.card ≤ ({j} \ direct).card := by
        simpa [hsupport] using hparts
      have hcard := Finset.card_sdiff_add_card_eq_card hsubset
      have hcard' : ({j} \ direct).card + direct.card = 1 := by
        simpa [hsupport] using hcard
      omega

/-- A complete expansion choice on a singleton support is necessarily a singleton choice. -/
theorem singleton_cases {J noiseDim parentTime : ℕ}
    (j : Index J noiseDim)
    (choice : DriftExpansionChoice J noiseDim parentTime {j}) :
    ∃ (time : ℕ) (htime : time < parentTime),
      choice = DriftExpansionChoice.singleton time j htime := by
  obtain ⟨time, htime, hchoice⟩ := singleton_cases_general choice j rfl
  exact ⟨time, htime, eq_of_heq hchoice⟩

/-- Singleton-support expansion choices are exactly the earlier Euler times. -/
noncomputable def singletonEquivFin {J noiseDim parentTime : ℕ}
    (j : Index J noiseDim) :
    DriftExpansionChoice J noiseDim parentTime {j} ≃ Fin parentTime where
  toFun choice := ⟨choice.time, choice.time_lt_parent⟩
  invFun time := .singleton time.val j time.isLt
  left_inv choice := by
    obtain ⟨time, htime, rfl⟩ := singleton_cases j choice
    rfl
  right_inv time := by
    rfl

end DriftExpansionChoice

namespace PayoffExpansionChoice

/-- The complete expansion choice corresponding to the root-only payoff term. -/
def rootOnly {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    PayoffExpansionChoice J noiseDim u m := by
  let rootPartition : Finpartition (u \ u) :=
    (Finpartition.empty (Finset (Index J noiseDim))).copy (by simp)
  refine
    { direct := u
      direct_subset := Finset.Subset.rfl
      direct_endpoint := hendpoint
      partition := rootPartition
      children := ?_ }
  intro block
  have hparts : rootPartition.parts = ∅ := by
    simp [rootPartition]
  have hempty : False := by
    simpa [hparts] using block.property
  exact hempty.elim

@[simp]
theorem rootOnly_direct {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    (rootOnly u hendpoint m).direct = u :=
  by simp [rootOnly]

@[simp]
theorem rootOnly_partition_parts {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim))
    (hendpoint : ∀ j ∈ u, IsEndpoint j) (m : ℕ) :
    (rootOnly u hendpoint m).partition.parts = ∅ := by
  simp [rootOnly]

end PayoffExpansionChoice

end

end TimeDependentLattice.Trees
