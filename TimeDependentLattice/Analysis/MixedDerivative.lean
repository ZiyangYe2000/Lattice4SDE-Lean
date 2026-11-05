/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.GroupTheory.Perm.Sign
import TimeDependentLattice.Analysis.Finpartition
import TimeDependentLattice.BrownianBridge.Path

/-!
# Mixed coordinate derivatives and finite partitions

The paper differentiates once in every coordinate belonging to a finite set `u`.  Mathlib's
`iteratedFDeriv` takes an ordered family of directions, so this file evaluates it on the standard
basis directions obtained from the canonical finite enumeration of `u`.

Mathlib already proves the higher-order chain rule using `OrderedFinpartition`.  We expose its
individual summands in the notation needed for the paper.  The order only supplies a canonical
enumeration of the blocks; each block also has an unordered `Finset` view for the later tree API.
-/

namespace TimeDependentLattice.Analysis

noncomputable section

open scoped BigOperators ContDiff
open TimeDependentLattice.BrownianBridge

/-- The canonical list of standard basis directions associated with a coordinate set. -/
def coordinateDirections {J noiseDim : ℕ} (u : Finset (Index J noiseDim)) :
    Fin u.card → Input J noiseDim :=
  fun k ↦ inputBasis (u.equivFin.symm k).val

/-- The mixed derivative `∂_u f(z)`, with every coordinate of `u` used exactly once. -/
def mixedDerivative {J noiseDim : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Input J noiseDim → F) (u : Finset (Index J noiseDim)) (z : Input J noiseDim) : F :=
  iteratedFDeriv ℝ u.card f z (coordinateDirections u)

/-- The first derivative in one coordinate direction.  Keeping this interface separate avoids
dependent casts between `Fin ({j}.card)` and `Fin 1` in first-order recursion formulas. -/
def coordinateDerivative {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Input J noiseDim → F)
    (j : Index J noiseDim) (z : Input J noiseDim) : F :=
  fderiv ℝ f z (inputBasis j)

private theorem vecDecomposeTwo {E : Type*} {n : ℕ} (v : Fin (n + 2) → E) :
    v = Fin.cons (v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail v))) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · rfl

private theorem vecSwapZeroOne {E : Type*} {n : ℕ} (v : Fin (n + 2) → E) :
    v ∘ Equiv.swap (0 : Fin (n + 2)) 1 =
      Fin.cons (v 1) (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k.succ)
      (Fin.succ_succ_ne_one k)]
    rfl

private theorem vecSwapSucc {E : Type*} {n : ℕ} (v : Fin (n + 2) → E)
    (i j : Fin (n + 1)) :
    v ∘ Equiv.swap i.succ j.succ =
      Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap i j) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [Function.comp_apply, Fin.cons_zero]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
      (Fin.succ_ne_zero j).symm]
  · change v ((Equiv.swap i.succ j.succ) k.succ) =
      v ((Equiv.swap i j k).succ)
    congr 1
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all

private theorem iteratedFDeriv_front_swap_of_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (x : E) (n : ℕ)
    (a b : E) (rest : Fin n → E) :
    iteratedFDeriv ℝ ((n + 1) + 1) f x (Fin.cons a (Fin.cons b rest)) =
      iteratedFDeriv ℝ ((n + 1) + 1) f x (Fin.cons b (Fin.cons a rest)) := by
  let h : E → F := fun y => iteratedFDeriv ℝ n f y rest
  have hbase : ContDiff ℝ 2 h := by
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F rest).contDiff.comp
      (hf.iteratedFDeriv_right (m := 2) (i := n) (by simp))
  have hsymm : IsSymmSndFDerivAt ℝ h x :=
    hbase.contDiffAt.isSymmSndFDerivAt (by simp)
  have hleft :
      iteratedFDeriv ℝ ((n + 1) + 1) f x (Fin.cons a (Fin.cons b rest)) =
        iteratedFDeriv ℝ 2 h x ![a, b] := by
    have hDn1 : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
      (hf.iteratedFDeriv_right (m := 1) (i := n + 1) (by simp)).differentiable
        (by simp) |>.differentiableAt
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hDn1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    have hfun :
        (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.cons b rest)) =
          fun y => fderiv ℝ h y b := by
      funext y
      have hDn : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
        (hf.iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiable
          (by simp) |>.differentiableAt
      rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hDn]
      simp [h]
    rw [hfun]
    rw [iteratedFDeriv_two_apply]
    have heq : (2 : ℕ∞ω) = 1 + 1 := by norm_num
    rw [heq] at hbase
    have hfd : ContDiff ℝ 1 (fderiv ℝ h) :=
      (contDiff_succ_iff_fderiv.mp hbase).2.2
    have hc : DifferentiableAt ℝ (fderiv ℝ h) x :=
      (hfd.differentiable (by simp)).differentiableAt
    have hb : DifferentiableAt ℝ (fun _ : E => b) x := differentiableAt_const b
    rw [fderiv_clm_apply hc hb]
    simp
  have hright :
      iteratedFDeriv ℝ ((n + 1) + 1) f x (Fin.cons b (Fin.cons a rest)) =
        iteratedFDeriv ℝ 2 h x ![b, a] := by
    have hDn1 : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
      (hf.iteratedFDeriv_right (m := 1) (i := n + 1) (by simp)).differentiable
        (by simp) |>.differentiableAt
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hDn1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    have hfun :
        (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.cons a rest)) =
          fun y => fderiv ℝ h y a := by
      funext y
      have hDn : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
        (hf.iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiable
          (by simp) |>.differentiableAt
      rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hDn]
      simp [h]
    rw [hfun]
    rw [iteratedFDeriv_two_apply]
    have heq : (2 : ℕ∞ω) = 1 + 1 := by norm_num
    rw [heq] at hbase
    have hfd : ContDiff ℝ 1 (fderiv ℝ h) :=
      (contDiff_succ_iff_fderiv.mp hbase).2.2
    have hc : DifferentiableAt ℝ (fderiv ℝ h) x :=
      (hfd.differentiable (by simp)).differentiableAt
    have ha : DifferentiableAt ℝ (fun _ : E => a) x := differentiableAt_const a
    rw [fderiv_clm_apply hc ha]
    simp
  rw [hleft, hright]
  exact hsymm.iteratedFDeriv_cons

private theorem iteratedFDeriv_adjacent_swap_of_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (x : E) (n : ℕ)
    (i : Fin (n + 1)) (directions : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f x
        (directions ∘ Equiv.swap i.castSucc i.succ) =
      iteratedFDeriv ℝ (n + 2) f x directions := by
  induction n generalizing x with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hzero : directions ∘ Equiv.swap (Fin.castSucc 0) (Fin.succ 0) =
          Fin.cons (directions 1)
            (Fin.cons (directions 0) (Fin.tail (Fin.tail directions))) := by
        convert vecSwapZeroOne directions using 1 <;> simp
      rw [hzero, vecDecomposeTwo directions]
      exact (iteratedFDeriv_front_swap_of_contDiff f hf x 0 (directions 0) (directions 1)
        (Fin.tail (Fin.tail directions))).symm
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · have hzero : directions ∘ Equiv.swap (Fin.castSucc 0) (Fin.succ 0) =
            Fin.cons (directions 1)
              (Fin.cons (directions 0) (Fin.tail (Fin.tail directions))) := by
          convert vecSwapZeroOne directions using 1 <;> simp
        rw [hzero, vecDecomposeTwo directions]
        exact (iteratedFDeriv_front_swap_of_contDiff f hf x n.succ (directions 0) (directions 1)
          (Fin.tail (Fin.tail directions))).symm
      · have hleft :
            directions ∘ Equiv.swap j.succ.castSucc j.succ.succ =
              Fin.cons (directions 0)
                (Fin.tail directions ∘ Equiv.swap j.castSucc j.succ) := by
          exact vecSwapSucc directions j.castSucc j.succ
        rw [hleft]
        have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 2) f) x :=
          (hf.iteratedFDeriv_right (m := 1) (i := n + 2) (by simp)).differentiable
            (by simp) |>.differentiableAt
        rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' (n := n + 2) hdiff]
        rw [show directions = Fin.cons (directions 0) (Fin.tail directions) by
          rw [Fin.cons_self_tail]]
        rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' (n := n + 2) hdiff]
        simp only [Fin.cons_zero, Fin.tail_cons]
        have hfun :
            (fun y => iteratedFDeriv ℝ (n + 2) f y
              (Fin.tail directions ∘ Equiv.swap j.castSucc j.succ)) =
              fun y => iteratedFDeriv ℝ (n + 2) f y (Fin.tail directions) := by
          funext y
          exact ih y j (Fin.tail directions)
        rw [hfun]

theorem iteratedFDeriv_permute_directions_of_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (x : E) (n : ℕ)
    (directions : Fin n → E) (permutation : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (directions ∘ permutation) =
      iteratedFDeriv ℝ n f x directions := by
  cases n with
  | zero =>
      have hp : permutation = 1 := Subsingleton.elim _ _
      subst permutation
      simp
  | succ n =>
      cases n with
      | zero =>
          have hp : permutation = 1 := by
            ext i
            omega
          subst permutation
          simp
      | succ n =>
          let stabilizer : Submonoid (Equiv.Perm (Fin (n + 2))) :=
            { carrier := {p | ∀ d : Fin (n + 2) → E,
                iteratedFDeriv ℝ (n + 2) f x (d ∘ p) =
                  iteratedFDeriv ℝ (n + 2) f x d}
              one_mem' := by intro d; simp
              mul_mem' := by
                intro p q hp hq d
                rw [show d ∘ (p * q) = (d ∘ p) ∘ q by rfl]
                exact (hq (d ∘ p)).trans (hp d) }
          have hgen : Set.range (fun i : Fin (n + 1) =>
              Equiv.swap i.castSucc i.succ) ⊆ stabilizer := by
            rintro p ⟨i, rfl⟩
            exact iteratedFDeriv_adjacent_swap_of_contDiff f hf x n i
          have hclosure : Submonoid.closure (Set.range (fun i : Fin (n + 1) =>
              Equiv.swap i.castSucc i.succ)) ≤ stabilizer :=
            Submonoid.closure_le.mpr hgen
          apply hclosure
          rw [Equiv.Perm.mclosure_swap_castSucc_succ (n + 1)]
          trivial

/-- Reindexing by an equivalence does not change the directions of an iterated derivative of a
smooth function.  The equivalence also identifies the two finite derivative orders. -/
theorem iteratedFDeriv_comp_equiv_directions_of_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) {n m : ℕ} (directions : Fin m → E)
    (reindex : Fin n ≃ Fin m) (hf : ContDiff ℝ ∞ f) :
    iteratedFDeriv ℝ n f x (directions ∘ reindex) =
      iteratedFDeriv ℝ m f x directions := by
  have hnm : n = m := by
    simpa using Fintype.card_congr reindex
  subst m
  exact iteratedFDeriv_permute_directions_of_contDiff f hf x n directions reindex

/-- An analytic function's iterated derivative is unchanged when its input directions are
permuted. -/
theorem iteratedFDeriv_permute_directions_of_analytic {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) {n : ℕ} (directions : Fin n → E)
    (permutation : Equiv.Perm (Fin n)) (hf : ContDiffAt ℝ ω f x) :
    iteratedFDeriv ℝ n f x (directions ∘ permutation) =
      iteratedFDeriv ℝ n f x directions :=
  hf.iteratedFDeriv_comp_perm directions permutation

/-- Reindexing the directions by an equivalence does not change an analytic iterated derivative.
The equivalence itself supplies the equality of the two finite derivative orders. -/
theorem iteratedFDeriv_comp_equiv_directions_of_analytic {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) {n m : ℕ} (directions : Fin m → E)
    (reindex : Fin n ≃ Fin m) (hf : ContDiffAt ℝ ω f x) :
    iteratedFDeriv ℝ n f x (directions ∘ reindex) =
      iteratedFDeriv ℝ m f x directions := by
  have hnm : n = m := by
    simpa using Fintype.card_congr reindex
  subst m
  exact iteratedFDeriv_permute_directions_of_analytic f x directions reindex hf

/-- An iterated Fréchet derivative whose order is propositionally equal to one is the ordinary
Fréchet derivative applied to its sole direction. -/
theorem iteratedFDeriv_eq_fderiv_of_eq_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) {n : ℕ} (hn : n = 1) (x : E) (directions : Fin n → E) :
    iteratedFDeriv ℝ n f x directions =
      fderiv ℝ f x (directions (Fin.cast hn.symm 0)) := by
  subst n
  simp [iteratedFDeriv_one_apply]

/-- A mixed derivative on a singleton coordinate set is the corresponding coordinate
derivative. -/
@[simp]
theorem mixedDerivative_singleton {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Input J noiseDim → F) (j : Index J noiseDim) (z : Input J noiseDim) :
    mixedDerivative f {j} z = coordinateDerivative f j z := by
  unfold mixedDerivative coordinateDerivative
  rw [iteratedFDeriv_eq_fderiv_of_eq_one f (by simp)]
  congr 1
  exact congrArg inputBasis (Finset.mem_singleton.mp
    (({j} : Finset (Index J noiseDim)).equivFin.symm
      (Fin.cast (by simp) 0)).property)

/-- A continuous linear map has no derivatives of order two or higher.  This function-level
statement avoids dependent casts when the order also determines the type of the directions. -/
theorem iteratedFDeriv_clm_add_two {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (k : ℕ) :
    iteratedFDeriv ℝ (k + 2) (fun x : E ↦ L x) = 0 := by
  induction k with
  | zero =>
      have hfirst :
          iteratedFDeriv ℝ 1 (fun x : E ↦ L x) =
            Function.const E (iteratedFDeriv ℝ 1 (fun x : E ↦ L x) 0) := by
        funext x
        ext v
        simp [iteratedFDeriv_one_apply]
      rw [show 0 + 2 = 1 + 1 by omega, iteratedFDeriv_succ_eq_comp_left, hfirst]
      funext x
      simp only [Function.comp_apply, fderiv_const]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 ↦ E) F).symm.map_zero
  | succ k ih =>
      rw [show k.succ + 2 = (k + 2) + 1 by omega,
        iteratedFDeriv_succ_eq_comp_left, ih]
      funext x
      simp only [Function.comp_apply, fderiv_zero]
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin ((k + 2) + 1) ↦ E) F).symm.map_zero

/-- Order-independent form of `iteratedFDeriv_clm_add_two`. -/
theorem iteratedFDeriv_clm_eq_zero_of_two_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {n : ℕ} (hn : 2 ≤ n) :
    iteratedFDeriv ℝ n (fun x : E ↦ L x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 k]
  exact iteratedFDeriv_clm_add_two L k

/-- The first iterated derivative of a continuous linear map is evaluation of that map.  The
explicit equality `n = 1` packages the dependent cast on its direction index. -/
theorem iteratedFDeriv_clm_eq_of_eq_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {n : ℕ} (hn : n = 1) (z : E) (m : Fin n → E) :
    iteratedFDeriv ℝ n (fun x ↦ L x) z m = L (m (Fin.cast hn.symm 0)) := by
  subst n
  simp [iteratedFDeriv_one_apply]

/-- Every mixed coordinate derivative of order at least two of a continuous linear map vanishes. -/
theorem mixedDerivative_clm_eq_zero {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Input J noiseDim →L[ℝ] F) (u : Finset (Index J noiseDim))
    (hu : 2 ≤ u.card) (z : Input J noiseDim) :
    mixedDerivative (fun x ↦ L x) u z = 0 := by
  unfold mixedDerivative
  rw [iteratedFDeriv_clm_eq_zero_of_two_le L hu]
  rfl

/-- Mixed derivatives distribute over pointwise addition at points where both summands have the
required differentiability. -/
theorem mixedDerivative_add {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (z : Input J noiseDim) (hf : ContDiffAt ℝ u.card f z)
    (hg : ContDiffAt ℝ u.card g z) :
    mixedDerivative (fun x ↦ f x + g x) u z =
      mixedDerivative f u z + mixedDerivative g u z := by
  unfold mixedDerivative
  change (iteratedFDeriv ℝ u.card (f + g) z) (coordinateDirections u) = _
  rw [iteratedFDeriv_add_apply hf hg]
  rfl

/-- A constant scalar factors out of a mixed derivative. -/
theorem mixedDerivative_const_smul {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (z : Input J noiseDim) (hf : ContDiffAt ℝ u.card f z) :
    mixedDerivative (fun x ↦ a • f x) u z = a • mixedDerivative f u z := by
  unfold mixedDerivative
  rw [iteratedFDeriv_const_smul_apply' hf]
  rfl

@[simp]
theorem mixedDerivative_empty {J noiseDim : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Input J noiseDim → F) (z : Input J noiseDim) :
    mixedDerivative f ∅ z = f z := by
  rfl

/-- A paper-style unordered partition of a coordinate subset. -/
abbrev CoordinatePartition {J noiseDim : ℕ} (u : Finset (Index J noiseDim)) :=
  Finpartition u

/-- The coordinate set represented by one block of Mathlib's ordered partition. -/
def partitionBlock {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) : Finset (Index J noiseDim) :=
  Finset.univ.image fun k : Fin (c.partSize i) ↦ (u.equivFin.symm (c.emb i k)).val

/-- Mathlib's ordered partition, transported from `Fin u.card` to the paper's coordinate set
`u` and with the auxiliary order forgotten. -/
noncomputable def orderedFinpartitionToFinpartition {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card) :
    Finpartition u :=
  rankToFinpartition u (orderedFinpartitionAsFinpartition c)

/-- The canonical Mathlib partition representation is equivalent to the paper's unordered
coordinate partitions. -/
noncomputable def orderedFinpartitionEquivCoordinateFinpartition {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) :
    OrderedFinpartition u.card ≃ CoordinatePartition u :=
  (orderedFinpartitionEquivFinpartition u.card).trans (finpartitionRankEquiv u).symm

@[simp]
theorem orderedFinpartitionEquivCoordinateFinpartition_apply {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card) :
    orderedFinpartitionEquivCoordinateFinpartition u c =
      orderedFinpartitionToFinpartition u c :=
  rfl

@[simp]
theorem orderedFinpartitionToFinpartition_parts {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card) :
    (orderedFinpartitionToFinpartition u c).parts =
      Finset.univ.image (partitionBlock u c) := by
  rw [orderedFinpartitionToFinpartition, rankToFinpartition_parts]
  rw [orderedFinpartitionAsFinpartition_parts]
  ext block
  simp [partitionBlock, unrankFinsetBlock, orderedFinpartitionBlock,
    Finset.image_image, Function.comp_def]

theorem partitionBlock_subset {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) : partitionBlock u c i ⊆ u := by
  intro j hj
  rw [partitionBlock, Finset.mem_image] at hj
  obtain ⟨k, _, rfl⟩ := hj
  exact (u.equivFin.symm (c.emb i k)).property

theorem partitionBlock_nonempty {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) : (partitionBlock u c i).Nonempty := by
  let k : Fin (c.partSize i) := ⟨0, c.partSize_pos i⟩
  refine ⟨(u.equivFin.symm (c.emb i k)).val, ?_⟩
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- Distinct indices of an ordered partition give distinct coordinate blocks. -/
theorem partitionBlock_injective {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card) :
    Function.Injective (partitionBlock u c) := by
  intro left right heq
  let k : Fin (c.partSize left) := ⟨0, c.partSize_pos left⟩
  have hk : (u.equivFin.symm (c.emb left k)).val ∈ partitionBlock u c left :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  rw [heq, partitionBlock, Finset.mem_image] at hk
  obtain ⟨l, -, hl⟩ := hk
  have hemb : c.emb left k = c.emb right l := by
    apply u.equivFin.symm.injective
    exact Subtype.ext hl.symm
  have hsigma : (⟨left, k⟩ : Σ i, Fin (c.partSize i)) = ⟨right, l⟩ :=
    c.emb_injective hemb
  exact congrArg Sigma.fst hsigma

/-- Positions in a Mathlib ordered partition are equivalent to the blocks of the corresponding
paper partition. -/
noncomputable def partitionBlockIndexEquivParts {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card) :
    Fin c.length ≃ (orderedFinpartitionToFinpartition u c).parts :=
  Equiv.ofBijective
    (fun i ↦ ⟨partitionBlock u c i, by
      rw [orderedFinpartitionToFinpartition_parts]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun left right heq ↦ partitionBlock_injective u c
        (congrArg Subtype.val heq),
      fun block ↦ by
        have hblock : block.1 ∈ Finset.univ.image (partitionBlock u c) := by
          simpa only [orderedFinpartitionToFinpartition_parts] using block.2
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hblock
        refine ⟨i, Subtype.ext ?_⟩
        exact hi⟩

@[simp]
theorem partitionBlockIndexEquivParts_apply {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) :
    (partitionBlockIndexEquivParts u c i).1 = partitionBlock u c i :=
  rfl

/-- Forgetting the auxiliary order preserves the number of partition blocks. -/
theorem orderedFinpartitionToFinpartition_card {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card) :
    (orderedFinpartitionToFinpartition u c).parts.card = c.length := by
  rw [orderedFinpartitionToFinpartition_parts]
  rw [Finset.card_image_of_injective _ (partitionBlock_injective u c)]
  simp

/-- The unordered coordinate block and its ordered representative have the same size. -/
theorem partitionBlock_card {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) :
    (partitionBlock u c i).card = c.partSize i := by
  unfold partitionBlock
  have hinj : Function.Injective
      (fun k : Fin (c.partSize i) ↦ (u.equivFin.symm (c.emb i k)).val) :=
    Subtype.val_injective.comp
      (u.equivFin.symm.injective.comp (c.emb_strictMono i).injective)
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- The ordered coordinates in one partition block are in bijection with the corresponding
unordered coordinate subset. -/
def partitionBlockEquiv {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) :
    Fin (c.partSize i) ≃ ↥(partitionBlock u c i) :=
  Equiv.ofBijective
    (fun k ↦ ⟨(u.equivFin.symm (c.emb i k)).val,
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)
    ⟨by
      intro left right heq
      apply (c.emb_strictMono i).injective
      apply u.equivFin.symm.injective
      apply Subtype.ext
      exact congrArg
        (fun x : ↥(partitionBlock u c i) ↦ x.val) heq,
    by
      intro j
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp j.property
      refine ⟨k, ?_⟩
      exact Subtype.ext hk⟩

/-- The canonical enumeration of an unordered block differs from its ordered-partition
enumeration only by this explicit reindexing equivalence. -/
def partitionBlockIndexEquiv {J noiseDim : ℕ}
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (i : Fin c.length) : Fin (c.partSize i) ≃ Fin (partitionBlock u c i).card :=
  (partitionBlockEquiv u c i).trans (partitionBlock u c i).equivFin

/-- The standard basis directions belonging to one partition block. -/
def partitionDirections {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) :
    Fin (c.partSize i) → Input J noiseDim :=
  fun k ↦ inputBasis (u.equivFin.symm (c.emb i k)).val

theorem coordinateDirections_partitionBlock_comp_indexEquiv
    {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) :
    coordinateDirections (partitionBlock u c i) ∘ partitionBlockIndexEquiv u c i =
      partitionDirections u c i := by
  funext k
  simp only [Function.comp_apply, coordinateDirections, partitionDirections,
    partitionBlockIndexEquiv, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  rfl

/-- The derivative of a function along the directions in one canonical partition block. -/
def partitionDerivative {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) (z : Input J noiseDim) : F :=
  iteratedFDeriv ℝ (c.partSize i) f z (partitionDirections u c i)

/-- For a smooth function, the derivative along an ordered partition block equals the mixed
derivative indexed by the corresponding unordered coordinate block. -/
theorem partitionDerivative_eq_mixedDerivative_partitionBlock
    {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) (z : Input J noiseDim)
    (hf : ContDiff ℝ ∞ f) :
    partitionDerivative f u c i z =
      mixedDerivative f (partitionBlock u c i) z := by
  unfold partitionDerivative mixedDerivative
  rw [← coordinateDirections_partitionBlock_comp_indexEquiv u c i]
  exact iteratedFDeriv_comp_equiv_directions_of_contDiff f z
    (coordinateDirections (partitionBlock u c i)) (partitionBlockIndexEquiv u c i) hf

/-- A derivative along one ordered partition block is the mixed derivative indexed by the
corresponding unordered coordinate block. -/
theorem partitionDerivative_eq_mixedDerivative_partitionBlock_of_analytic
    {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) (z : Input J noiseDim)
    (hf : ContDiffAt ℝ ω f z) :
    partitionDerivative f u c i z =
      mixedDerivative f (partitionBlock u c i) z := by
  unfold partitionDerivative mixedDerivative
  rw [← coordinateDirections_partitionBlock_comp_indexEquiv u c i]
  exact iteratedFDeriv_comp_equiv_directions_of_analytic f z
    (coordinateDirections (partitionBlock u c i)) (partitionBlockIndexEquiv u c i) hf

/-- A partition-block derivative distributes over pointwise addition. -/
theorem partitionDerivative_add {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) (z : Input J noiseDim)
    (hf : ContDiffAt ℝ (c.partSize i) f z)
    (hg : ContDiffAt ℝ (c.partSize i) g z) :
    partitionDerivative (fun x ↦ f x + g x) u c i z =
      partitionDerivative f u c i z + partitionDerivative g u c i z := by
  unfold partitionDerivative
  change (iteratedFDeriv ℝ (c.partSize i) (f + g) z) (partitionDirections u c i) = _
  rw [iteratedFDeriv_add_apply hf hg]
  rfl

/-- A partition-block derivative of a continuous linear map vanishes for blocks of size at least
two. -/
theorem partitionDerivative_clm_eq_zero {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Input J noiseDim →L[ℝ] F) (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length)
    (hi : 2 ≤ c.partSize i) (z : Input J noiseDim) :
    partitionDerivative (fun x ↦ L x) u c i z = 0 := by
  unfold partitionDerivative
  rw [iteratedFDeriv_clm_eq_zero_of_two_le L hi]
  rfl

/-- A singleton partition-block derivative of a continuous linear map is evaluation in its sole
direction. -/
theorem partitionDerivative_clm_eq_of_partSize_eq_one
    {J noiseDim : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Input J noiseDim →L[ℝ] F) (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length)
    (hi : c.partSize i = 1) (z : Input J noiseDim) :
    partitionDerivative (fun x ↦ L x) u c i z =
      L (partitionDirections u c i (Fin.cast hi.symm 0)) := by
  unfold partitionDerivative
  exact iteratedFDeriv_clm_eq_of_eq_one L hi z (partitionDirections u c i)

/-- The unique coordinate carried by a singleton ordered partition block. -/
def partitionCoordinate {J noiseDim : ℕ} (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (i : Fin c.length) (hi : c.partSize i = 1) :
    Index J noiseDim :=
  (u.equivFin.symm (c.emb i (Fin.cast hi.symm 0))).val

/-- One set-partition summand in the higher-order chain rule. -/
def partitionChainTerm {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (c : OrderedFinpartition u.card) (z : Input J noiseDim) : G :=
  iteratedFDeriv ℝ c.length g (f z) fun i ↦
    partitionDerivative f u c i z

/-- In a smooth chain-rule summand, every ordered block derivative can be written as the mixed
derivative indexed by its unordered coordinate block. -/
theorem partitionChainTerm_eq_mixedDerivative_blocks
    {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F)
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (z : Input J noiseDim) (hf : ContDiff ℝ ∞ f) :
    partitionChainTerm g f u c z =
      iteratedFDeriv ℝ c.length g (f z) fun i ↦
        mixedDerivative f (partitionBlock u c i) z := by
  unfold partitionChainTerm
  congr 1
  funext i
  exact partitionDerivative_eq_mixedDerivative_partitionBlock f u c i z hf

/-- In a chain-rule summand, every ordered block derivative can be replaced by the mixed
derivative indexed by its unordered coordinate block. -/
theorem partitionChainTerm_eq_mixedDerivative_blocks_of_analytic
    {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F)
    (u : Finset (Index J noiseDim)) (c : OrderedFinpartition u.card)
    (z : Input J noiseDim) (hf : ContDiffAt ℝ ω f z) :
    partitionChainTerm g f u c z =
      iteratedFDeriv ℝ c.length g (f z) fun i ↦
        mixedDerivative f (partitionBlock u c i) z := by
  unfold partitionChainTerm
  congr 1
  funext i
  exact partitionDerivative_eq_mixedDerivative_partitionBlock_of_analytic f u c i z hf

/-- A chain-rule term indexed by the paper's unordered coordinate partition. -/
def finpartitionChainTerm {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (p : CoordinatePartition u) (z : Input J noiseDim) : G :=
  partitionChainTerm g f u
    ((orderedFinpartitionEquivCoordinateFinpartition u).symm p) z

/-- Reindex the Mathlib Faà di Bruno sum by the unordered partitions used in the paper. -/
theorem sum_partitionChainTerm_eq_sum_finpartitionChainTerm
    {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (z : Input J noiseDim) :
    (∑ c : OrderedFinpartition u.card, partitionChainTerm g f u c z) =
      ∑ p : CoordinatePartition u, finpartitionChainTerm g f u p z := by
  simpa only [finpartitionChainTerm,
    Equiv.symm_apply_apply] using
    (Equiv.sum_comp (orderedFinpartitionEquivCoordinateFinpartition u)
      (fun p : CoordinatePartition u ↦
        partitionChainTerm g f u
          ((orderedFinpartitionEquivCoordinateFinpartition u).symm p) z))

/-- The set-partition Faà di Bruno formula specialized to mixed coordinate derivatives. -/
theorem mixedDerivative_comp {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (z : Input J noiseDim) (hg : ContDiffAt ℝ u.card g (f z))
    (hf : ContDiffAt ℝ u.card f z) :
    mixedDerivative (g ∘ f) u z =
      ∑ c : OrderedFinpartition u.card, partitionChainTerm g f u c z := by
  unfold mixedDerivative partitionChainTerm partitionDerivative coordinateDirections
    partitionDirections
  rw [iteratedFDeriv_comp hg hf le_rfl]
  simp only [FormalMultilinearSeries.taylorComp, ftaylorSeries,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  rfl

/-- The mixed-coordinate Faà di Bruno formula indexed directly by the unordered partitions of
the paper. -/
theorem mixedDerivative_comp_finpartition {J noiseDim : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F → G) (f : Input J noiseDim → F) (u : Finset (Index J noiseDim))
    (z : Input J noiseDim) (hg : ContDiffAt ℝ u.card g (f z))
    (hf : ContDiffAt ℝ u.card f z) :
    mixedDerivative (g ∘ f) u z =
      ∑ p : CoordinatePartition u, finpartitionChainTerm g f u p z := by
  rw [mixedDerivative_comp g f u z hg hf]
  exact sum_partitionChainTerm_eq_sum_finpartitionChainTerm g f u z

end

end TimeDependentLattice.Analysis
