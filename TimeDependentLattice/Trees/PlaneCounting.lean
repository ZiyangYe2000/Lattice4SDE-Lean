/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.Counting

/-!
# Concrete plane encodings for the weighted tree count

This file supplies the encoding step left abstract at the end of `Trees.Counting`.  It first
records the elementary facts about the Cartesian list `listChoices` that are needed to show
that the local child orderings of a valid payoff tree are all distinct.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open TimeDependentLattice.BrownianBridge

/-- Membership in `listChoices` is the pointwise membership relation between a chosen list and
the list of choice families. -/
theorem mem_listChoices_iff_forall₂ {α : Type*} {families : List (List α)}
    {chosen : List α} :
    chosen ∈ listChoices families ↔
      List.Forall₂ (fun entry family => entry ∈ family) chosen families := by
  induction families generalizing chosen with
  | nil =>
      simp [listChoices]
  | cons family families ih =>
      simp only [listChoices_cons, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨entry, hentry, tail, htail, rfl⟩
        exact .cons hentry (ih.mp htail)
      · intro hchosen
        cases hchosen with
        | cons hentry htail =>
            exact ⟨_, hentry, _, ih.mpr htail, rfl⟩

/-- Cartesian products of duplicate-free finite lists are duplicate-free. -/
theorem listChoices_nodup {α : Type*} {families : List (List α)}
    (hnodup : ∀ family ∈ families, family.Nodup) :
    (listChoices families).Nodup := by
  induction families with
  | nil => simp [listChoices]
  | cons family families ih =>
      have hfamily : family.Nodup := hnodup family List.mem_cons_self
      have hfamilies : ∀ choices ∈ families, choices.Nodup := by
        intro choices hchoices
        exact hnodup choices (List.mem_cons_of_mem family hchoices)
      rw [listChoices_cons, List.nodup_flatMap]
      constructor
      · intro entry hentry
        exact (ih hfamilies).map (by
          intro left right heq
          exact List.cons.inj heq |>.2)
      · apply (List.nodup_iff_pairwise_ne.mp hfamily).imp
        intro left right hne
        change List.Disjoint
          ((listChoices families).map (left :: ·))
          ((listChoices families).map (right :: ·))
        rw [List.disjoint_left]
        intro chosen hleft hright
        rcases List.mem_map.mp hleft with ⟨leftTail, -, rfl⟩
        rcases List.mem_map.mp hright with ⟨rightTail, -, heq⟩
        exact hne (List.cons.inj heq).1.symm

/-- Every entry of a Cartesian choice comes from one of the input families. -/
theorem mem_family_of_mem_choice {α : Type*} {families : List (List α)}
    {chosen : List α} (hchosen : chosen ∈ listChoices families)
    {entry : α} (hentry : entry ∈ chosen) :
    ∃ family ∈ families, entry ∈ family := by
  induction families generalizing chosen with
  | nil =>
      have hchosenEmpty : chosen = [] := by simpa [listChoices] using hchosen
      subst chosen
      simp at hentry
  | cons family families ih =>
      have hrel := mem_listChoices_iff_forall₂.mp hchosen
      cases hrel with
      | cons hhead htail =>
          simp only [List.mem_cons] at hentry
          rcases hentry with rfl | hentry
          · exact ⟨family, List.mem_cons_self, hhead⟩
          · rcases ih (mem_listChoices_iff_forall₂.mpr htail) hentry with
              ⟨other, hother, hmem⟩
            exact ⟨other, List.mem_cons_of_mem family hother, hmem⟩

/-- If distinct input families are disjoint, a Cartesian choice contains no repeated entry. -/
theorem nodup_of_mem_listChoices_of_pairwise_disjoint {α : Type*}
    {families : List (List α)} (hdisjoint : families.Pairwise List.Disjoint)
    {chosen : List α} (hchosen : chosen ∈ listChoices families) :
    chosen.Nodup := by
  induction families generalizing chosen with
  | nil =>
      have hchosenEmpty : chosen = [] := by simpa [listChoices] using hchosen
      subst chosen
      exact List.nodup_nil
  | cons family families ih =>
      have hrel := mem_listChoices_iff_forall₂.mp hchosen
      cases hrel with
      | cons hhead htail =>
          rw [List.pairwise_cons] at hdisjoint
          rw [List.nodup_cons]
          constructor
          · intro hmem
            rcases mem_family_of_mem_choice
                (mem_listChoices_iff_forall₂.mpr htail) hmem with
              ⟨other, hother, hheadOther⟩
            exact (List.disjoint_left.mp (hdisjoint.1 other hother)) hhead hheadOther
          · exact ih hdisjoint.2 (mem_listChoices_iff_forall₂.mpr htail)

/-- For pairwise-disjoint input families, two Cartesian choices that differ in position cannot
be permutations of one another. -/
theorem eq_of_mem_listChoices_of_perm_of_pairwise_disjoint {α : Type*}
    {families : List (List α)} (hdisjoint : families.Pairwise List.Disjoint)
    {left right : List α} (hleft : left ∈ listChoices families)
    (hright : right ∈ listChoices families) (hperm : left.Perm right) :
    left = right := by
  induction families generalizing left right with
  | nil =>
      have hleftEmpty : left = [] := by simpa [listChoices] using hleft
      have hrightEmpty : right = [] := by simpa [listChoices] using hright
      exact hleftEmpty.trans hrightEmpty.symm
  | cons family families ih =>
      have hleftRel := mem_listChoices_iff_forall₂.mp hleft
      have hrightRel := mem_listChoices_iff_forall₂.mp hright
      cases hleftRel with
      | cons hleftHead hleftTail =>
          rename_i leftHead leftTail
          cases hrightRel with
          | cons hrightHead hrightTail =>
              rename_i rightHead rightTail
              rw [List.pairwise_cons] at hdisjoint
              have hmemRight : leftHead ∈ rightHead :: rightTail :=
                (hperm.mem_iff).mp List.mem_cons_self
              have hheadEq : leftHead = rightHead := by
                rcases List.mem_cons.mp hmemRight with heq | htail
                · exact heq
                · rcases mem_family_of_mem_choice
                      (mem_listChoices_iff_forall₂.mpr hrightTail) htail with
                    ⟨other, hother, hleftOther⟩
                  exact ((List.disjoint_left.mp (hdisjoint.1 other hother))
                    hleftHead hleftOther).elim
              subst_vars
              have htailPerm := hperm.cons_inv
              have htailEq := ih hdisjoint.2
                (mem_listChoices_iff_forall₂.mpr hleftTail)
                (mem_listChoices_iff_forall₂.mpr hrightTail) htailPerm
              subst_vars
              rfl

/-! ## Ordered variants preserve the underlying labelled tree data -/

/-- Permuting a forest does not change the union of its coordinate supports. -/
theorem childrenSupport_eq_of_perm {J noiseDim : ℕ}
    {left right : List (DriftTreeData J noiseDim)} (hperm : left.Perm right) :
    childrenSupport left = childrenSupport right := by
  induction hperm with
  | nil => rfl
  | cons tree hperm ih =>
      simp only [childrenSupport_cons]
      rw [ih]
  | swap left right tail =>
      simp only [childrenSupport_cons]
      ac_rfl
  | trans hfirst hsecond ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

/-- Replacing every tree in a forest by a tree with the same support does not change the union
of the supports. -/
theorem childrenSupport_eq_of_forall₂_support_eq {J noiseDim : ℕ}
    {left right : List (DriftTreeData J noiseDim)}
    (hsupport : List.Forall₂
      (fun leftTree rightTree => leftTree.support = rightTree.support) left right) :
    childrenSupport left = childrenSupport right := by
  induction hsupport with
  | nil => rfl
  | cons hhead htail ih =>
      simp only [childrenSupport_cons]
      rw [hhead, ih]

/-- A pointwise equality relation in `Forall₂` identifies a mapped list with its target. -/
theorem map_eq_of_forall₂_apply_eq {α β : Type*} (f : α → β)
    {left : List α} {right : List β}
    (hrel : List.Forall₂ (fun a b => f a = b) left right) :
    left.map f = right := by
  induction hrel with
  | nil => rfl
  | cons hhead htail ih => simp [hhead, ih]

/-- Every plane ordering of a drift tree has exactly the same coordinate support. -/
theorem DriftTreeData.support_eq_of_mem_orderedVersions {J noiseDim : ℕ}
    (tree variant : DriftTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions) :
    variant.support = tree.support := by
  exact DriftTreeData.rec
    (motive_1 := fun tree => ∀ variant ∈ tree.orderedVersions,
      variant.support = tree.support)
    (motive_2 := fun children =>
      ∀ chosen ∈ listChoices (children.map DriftTreeData.orderedVersions),
        List.Forall₂
          (fun variant source => variant.support = source.support) chosen children)
    (fun direct children hchildren variant hvariant => by
      rw [DriftTreeData.orderedVersions_node] at hvariant
      simp only [List.mem_flatMap, List.mem_map] at hvariant
      rcases hvariant with ⟨chosen, hchosen, permuted, hpermuted, rfl⟩
      have hperm : permuted.Perm chosen := List.mem_permutations.mp hpermuted
      simp only [DriftTreeData.support_node]
      rw [childrenSupport_eq_of_perm hperm,
        childrenSupport_eq_of_forall₂_support_eq (hchildren chosen hchosen)])
    (by
      intro chosen hchosen
      have : chosen = [] := by simpa [listChoices] using hchosen
      subst chosen
      exact .nil)
    (fun head tail hhead htail chosen hchosen => by
      have hrel := mem_listChoices_iff_forall₂.mp hchosen
      cases hrel with
      | cons hvariant hchosenTail =>
          exact .cons (hhead _ hvariant)
            (htail _ (mem_listChoices_iff_forall₂.mpr hchosenTail)))
    tree variant hvariant

/-- Concatenating pointwise-permuted lists preserves the resulting flattened multiset. -/
theorem flatMap_perm_of_forall₂_perm {α β : Type*} (f : α → List β) (g : α → List β)
    {left right : List α} (hrel : List.Forall₂ (fun a b => (f a).Perm (g b)) left right) :
    (left.flatMap f).Perm (right.flatMap g) := by
  induction hrel with
  | nil => exact .nil
  | cons hhead htail ih =>
      simpa only [List.flatMap_cons] using hhead.append ih

/-- Plane ordering changes only the order of the preorder direct-label list. -/
theorem DriftTreeData.directLabels_perm_of_mem_orderedVersions {J noiseDim : ℕ}
    (tree variant : DriftTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions) :
    variant.directLabels.Perm tree.directLabels := by
  exact DriftTreeData.rec
    (motive_1 := fun tree => ∀ variant ∈ tree.orderedVersions,
      variant.directLabels.Perm tree.directLabels)
    (motive_2 := fun children =>
      ∀ chosen ∈ listChoices (children.map DriftTreeData.orderedVersions),
        List.Forall₂
          (fun variant source => variant.directLabels.Perm source.directLabels)
          chosen children)
    (fun direct children hchildren variant hvariant => by
      rw [DriftTreeData.orderedVersions_node] at hvariant
      simp only [List.mem_flatMap, List.mem_map] at hvariant
      rcases hvariant with ⟨chosen, hchosen, permuted, hpermuted, rfl⟩
      have hperm : permuted.Perm chosen := List.mem_permutations.mp hpermuted
      simp only [DriftTreeData.directLabels]
      exact List.Perm.cons direct
        ((hperm.flatMap (fun _ _ => List.Perm.refl _)).trans
          (flatMap_perm_of_forall₂_perm DriftTreeData.directLabels
            DriftTreeData.directLabels (hchildren chosen hchosen))))
    (by
      intro chosen hchosen
      have : chosen = [] := by simpa [listChoices] using hchosen
      subst chosen
      exact .nil)
    (fun head tail hhead htail chosen hchosen => by
      have hrel := mem_listChoices_iff_forall₂.mp hchosen
      cases hrel with
      | cons hvariant hchosenTail =>
          exact .cons (hhead _ hvariant)
            (htail _ (mem_listChoices_iff_forall₂.mpr hchosenTail)))
    tree variant hvariant

/-- Pointwise direct-label invariance for a Cartesian forest choice. -/
theorem directLabels_forall₂_of_mem_listChoices_orderedVersions
    {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim))
    (chosen : List (DriftTreeData J noiseDim))
    (hchosen : chosen ∈ listChoices (children.map DriftTreeData.orderedVersions)) :
    List.Forall₂
      (fun variant source => variant.directLabels.Perm source.directLabels)
      chosen children := by
  induction children generalizing chosen with
  | nil =>
      have : chosen = [] := by simpa [listChoices] using hchosen
      subst chosen
      exact .nil
  | cons child children ih =>
      have hrel := mem_listChoices_iff_forall₂.mp hchosen
      cases hrel with
      | cons hvariant hchosenTail =>
          exact .cons
            (child.directLabels_perm_of_mem_orderedVersions _ hvariant)
            (ih _ (mem_listChoices_iff_forall₂.mpr hchosenTail))

/-- At the payoff root, plane ordering preserves the multiset of all drift-vertex direct
labels. -/
theorem PayoffTreeData.driftDirectLabels_perm_of_mem_orderedVersions
    {J noiseDim : ℕ} (tree variant : PayoffTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions) :
    variant.driftDirectLabels.Perm tree.driftDirectLabels := by
  rw [PayoffTreeData.orderedVersions] at hvariant
  simp only [List.mem_flatMap, List.mem_map] at hvariant
  rcases hvariant with ⟨chosen, hchosen, permuted, hpermuted, rfl⟩
  have hperm : permuted.Perm chosen := List.mem_permutations.mp hpermuted
  unfold PayoffTreeData.driftDirectLabels
  exact (hperm.flatMap (fun _ _ => List.Perm.refl _)).trans
    (flatMap_perm_of_forall₂_perm DriftTreeData.directLabels
      DriftTreeData.directLabels
      (directLabels_forall₂_of_mem_listChoices_orderedVersions
        tree.children chosen hchosen))

/-- The same invariance after discarding empty direct sets. -/
theorem PayoffTreeData.nonemptyDirectLabels_perm_of_mem_orderedVersions
    {J noiseDim : ℕ} (tree variant : PayoffTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions) :
    variant.nonemptyDirectLabels.Perm tree.nonemptyDirectLabels := by
  exact (tree.driftDirectLabels_perm_of_mem_orderedVersions variant hvariant).filter _

/-- Ordering children does not change the payoff-root direct label. -/
theorem PayoffTreeData.direct_eq_of_mem_orderedVersions {J noiseDim : ℕ}
    (tree variant : PayoffTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions) :
    variant.direct = tree.direct := by
  rw [PayoffTreeData.orderedVersions] at hvariant
  rcases List.mem_flatMap.mp hvariant with ⟨chosen, _, hchosen⟩
  rcases List.mem_map.mp hchosen with ⟨ordered, _, rfl⟩
  rfl

/-- Ordered-version lists belonging to two valid disjoint subtrees are disjoint lists. -/
theorem DriftTreeData.orderedVersions_disjoint_of_valid_of_disjoint
    {J noiseDim : ℕ} {left right : DriftTreeData J noiseDim}
    (hleft : left.Valid) (hright : right.Valid)
    (hdisjoint : Disjoint left.support right.support) :
    left.orderedVersions.Disjoint right.orderedVersions := by
  rw [List.disjoint_left]
  intro variant hvariantLeft hvariantRight
  have hleftSupport := left.support_eq_of_mem_orderedVersions variant hvariantLeft
  have hrightSupport := right.support_eq_of_mem_orderedVersions variant hvariantRight
  have hsupportEq : left.support = right.support := hleftSupport.symm.trans hrightSupport
  have hself : Disjoint left.support left.support := by simpa [hsupportEq] using hdisjoint
  exact (left.valid_support_nonempty hleft).ne_empty (disjoint_self.mp hself)

/-- The ordered-version families of the children of a valid node are pairwise disjoint. -/
theorem DriftTreeData.orderedVersionFamilies_pairwise_disjoint
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    (tree.children.map DriftTreeData.orderedVersions).Pairwise List.Disjoint := by
  cases tree with
  | node direct children =>
      simp only [DriftTreeData.Valid, DriftTreeData.children] at hvalid ⊢
      have hsupportPairwise :
          children.Pairwise
            (fun left right => Disjoint left.support right.support) := by
        rw [← List.pairwise_map]
        exact hvalid.2.2.1
      rw [List.pairwise_map]
      exact hsupportPairwise.imp_of_mem (by
        intro left right hleftMem hrightMem hdisjoint
        exact left.orderedVersions_disjoint_of_valid_of_disjoint
          (hvalid.2.2.2.2 left hleftMem) (hvalid.2.2.2.2 right hrightMem) hdisjoint)

/-- For a valid drift tree, the list `orderedVersions` contains each simultaneous local child
ordering exactly once. -/
theorem DriftTreeData.orderedVersions_nodup_of_valid {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid) :
    tree.orderedVersions.Nodup := by
  exact DriftTreeData.rec
    (motive_1 := fun tree => tree.Valid → tree.orderedVersions.Nodup)
    (motive_2 := fun children =>
      (∀ child ∈ children, child.Valid) →
        ∀ child ∈ children, child.orderedVersions.Nodup)
    (fun direct children hchildren hvalidNode => by
      simp only [DriftTreeData.Valid] at hvalidNode
      let families := children.map DriftTreeData.orderedVersions
      have hfamilyNodup : ∀ family ∈ families, family.Nodup := by
        intro family hfamily
        rcases List.mem_map.mp hfamily with ⟨child, hchild, rfl⟩
        exact hchildren hvalidNode.2.2.2.2 child hchild
      have hchoicesNodup : (listChoices families).Nodup :=
        listChoices_nodup hfamilyNodup
      have hfamiliesDisjoint : families.Pairwise List.Disjoint := by
        exact (DriftTreeData.node direct children).orderedVersionFamilies_pairwise_disjoint
          (by simpa only [DriftTreeData.Valid] using hvalidNode)
      rw [DriftTreeData.orderedVersions_node, List.nodup_flatMap]
      constructor
      · intro chosen hchosen
        exact (List.nodup_permutations chosen
          (nodup_of_mem_listChoices_of_pairwise_disjoint
            hfamiliesDisjoint hchosen)).map (by
              intro left right heq
              exact DriftTreeData.node.inj heq |>.2)
      · apply (List.nodup_iff_pairwise_ne.mp hchoicesNodup).imp_of_mem
        intro left right hleft hright hne
        change List.Disjoint
          (left.permutations.map (DriftTreeData.node direct))
          (right.permutations.map (DriftTreeData.node direct))
        rw [List.disjoint_left]
        intro variant hvariantLeft hvariantRight
        rcases List.mem_map.mp hvariantLeft with
          ⟨leftChildren, hleftChildren, rfl⟩
        rcases List.mem_map.mp hvariantRight with
          ⟨rightChildren, hrightChildren, heq⟩
        have hchildrenEq : rightChildren = leftChildren :=
          (DriftTreeData.node.inj heq).2
        have hpermLeft : leftChildren.Perm left :=
          List.mem_permutations.mp hleftChildren
        have hpermRight : rightChildren.Perm right :=
          List.mem_permutations.mp hrightChildren
        have hperm : left.Perm right := by
          exact hpermLeft.symm.trans (hchildrenEq ▸ hpermRight)
        exact hne (eq_of_mem_listChoices_of_perm_of_pairwise_disjoint
          hfamiliesDisjoint hleft hright hperm))
    (by simp)
    (fun head tail hhead htail hvalidChildren => by
      have hheadValid := hvalidChildren head List.mem_cons_self
      have htailValid : ∀ other ∈ tail, other.Valid := by
        intro other hother
        exact hvalidChildren other (List.mem_cons_of_mem head hother)
      intro child hchild
      simp only [List.mem_cons] at hchild
      rcases hchild with rfl | hchild
      · exact hhead hheadValid
      · exact htail htailValid child hchild)
    tree hvalid

/-- The root-level ordered-version list is duplicate-free for every valid payoff tree. -/
theorem PayoffTreeData.orderedVersions_nodup_of_valid {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) {support : Finset (Index J noiseDim)}
    (hvalid : tree.Valid support) :
    tree.orderedVersions.Nodup := by
  let families := tree.children.map DriftTreeData.orderedVersions
  have hfamilyNodup : ∀ family ∈ families, family.Nodup := by
    intro family hfamily
    rcases List.mem_map.mp hfamily with ⟨child, hchild, rfl⟩
    exact child.orderedVersions_nodup_of_valid
      (hvalid.2.2.2.2.2 child hchild)
  have hchoicesNodup : (listChoices families).Nodup :=
    listChoices_nodup hfamilyNodup
  have hfamiliesDisjoint : families.Pairwise List.Disjoint := by
    have hsupportPairwise :
        tree.children.Pairwise
          (fun left right => Disjoint left.support right.support) := by
      rw [← List.pairwise_map]
      exact hvalid.2.2.2.1
    rw [List.pairwise_map]
    exact hsupportPairwise.imp_of_mem (by
      intro left right hleftMem hrightMem hdisjoint
      exact left.orderedVersions_disjoint_of_valid_of_disjoint
        (hvalid.2.2.2.2.2 left hleftMem)
        (hvalid.2.2.2.2.2 right hrightMem) hdisjoint)
  rw [PayoffTreeData.orderedVersions, List.nodup_flatMap]
  constructor
  · intro chosen hchosen
    exact (List.nodup_permutations chosen
      (nodup_of_mem_listChoices_of_pairwise_disjoint
        hfamiliesDisjoint hchosen)).map (by
          intro left right heq
          exact PayoffTreeData.mk.inj heq |>.2)
  · apply (List.nodup_iff_pairwise_ne.mp hchoicesNodup).imp_of_mem
    intro left right hleft hright hne
    change List.Disjoint
      (left.permutations.map (PayoffTreeData.mk tree.direct))
      (right.permutations.map (PayoffTreeData.mk tree.direct))
    rw [List.disjoint_left]
    intro variant hvariantLeft hvariantRight
    rcases List.mem_map.mp hvariantLeft with ⟨leftChildren, hleftChildren, rfl⟩
    rcases List.mem_map.mp hvariantRight with ⟨rightChildren, hrightChildren, heq⟩
    have hchildrenEq : rightChildren = leftChildren :=
      (PayoffTreeData.mk.inj heq).2
    have hpermLeft : leftChildren.Perm left :=
      List.mem_permutations.mp hleftChildren
    have hpermRight : rightChildren.Perm right :=
      List.mem_permutations.mp hrightChildren
    have hperm : left.Perm right := by
      exact hpermLeft.symm.trans (hchildrenEq ▸ hpermRight)
    exact hne (eq_of_mem_listChoices_of_perm_of_pairwise_disjoint
      hfamiliesDisjoint hleft hright hperm)

/-! ## Recovering the canonical unordered tree from a plane ordering -/

/-- Disjoint nonempty supports have different least-coordinate keys. -/
theorem DriftTreeData.supportKey_ne_of_disjoint_of_nonempty
    {J noiseDim : ℕ} {left right : DriftTreeData J noiseDim}
    (hleft : left.support.Nonempty) (hright : right.support.Nonempty)
    (hdisjoint : Disjoint left.support right.support) :
    left.supportKey ≠ right.supportKey := by
  intro hkey
  have hleftImage : (left.support.image coordinateRank).Nonempty := hleft.image _
  have hrightImage : (right.support.image coordinateRank).Nonempty := hright.image _
  have hminEq :
      (left.support.image coordinateRank).min' hleftImage =
        (right.support.image coordinateRank).min' hrightImage := by
    apply WithTop.coe_eq_coe.mp
    rw [Finset.coe_min', Finset.coe_min']
    exact hkey
  have hleftMinMem := Finset.min'_mem _ hleftImage
  have hrightMinMem := Finset.min'_mem _ hrightImage
  rcases Finset.mem_image.mp hleftMinMem with ⟨leftIndex, hleftMem, hleftRank⟩
  rcases Finset.mem_image.mp hrightMinMem with ⟨rightIndex, hrightMem, hrightRank⟩
  have hindexEq : leftIndex = rightIndex := coordinateRank_injective (by
    rw [hleftRank, hrightRank, hminEq])
  subst rightIndex
  exact Finset.disjoint_left.mp hdisjoint hleftMem hrightMem

/-- Sort children by their least coordinate rank.  The definition is used only on valid
pairwise-disjoint child families, where all keys are distinct. -/
noncomputable def canonicalChildOrder {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim)) : List (DriftTreeData J noiseDim) :=
  children.mergeSort fun left right => decide (left.supportKey ≤ right.supportKey)

theorem canonicalChildOrder_perm {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim)) :
    (canonicalChildOrder children).Perm children := by
  exact List.mergeSort_perm _ _

/-- Sorting a pairwise-disjoint valid child family produces the canonical strict key order. -/
theorem canonicalChildOrder_canonical {J noiseDim : ℕ}
    (children : List (DriftTreeData J noiseDim))
    (hvalid : ∀ child ∈ children, child.Valid)
    (hdisjoint : childrenDisjoint children) :
    childrenCanonical (canonicalChildOrder children) := by
  let ordered := canonicalChildOrder children
  have hperm : ordered.Perm children := canonicalChildOrder_perm children
  have hle : ordered.Pairwise
      (fun left right => left.supportKey ≤ right.supportKey) := by
    unfold ordered canonicalChildOrder
    simpa using List.pairwise_mergeSort
      (le := fun left right : DriftTreeData J noiseDim =>
        decide (left.supportKey ≤ right.supportKey))
      (fun _ _ _ hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact hab.trans hbc)
      (fun left right => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total left.supportKey right.supportKey)
      children
  have hdisjointChildren : children.Pairwise
      (fun left right => Disjoint left.support right.support) := by
    rw [← List.pairwise_map]
    exact hdisjoint
  have horderedDisjoint : ordered.Pairwise
      (fun left right => Disjoint left.support right.support) :=
    (hperm.pairwise_iff (fun h => h.symm)).2 hdisjointChildren
  rw [childrenCanonical, List.pairwise_iff_get]
  rw [List.pairwise_iff_get] at hle horderedDisjoint
  intro i j hij
  have hleftMem : ordered.get i ∈ children :=
    (hperm.mem_iff).mp (List.get_mem ordered i)
  have hrightMem : ordered.get j ∈ children :=
    (hperm.mem_iff).mp (List.get_mem ordered j)
  have hne := (ordered.get i).supportKey_ne_of_disjoint_of_nonempty
    ((ordered.get i).valid_support_nonempty (hvalid _ hleftMem))
    ((ordered.get j).valid_support_nonempty (hvalid _ hrightMem))
    (horderedDisjoint i j hij)
  exact lt_of_le_of_ne (hle i j hij) hne

/-- Recursively forget all local plane orders and restore the paper's canonical sibling order. -/
noncomputable def DriftTreeData.canonicalize {J noiseDim : ℕ} :
    DriftTreeData J noiseDim → DriftTreeData J noiseDim
  | .node direct children =>
      .node direct (canonicalChildOrder (children.map DriftTreeData.canonicalize))
termination_by tree => sizeOf tree

/-- A plane version of a valid drift tree canonicalizes back to that tree. -/
theorem DriftTreeData.canonicalize_eq_of_mem_orderedVersions
    {J noiseDim : ℕ} (tree : DriftTreeData J noiseDim) (hvalid : tree.Valid)
    (variant : DriftTreeData J noiseDim) (hvariant : variant ∈ tree.orderedVersions) :
    variant.canonicalize = tree := by
  exact DriftTreeData.rec
    (motive_1 := fun tree => tree.Valid → ∀ variant ∈ tree.orderedVersions,
      variant.canonicalize = tree)
    (motive_2 := fun children =>
      (∀ child ∈ children, child.Valid) →
      ∀ chosen ∈ listChoices (children.map DriftTreeData.orderedVersions),
        List.Forall₂
          (fun variant source => variant.canonicalize = source) chosen children)
    (fun direct children hchildren hvalidNode variant hvariant => by
      have hvalidNode' := hvalidNode
      simp only [DriftTreeData.Valid] at hvalidNode'
      rw [DriftTreeData.orderedVersions_node] at hvariant
      simp only [List.mem_flatMap, List.mem_map] at hvariant
      rcases hvariant with ⟨chosen, hchosen, permuted, hpermuted, rfl⟩
      have hchoiceCanon := hchildren hvalidNode'.2.2.2.2 chosen hchosen
      have hmapChosen : chosen.map DriftTreeData.canonicalize = children := by
        exact map_eq_of_forall₂_apply_eq DriftTreeData.canonicalize hchoiceCanon
      have hperm : permuted.Perm chosen := List.mem_permutations.mp hpermuted
      have hcanonPerm :
          (permuted.map DriftTreeData.canonicalize).Perm children := by
        simpa [hmapChosen] using hperm.map DriftTreeData.canonicalize
      have hcanonValid : ∀ child ∈ permuted.map DriftTreeData.canonicalize,
          child.Valid := by
        intro child hchild
        exact hvalidNode'.2.2.2.2 child ((hcanonPerm.mem_iff).mp hchild)
      have hchildrenDisjoint : childrenDisjoint children := hvalidNode'.2.2.1
      have hcanonDisjoint : childrenDisjoint
          (permuted.map DriftTreeData.canonicalize) := by
        unfold childrenDisjoint at hchildrenDisjoint ⊢
        have hsupportPerm := hcanonPerm.map DriftTreeData.support
        exact (hsupportPerm.pairwise_iff (fun h => h.symm)).2 hchildrenDisjoint
      have horderedCanonical := canonicalChildOrder_canonical
        (permuted.map DriftTreeData.canonicalize) hcanonValid hcanonDisjoint
      have horderedPerm :
          (canonicalChildOrder (permuted.map DriftTreeData.canonicalize)).Perm children :=
        (canonicalChildOrder_perm _).trans hcanonPerm
      have hchildrenEq := children_eq_of_perm_of_canonical horderedPerm
        horderedCanonical hvalidNode'.2.2.2.1
      simp only [DriftTreeData.canonicalize]
      rw [hchildrenEq])
    (by
      intro _ chosen hchosen
      have : chosen = [] := by simpa [listChoices] using hchosen
      subst chosen
      exact .nil)
    (fun head tail hhead htail hvalidChildren chosen hchosen => by
      have hrel := mem_listChoices_iff_forall₂.mp hchosen
      cases hrel with
      | cons hvariant hchosenTail =>
          exact .cons
            (hhead (hvalidChildren head List.mem_cons_self) _ hvariant)
            (htail (fun other hother =>
              hvalidChildren other (List.mem_cons_of_mem head hother)) _
                (mem_listChoices_iff_forall₂.mpr hchosenTail)))
    tree hvalid variant hvariant

/-- Pointwise recovery of a forest chosen from the ordered-version families. -/
theorem canonicalize_forall₂_of_mem_listChoices_orderedVersions
    {J noiseDim : ℕ} (children : List (DriftTreeData J noiseDim))
    (hvalid : ∀ child ∈ children, child.Valid)
    (chosen : List (DriftTreeData J noiseDim))
    (hchosen : chosen ∈ listChoices (children.map DriftTreeData.orderedVersions)) :
    List.Forall₂ (fun variant source => variant.canonicalize = source) chosen children := by
  induction children generalizing chosen with
  | nil =>
      have : chosen = [] := by simpa [listChoices] using hchosen
      subst chosen
      exact .nil
  | cons child children ih =>
      have hrel := mem_listChoices_iff_forall₂.mp hchosen
      cases hrel with
      | cons hvariant hchosenTail =>
          exact .cons
            (child.canonicalize_eq_of_mem_orderedVersions
              (hvalid child List.mem_cons_self) _ hvariant)
            (ih (fun other hother =>
              hvalid other (List.mem_cons_of_mem child hother)) _
                (mem_listChoices_iff_forall₂.mpr hchosenTail))

/-- Canonicalization at the payoff root. -/
noncomputable def PayoffTreeData.canonicalize {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) : PayoffTreeData J noiseDim :=
  .mk tree.direct
    (canonicalChildOrder (tree.children.map DriftTreeData.canonicalize))

/-- Every plane version of a valid payoff tree canonicalizes back to its unique source. -/
theorem PayoffTreeData.canonicalize_eq_of_mem_orderedVersions
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim)
    {support : Finset (Index J noiseDim)} (hvalid : tree.Valid support)
    (variant : PayoffTreeData J noiseDim) (hvariant : variant ∈ tree.orderedVersions) :
    variant.canonicalize = tree := by
  rw [PayoffTreeData.orderedVersions] at hvariant
  simp only [List.mem_flatMap, List.mem_map] at hvariant
  rcases hvariant with ⟨chosen, hchosen, permuted, hpermuted, rfl⟩
  have hchoiceCanon := canonicalize_forall₂_of_mem_listChoices_orderedVersions
    tree.children hvalid.2.2.2.2.2 chosen hchosen
  have hmapChosen : chosen.map DriftTreeData.canonicalize = tree.children :=
    map_eq_of_forall₂_apply_eq DriftTreeData.canonicalize hchoiceCanon
  have hperm : permuted.Perm chosen := List.mem_permutations.mp hpermuted
  have hcanonPerm :
      (permuted.map DriftTreeData.canonicalize).Perm tree.children := by
    simpa [hmapChosen] using hperm.map DriftTreeData.canonicalize
  have hcanonValid : ∀ child ∈ permuted.map DriftTreeData.canonicalize,
      child.Valid := by
    intro child hchild
    exact hvalid.2.2.2.2.2 child ((hcanonPerm.mem_iff).mp hchild)
  have hcanonDisjoint : childrenDisjoint
      (permuted.map DriftTreeData.canonicalize) := by
    have hchildrenDisjoint : childrenDisjoint tree.children := hvalid.2.2.2.1
    unfold childrenDisjoint at hchildrenDisjoint ⊢
    have hsupportPerm := hcanonPerm.map DriftTreeData.support
    exact (hsupportPerm.pairwise_iff (fun h => h.symm)).2 hchildrenDisjoint
  have horderedCanonical := canonicalChildOrder_canonical
    (permuted.map DriftTreeData.canonicalize) hcanonValid hcanonDisjoint
  have horderedPerm :
      (canonicalChildOrder (permuted.map DriftTreeData.canonicalize)).Perm tree.children :=
    (canonicalChildOrder_perm _).trans hcanonPerm
  have hchildrenEq := children_eq_of_perm_of_canonical horderedPerm
    horderedCanonical hvalid.2.2.2.2.1
  simp only [PayoffTreeData.canonicalize]
  rw [hchildrenEq]

/-- The payoff-root analogue: a plane version of a valid payoff tree determines and
canonicalizes back to its unique source tree. -/
theorem PayoffTreeData.eq_of_valid_of_common_orderedVersion
    {J noiseDim : ℕ} {left right variant : PayoffTreeData J noiseDim}
    {leftSupport rightSupport : Finset (Index J noiseDim)}
    (hleft : left.Valid leftSupport) (hright : right.Valid rightSupport)
    (hvariantLeft : variant ∈ left.orderedVersions)
    (hvariantRight : variant ∈ right.orderedVersions) :
    left = right := by
  have hleftEq := left.canonicalize_eq_of_mem_orderedVersions
    hleft variant hvariantLeft
  have hrightEq := right.canonicalize_eq_of_mem_orderedVersions
    hright variant hvariantRight
  exact hleftEq.symm.trans hrightEq

/-! ## The explicit Catalan shape-and-placement code -/

/-- Preorder traversal of the left-child/right-sibling code is exactly the preorder list of
direct labels on the encoded drift forest. -/
theorem binaryTreePreorder_encodeDriftForest {J noiseDim : ℕ} :
    ∀ children : List (DriftTreeData J noiseDim),
      binaryTreePreorder (encodeDriftForest children) =
        children.flatMap DriftTreeData.directLabels
  | [] => by simp [encodeDriftForest, binaryTreePreorder]
  | .node direct children :: tail => by
      rw [encodeDriftForest]
      simp only [binaryTreePreorder, DriftTreeData.directLabels, List.flatMap_cons]
      rw [binaryTreePreorder_encodeDriftForest children,
        binaryTreePreorder_encodeDriftForest tail]
      simp

@[simp]
theorem PayoffTreeData.binaryTreePreorder_planeCode {J noiseDim : ℕ}
    (tree : PayoffTreeData J noiseDim) :
    binaryTreePreorder tree.planeCode = tree.driftDirectLabels := by
  exact binaryTreePreorder_encodeDriftForest tree.children

theorem DriftTreeData.length_directLabels_eq_vertexCount {J noiseDim : ℕ}
    (tree : DriftTreeData J noiseDim) :
    tree.directLabels.length = tree.vertexCount := by
  exact DriftTreeData.rec
    (motive_1 := fun tree => tree.directLabels.length = tree.vertexCount)
    (motive_2 := fun children =>
      (children.flatMap DriftTreeData.directLabels).length =
        (children.map DriftTreeData.vertexCount).sum)
    (fun direct children hchildren => by
      simp [DriftTreeData.directLabels, hchildren, Nat.add_comm])
    (by simp)
    (fun head tail hhead htail => by
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      rw [hhead, htail])
    tree

theorem PayoffTreeData.length_driftDirectLabels_add_one_eq_vertexCount
    {J noiseDim : ℕ} (tree : PayoffTreeData J noiseDim) :
    tree.driftDirectLabels.length + 1 = tree.vertexCount := by
  unfold PayoffTreeData.driftDirectLabels PayoffTreeData.vertexCount
  have hlength :
      (tree.children.flatMap DriftTreeData.directLabels).length =
        (tree.children.map DriftTreeData.vertexCount).sum := by
    induction tree.children with
    | nil => simp
    | cons head tail ih =>
        simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
        rw [head.length_directLabels_eq_vertexCount, ih]
  omega

/-- An ordered version has the same number of vertices as its canonical source. -/
theorem PayoffTreeData.vertexCount_eq_of_mem_orderedVersions
    {J noiseDim : ℕ} (tree variant : PayoffTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions) :
    variant.vertexCount = tree.vertexCount := by
  have hperm := tree.driftDirectLabels_perm_of_mem_orderedVersions variant hvariant
  have hlength := hperm.length_eq
  rw [← tree.length_driftDirectLabels_add_one_eq_vertexCount,
    ← variant.length_driftDirectLabels_add_one_eq_vertexCount]
  omega

/-- If filtering a list by `p` removes all repeated retained entries, the first occurrence of a
retained entry is its given position in the original list. -/
theorem idxOf_get_eq_of_filter_nodup {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) (values : List α) (value : α) (i : ℕ)
    (hi : i < values.length) (hget : values.get ⟨i, hi⟩ = value)
    (hnodup : (values.filter p).Nodup) (hkeep : p value = true) :
    values.idxOf value = i := by
  induction values generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero =>
          have hhead : head = value := by simpa using hget
          subst head
          simp
      | succ i =>
          have hiTail : i < tail.length := by simpa using hi
          have hgetTail : tail.get ⟨i, hiTail⟩ = value := by simpa using hget
          have htailNodup : (tail.filter p).Nodup := by
            by_cases hheadKeep : p head = true
            · have hconsNodup : (head :: tail.filter p).Nodup := by
                simpa [hheadKeep] using hnodup
              exact hconsNodup.tail
            · simpa [hheadKeep] using hnodup
          have hne : head ≠ value := by
            intro heq
            subst head
            have hconsNodup : (value :: tail.filter p).Nodup := by
              simpa [hkeep] using hnodup
            have hvalueMemTail : value ∈ tail := by
              rw [← hgetTail]
              exact List.get_mem tail ⟨i, hiTail⟩
            have hvalueMemFilter : value ∈ tail.filter p := by
              exact List.mem_filter.mpr ⟨hvalueMemTail, hkeep⟩
            exact (List.nodup_cons.mp hconsNodup).1 hvalueMemFilter
          rw [List.idxOf_cons_ne tail hne,
            ih i hiTail hgetTail htailNodup]

/-- The plane tree selected by one occurrence counted by `Q(𝔗)`. -/
noncomputable def OrderedPayoffOccurrence.variant {J noiseDim : ℕ}
    {family : Finset (PayoffTreeData J noiseDim)}
    (occurrence : OrderedPayoffOccurrence family) : PayoffTreeData J noiseDim :=
  let tree := occurrence.1.1
  tree.orderedVersions.get
    (Fin.cast tree.length_orderedVersions_eq_childFactorialProduct.symm occurrence.2)

theorem OrderedPayoffOccurrence.variant_mem_orderedVersions {J noiseDim : ℕ}
    {family : Finset (PayoffTreeData J noiseDim)}
    (occurrence : OrderedPayoffOccurrence family) :
    occurrence.variant ∈ occurrence.1.1.orderedVersions := by
  exact List.get_mem _ _

/-- A nonempty block appears at a well-defined vertex position in the binary plane code. -/
noncomputable def payoffBlockPlacement {J noiseDim : ℕ}
    (blocks : Finset (Finset (Index J noiseDim)))
    (tree variant : PayoffTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions)
    (hblocks : tree.nonemptyDirectLabels.Perm blocks.toList) :
    (↥blocks) ↪ Fin variant.planeCode.numNodes := by
  let labels := variant.driftDirectLabels
  have hlength : labels.length = variant.planeCode.numNodes := by
    change variant.driftDirectLabels.length = variant.planeCode.numNodes
    rw [← variant.binaryTreePreorder_planeCode, BinaryTree.length_preorder]
  have hvariantBlocks : variant.nonemptyDirectLabels.Perm blocks.toList :=
    (tree.nonemptyDirectLabels_perm_of_mem_orderedVersions variant hvariant).trans hblocks
  let position : ↥blocks → Fin variant.planeCode.numNodes := fun block => by
    have hblockInBlocks : block.1 ∈ blocks.toList := by simpa using block.2
    have hblockNonempty : block.1 ∈ variant.nonemptyDirectLabels :=
      (hvariantBlocks.mem_iff).mpr hblockInBlocks
    have hblockLabels : block.1 ∈ labels := (List.mem_filter.mp hblockNonempty).1
    exact ⟨labels.idxOf block.1, by
      rw [← hlength]
      exact List.idxOf_lt_length_iff.mpr hblockLabels⟩
  exact ⟨position, by
    intro left right heq
    apply Subtype.ext
    have hleftInBlocks : left.1 ∈ blocks.toList := by simpa using left.2
    have hrightInBlocks : right.1 ∈ blocks.toList := by simpa using right.2
    have hleftNonempty : left.1 ∈ variant.nonemptyDirectLabels :=
      (hvariantBlocks.mem_iff).mpr hleftInBlocks
    have hrightNonempty : right.1 ∈ variant.nonemptyDirectLabels :=
      (hvariantBlocks.mem_iff).mpr hrightInBlocks
    have hleftLabels : left.1 ∈ labels := (List.mem_filter.mp hleftNonempty).1
    have hrightLabels : right.1 ∈ labels := (List.mem_filter.mp hrightNonempty).1
    have hleftBound : labels.idxOf left.1 < labels.length :=
      List.idxOf_lt_length_iff.mpr hleftLabels
    have hrightBound : labels.idxOf right.1 < labels.length :=
      List.idxOf_lt_length_iff.mpr hrightLabels
    have hidx : labels.idxOf left.1 = labels.idxOf right.1 := by
      exact congrArg Fin.val heq
    calc
      left.1 = labels.get ⟨labels.idxOf left.1, hleftBound⟩ :=
        (List.idxOf_get hleftBound).symm
      _ = labels.get ⟨labels.idxOf right.1, hrightBound⟩ := by
        congr 1
        exact Fin.ext hidx
      _ = right.1 := List.idxOf_get hrightBound⟩

@[simp]
theorem payoffBlockPlacement_apply_val {J noiseDim : ℕ}
    (blocks : Finset (Finset (Index J noiseDim)))
    (tree variant : PayoffTreeData J noiseDim)
    (hvariant : variant ∈ tree.orderedVersions)
    (hblocks : tree.nonemptyDirectLabels.Perm blocks.toList)
    (block : ↥blocks) :
    (payoffBlockPlacement blocks tree variant hvariant hblocks block).val =
      variant.driftDirectLabels.idxOf block.1 := rfl

/-- The positions of all nonempty blocks determine the full preorder label list: every
remaining position carries the empty direct label. -/
theorem driftDirectLabels_eq_of_blockPositions_eq {J noiseDim : ℕ}
    (blocks : Finset (Finset (Index J noiseDim)))
    (left right : List (Finset (Index J noiseDim)))
    (hlength : left.length = right.length)
    (hleftBlocks :
      (left.filter fun direct => decide direct.Nonempty).Perm blocks.toList)
    (hrightBlocks :
      (right.filter fun direct => decide direct.Nonempty).Perm blocks.toList)
    (hpositions : ∀ block : ↥blocks, left.idxOf block.1 = right.idxOf block.1) :
    left = right := by
  have hleftNodup :
      (left.filter fun direct => decide direct.Nonempty).Nodup :=
    hleftBlocks.nodup_iff.mpr (Finset.nodup_toList blocks)
  have hrightNodup :
      (right.filter fun direct => decide direct.Nonempty).Nodup :=
    hrightBlocks.nodup_iff.mpr (Finset.nodup_toList blocks)
  apply List.ext_get hlength
  intro i hileft hiright
  let leftValue := left.get ⟨i, hileft⟩
  let rightValue := right.get ⟨i, hiright⟩
  by_cases hleftNonempty : leftValue.Nonempty
  · have hleftKeep : decide leftValue.Nonempty = true := by simp [hleftNonempty]
    have hleftFilter : leftValue ∈
        left.filter fun direct => decide direct.Nonempty := by
      exact List.mem_filter.mpr ⟨List.get_mem left ⟨i, hileft⟩, hleftKeep⟩
    have hleftInBlocks : leftValue ∈ blocks.toList :=
      hleftBlocks.mem_iff.mp hleftFilter
    let block : ↥blocks := ⟨leftValue, by simpa using hleftInBlocks⟩
    have hleftIdx : left.idxOf leftValue = i :=
      idxOf_get_eq_of_filter_nodup
        (fun direct : Finset (Index J noiseDim) => decide direct.Nonempty)
        left leftValue i hileft rfl hleftNodup hleftKeep
    have hrightIdx : right.idxOf leftValue = i := by
      calc
        right.idxOf leftValue = left.idxOf leftValue := by
          simpa [block] using (hpositions block).symm
        _ = i := hleftIdx
    have hrightBound : right.idxOf leftValue < right.length := by
      rw [hrightIdx]
      exact hiright
    have hrightGet : rightValue = leftValue := by
      simpa [rightValue, hrightIdx] using List.idxOf_get hrightBound
    exact hrightGet.symm
  · by_cases hrightNonempty : rightValue.Nonempty
    · have hrightKeep : decide rightValue.Nonempty = true := by simp [hrightNonempty]
      have hrightFilter : rightValue ∈
          right.filter fun direct => decide direct.Nonempty := by
        exact List.mem_filter.mpr ⟨List.get_mem right ⟨i, hiright⟩, hrightKeep⟩
      have hrightInBlocks : rightValue ∈ blocks.toList :=
        hrightBlocks.mem_iff.mp hrightFilter
      let block : ↥blocks := ⟨rightValue, by simpa using hrightInBlocks⟩
      have hrightIdx : right.idxOf rightValue = i :=
        idxOf_get_eq_of_filter_nodup
          (fun direct : Finset (Index J noiseDim) => decide direct.Nonempty)
          right rightValue i hiright rfl hrightNodup hrightKeep
      have hleftIdx : left.idxOf rightValue = i := by
        calc
          left.idxOf rightValue = right.idxOf rightValue := by
            simpa [block] using hpositions block
          _ = i := hrightIdx
      have hleftBound : left.idxOf rightValue < left.length := by
        rw [hleftIdx]
        exact hileft
      have hleftGet : leftValue = rightValue := by
        simpa [leftValue, hleftIdx] using List.idxOf_get hleftBound
      exact False.elim (hleftNonempty (hleftGet.symm ▸ hrightNonempty))
    · have hleftEmpty : leftValue = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hleftNonempty
      have hrightEmpty : rightValue = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hrightNonempty
      change leftValue = rightValue
      rw [hleftEmpty, hrightEmpty]

/-- The concrete Catalan shape-and-label pattern attached to an ordered occurrence. -/
noncomputable def orderedPayoffOccurrencePattern {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList)
    (hvertices : ∀ tree ∈ family,
      tree.vertexCount ≤ 2 * blocks.card)
    (occurrence : OrderedPayoffOccurrence family) :
    BoundedPlaneLabelPattern (↥blocks) blocks.card := by
  let tree := occurrence.1.1
  let variant := occurrence.variant
  have hvariant : variant ∈ tree.orderedVersions :=
    occurrence.variant_mem_orderedVersions
  have htreeBlocks : tree.nonemptyDirectLabels.Perm blocks.toList :=
    hblocks tree occurrence.1.2
  have hnodeBound : variant.planeCode.numNodes < 2 * blocks.card := by
    have htreeVertex := hvertices tree occurrence.1.2
    have hvariantVertex := tree.vertexCount_eq_of_mem_orderedVersions variant hvariant
    have hcodeNodes := variant.numNodes_planeCode
    omega
  let n : Fin (2 * blocks.card) := ⟨variant.planeCode.numNodes, hnodeBound⟩
  exact ⟨n, {
    shape := ⟨variant.planeCode.map (Function.const _ ()), by
      apply BinaryTree.mem_treesOfNumNodesEq.mpr
      simp [n]⟩
    placement := payoffBlockPlacement blocks tree variant hvariant htreeBlocks }⟩

@[simp]
theorem orderedPayoffOccurrencePattern_shape_val {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList)
    (hvertices : ∀ tree ∈ family,
      tree.vertexCount ≤ 2 * blocks.card)
    (occurrence : OrderedPayoffOccurrence family) :
    (orderedPayoffOccurrencePattern family blocks hblocks hvertices occurrence).2.shape.1 =
      occurrence.variant.planeCode.map (Function.const _ ()) := rfl

@[simp]
theorem orderedPayoffOccurrencePattern_placement_val {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList)
    (hvertices : ∀ tree ∈ family,
      tree.vertexCount ≤ 2 * blocks.card)
    (occurrence : OrderedPayoffOccurrence family)
    (block : ↥blocks) :
    ((orderedPayoffOccurrencePattern family blocks hblocks hvertices occurrence).2.placement
      block).val = occurrence.variant.driftDirectLabels.idxOf block.1 := rfl

/-- Equal Catalan patterns recover both the ordered plane tree and its canonical source. -/
theorem orderedPayoffOccurrencePattern_recovers_source_and_variant
    {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (support root : Finset (Index J noiseDim))
    (hvalid : ∀ tree ∈ family, tree.Valid support)
    (hroot : ∀ tree ∈ family, tree.direct = root)
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList)
    (hvertices : ∀ tree ∈ family,
      tree.vertexCount ≤ 2 * blocks.card)
    (left right : OrderedPayoffOccurrence family)
    (hpattern :
      orderedPayoffOccurrencePattern family blocks hblocks hvertices left =
        orderedPayoffOccurrencePattern family blocks hblocks hvertices right) :
    left.1.1 = right.1.1 ∧ left.variant = right.variant := by
  have hshape :
      left.variant.planeCode.map (Function.const _ ()) =
        right.variant.planeCode.map (Function.const _ ()) := by
    simpa using congrArg (fun pattern => pattern.2.shape.1) hpattern
  have hnodeCount :
      left.variant.planeCode.numNodes = right.variant.planeCode.numNodes := by
    have := congrArg BinaryTree.numNodes hshape
    simpa using this
  have hlength :
      left.variant.driftDirectLabels.length =
        right.variant.driftDirectLabels.length := by
    calc
      left.variant.driftDirectLabels.length =
          left.variant.planeCode.numNodes := by
        rw [← left.variant.binaryTreePreorder_planeCode,
          BinaryTree.length_preorder]
      _ = right.variant.planeCode.numNodes := hnodeCount
      _ = right.variant.driftDirectLabels.length := by
        rw [← right.variant.binaryTreePreorder_planeCode,
          BinaryTree.length_preorder]
  have hpositions : ∀ block : ↥blocks,
      left.variant.driftDirectLabels.idxOf block.1 =
        right.variant.driftDirectLabels.idxOf block.1 := by
    intro block
    have hfunctions := congrArg
      (fun pattern => fun block : ↥blocks => pattern.2.placement block |>.val)
      hpattern
    simpa using congrFun hfunctions block
  have hleftVariantMem : left.variant ∈ left.1.1.orderedVersions :=
    left.variant_mem_orderedVersions
  have hrightVariantMem : right.variant ∈ right.1.1.orderedVersions :=
    right.variant_mem_orderedVersions
  have hleftVariantBlocks :
      left.variant.nonemptyDirectLabels.Perm blocks.toList :=
    (left.1.1.nonemptyDirectLabels_perm_of_mem_orderedVersions
      left.variant hleftVariantMem).trans (hblocks left.1.1 left.1.2)
  have hrightVariantBlocks :
      right.variant.nonemptyDirectLabels.Perm blocks.toList :=
    (right.1.1.nonemptyDirectLabels_perm_of_mem_orderedVersions
      right.variant hrightVariantMem).trans (hblocks right.1.1 right.1.2)
  have hlabels :
      left.variant.driftDirectLabels = right.variant.driftDirectLabels :=
    driftDirectLabels_eq_of_blockPositions_eq blocks
      left.variant.driftDirectLabels right.variant.driftDirectLabels
      hlength hleftVariantBlocks hrightVariantBlocks hpositions
  have hcode : left.variant.planeCode = right.variant.planeCode :=
    BinaryTree.eq_of_map_const_eq_of_preorder_eq hshape (by
      rw [left.variant.binaryTreePreorder_planeCode,
        right.variant.binaryTreePreorder_planeCode]
      exact hlabels)
  have hdirect : left.variant.direct = right.variant.direct := by
    calc
      left.variant.direct = left.1.1.direct :=
        left.1.1.direct_eq_of_mem_orderedVersions left.variant hleftVariantMem
      _ = root := hroot left.1.1 left.1.2
      _ = right.1.1.direct := (hroot right.1.1 right.1.2).symm
      _ = right.variant.direct :=
        (right.1.1.direct_eq_of_mem_orderedVersions
          right.variant hrightVariantMem).symm
  have hvariant : left.variant = right.variant :=
    PayoffTreeData.eq_of_direct_eq_of_planeCode_eq hdirect hcode
  have hsource : left.1.1 = right.1.1 := by
    apply PayoffTreeData.eq_of_valid_of_common_orderedVersion
      (hvalid left.1.1 left.1.2) (hvalid right.1.1 right.1.2)
      hleftVariantMem
    rw [hvariant]
    exact hrightVariantMem
  exact ⟨hsource, hvariant⟩

/-- The concrete injection used in the Catalan count of paper Lemma B.7. -/
noncomputable def orderedPayoffOccurrenceEmbedding
    {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (support root : Finset (Index J noiseDim))
    (hvalid : ∀ tree ∈ family, tree.Valid support)
    (hroot : ∀ tree ∈ family, tree.direct = root)
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList)
    (hvertices : ∀ tree ∈ family,
      tree.vertexCount ≤ 2 * blocks.card) :
    OrderedPayoffOccurrence family ↪
      BoundedPlaneLabelPattern (↥blocks) blocks.card := by
  refine ⟨orderedPayoffOccurrencePattern family blocks hblocks hvertices, ?_⟩
  intro left right hpattern
  have hrecovered := orderedPayoffOccurrencePattern_recovers_source_and_variant
    family blocks support root hvalid hroot hblocks hvertices left right hpattern
  rcases hrecovered with ⟨hsource, hvariant⟩
  have htreeSubtype : left.1 = right.1 := Subtype.ext hsource
  cases left with
  | mk leftTree leftIndex =>
      cases right with
      | mk rightTree rightIndex =>
          simp only at htreeSubtype
          subst rightTree
          have hget :
              leftTree.1.orderedVersions.get
                  (Fin.cast
                    leftTree.1.length_orderedVersions_eq_childFactorialProduct.symm
                    leftIndex) =
                leftTree.1.orderedVersions.get
                  (Fin.cast
                    leftTree.1.length_orderedVersions_eq_childFactorialProduct.symm
                    rightIndex) := by
            simpa [OrderedPayoffOccurrence.variant] using hvariant
          have hcast :
              Fin.cast
                  leftTree.1.length_orderedVersions_eq_childFactorialProduct.symm
                  leftIndex =
                Fin.cast
                  leftTree.1.length_orderedVersions_eq_childFactorialProduct.symm
                  rightIndex :=
            (leftTree.1.orderedVersions_nodup_of_valid
              (hvalid leftTree.1 leftTree.2)).get_inj_iff.mp hget
          have hindex : leftIndex = rightIndex := by
            apply Fin.ext
            simpa using congrArg Fin.val hcast
          subst rightIndex
          rfl

/-- Paper Lemma B.7: the weighted number of canonical payoff trees is controlled by the
Catalan shape count, with no abstract encoding hypothesis remaining. -/
theorem weighted_payoffTree_count
    {J noiseDim : ℕ}
    (family : Finset (PayoffTreeData J noiseDim))
    (blocks : Finset (Finset (Index J noiseDim)))
    (support root : Finset (Index J noiseDim))
    (hvalid : ∀ tree ∈ family, tree.Valid support)
    (hroot : ∀ tree ∈ family, tree.direct = root)
    (hblocks : ∀ tree ∈ family,
      tree.nonemptyDirectLabels.Perm blocks.toList)
    (hvertices : ∀ tree ∈ family,
      tree.vertexCount ≤ 2 * blocks.card) :
    ∑ tree ∈ family, tree.childFactorialProduct ≤
      64 ^ blocks.card * blocks.card.factorial := by
  classical
  apply weighted_payoffTree_count_of_planeEncoding
    family (↥blocks) blocks.card
  · simp
  · exact orderedPayoffOccurrenceEmbedding
      family blocks support root hvalid hroot hblocks hvertices

end

end TimeDependentLattice.Trees
