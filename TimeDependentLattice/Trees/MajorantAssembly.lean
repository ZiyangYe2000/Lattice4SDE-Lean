/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Trees.Correspondence
import TimeDependentLattice.Trees.TimeFactorBound
import TimeDependentLattice.Trees.DerivativeExpansion

/-!
# Assembly of the derivative tree majorant

This file groups admissible timed payoff trees by the paper's pair `(E, π)`, where `E` is the
direct endpoint label at the payoff root and `π` is the partition formed by all nonempty direct
labels below the root.
-/

namespace TimeDependentLattice.Trees

noncomputable section

open scoped BigOperators
open TimeDependentLattice.Analysis
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Euler
open TimeDependentLattice.Regularity
open GevreyBounds

/-- Simplified form `64 K^6 max(1,T)` of the paper's `C_maj`.
`GevreyBounds.majorantConstant_eq_paper_formula` in `Trees/PaperConstants.lean`
identifies it with the paper's full maximum. -/
def GevreyBounds.majorantConstant
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) : ℝ :=
  64 * bounds.coefficientCountBase * max 1 T

theorem GevreyBounds.one_le_majorantConstant
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) :
    1 ≤ bounds.majorantConstant := by
  have hK : 1 ≤ bounds.coefficientCountBase := by
    exact one_le_pow₀ bounds.one_le_coefficientBase
  have hT : 1 ≤ max 1 T := le_max_left _ _
  dsimp [GevreyBounds.majorantConstant]
  nlinarith

theorem GevreyBounds.coefficient_time_count_le_majorantConstant_pow
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (supportCard blockCard : ℕ) :
    max 1 T ^ blockCard *
        bounds.coefficientCountBase ^ (supportCard + blockCard) *
        (64 : ℝ) ^ blockCard ≤
      bounds.majorantConstant ^ (supportCard + blockCard) := by
  let M : ℝ := 64 * max 1 T
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith [show (1 : ℝ) ≤ max 1 T from le_max_left _ _]
  have hK : 0 ≤ bounds.coefficientCountBase :=
    zero_le_one.trans (one_le_pow₀ bounds.one_le_coefficientBase)
  have hMpow : M ^ blockCard ≤ M ^ (supportCard + blockCard) :=
    pow_le_pow_right₀ hM (Nat.le_add_left blockCard supportCard)
  calc
    max 1 T ^ blockCard *
        bounds.coefficientCountBase ^ (supportCard + blockCard) *
        (64 : ℝ) ^ blockCard =
      bounds.coefficientCountBase ^ (supportCard + blockCard) * M ^ blockCard := by
        dsimp [M]
        rw [mul_pow]
        ring
    _ ≤ bounds.coefficientCountBase ^ (supportCard + blockCard) *
        M ^ (supportCard + blockCard) :=
      mul_le_mul_of_nonneg_left hMpow (pow_nonneg hK _)
    _ = bounds.majorantConstant ^ (supportCard + blockCard) := by
      rw [← mul_pow]
      dsimp [M, GevreyBounds.majorantConstant]
      congr 1
      ring

/-- The root-only payoff coefficient is absorbed by the same geometric constant as soon as the
mixed derivative support is nonempty. -/
theorem GevreyBounds.rootCoefficient_le_majorantConstant_pow
    {stateDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (n : ℕ) (hn : 0 < n) :
    bounds.G₀ * bounds.G₁ ^ n ≤ bounds.majorantConstant ^ n := by
  have hK : 0 ≤ bounds.coefficientBase :=
    zero_le_one.trans bounds.one_le_coefficientBase
  have hcoefficientCount : 0 ≤ bounds.coefficientCountBase := by
    exact pow_nonneg hK _
  have hfactor : (1 : ℝ) ≤ 64 * max 1 T := by
    nlinarith [show (1 : ℝ) ≤ max 1 T from le_max_left _ _]
  have hcountMajorant : bounds.coefficientCountBase ≤ bounds.majorantConstant := by
    calc
      bounds.coefficientCountBase ≤
          bounds.coefficientCountBase * (64 * max 1 T) :=
        le_mul_of_one_le_right hcoefficientCount hfactor
      _ = bounds.majorantConstant := by
        dsimp [GevreyBounds.majorantConstant]
        ring
  have hpayoff : bounds.G₀ * bounds.G₁ ^ n ≤
      bounds.coefficientBase * bounds.coefficientBase ^ n :=
    mul_le_mul bounds.G₀_le_coefficientBase
      (pow_le_pow_left₀ bounds.G₁_pos.le bounds.G₁_le_coefficientBase n)
      (pow_nonneg bounds.G₁_pos.le n) hK
  calc
    bounds.G₀ * bounds.G₁ ^ n ≤
        bounds.coefficientBase * bounds.coefficientBase ^ n := hpayoff
    _ = bounds.coefficientBase ^ (n + 1) := by rw [pow_succ']
    _ ≤ bounds.coefficientBase ^ (6 * n) := by
      apply pow_le_pow_right₀ bounds.one_le_coefficientBase
      omega
    _ = bounds.coefficientCountBase ^ n := by
      simp [GevreyBounds.coefficientCountBase, pow_mul]
    _ ≤ bounds.majorantConstant ^ n :=
      pow_le_pow_left₀ hcoefficientCount hcountMajorant n

/-- Root direct sets allowed by the payoff-tree definition: endpoint subsets of the support. -/
abbrev EndpointRoot {J noiseDim : ℕ} (support : Finset (Index J noiseDim)) :=
  ↥((support.filter IsEndpoint).powerset)

/-- The root direct set of a valid timed payoff tree, with its endpoint-subset proof. -/
def TimedPayoffTree.endpointRoot
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (timed : TimedPayoffTree J noiseDim support m) : EndpointRoot support := by
  refine ⟨timed.tree.data.direct, Finset.mem_powerset.mpr ?_⟩
  intro coordinate hcoordinate
  apply Finset.mem_filter.mpr
  constructor
  · rw [← timed.tree.valid.1]
    unfold PayoffTreeData.support
    exact Finset.mem_union_left _ hcoordinate
  · exact timed.tree.valid.2.1 coordinate hcoordinate

/-- The finite key space used to group the tree expansion by `(E, π)`. -/
abbrev MajorantKey {J noiseDim : ℕ} (support : Finset (Index J noiseDim)) :=
  Σ root : EndpointRoot support, Finpartition (support \ root.1)

/-- The paper's pair `(S(y_*), Π(𝔗))` attached to a timed payoff tree. -/
def TimedPayoffTree.majorantKey
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (timed : TimedPayoffTree J noiseDim support m) : MajorantKey support :=
  ⟨timed.endpointRoot, timed.tree.nonemptyDirectPartition⟩

/-- The finite family of underlying canonical tree shapes in one fixed `(E, π)` fiber. -/
def fixedKeyTreeFamily
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) : Finset (PayoffTreeData J noiseDim) := by
  classical
  exact (Finset.univ.filter fun timed : TimedPayoffTree J noiseDim support m ↦
      timed.majorantKey = key).image fun timed ↦ timed.tree.data

theorem fixedKeyTreeFamily_valid
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) (tree : PayoffTreeData J noiseDim)
    (htree : tree ∈ fixedKeyTreeFamily (m := m) key) :
    tree.Valid support := by
  classical
  unfold fixedKeyTreeFamily at htree
  rcases Finset.mem_image.mp htree with ⟨timed, htimed, rfl⟩
  exact timed.tree.valid

theorem fixedKeyTreeFamily_root
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) (tree : PayoffTreeData J noiseDim)
    (htree : tree ∈ fixedKeyTreeFamily (m := m) key) :
    tree.direct = key.1.1 := by
  classical
  unfold fixedKeyTreeFamily at htree
  rcases Finset.mem_image.mp htree with ⟨timed, htimed, rfl⟩
  have hkey := (Finset.mem_filter.mp htimed).2
  exact congrArg (fun candidate : MajorantKey support ↦ candidate.1.1) hkey

theorem fixedKeyTreeFamily_blocks
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) (tree : PayoffTreeData J noiseDim)
    (htree : tree ∈ fixedKeyTreeFamily (m := m) key) :
    tree.nonemptyDirectLabels.Perm key.2.parts.toList := by
  classical
  unfold fixedKeyTreeFamily at htree
  rcases Finset.mem_image.mp htree with ⟨timed, htimed, rfl⟩
  have hkey := (Finset.mem_filter.mp htimed).2
  cases hkey
  exact timed.tree.nonemptyDirectLabels_perm_partitionParts

/-- Timed trees in a fixed `(E, π)` fiber. -/
abbrev FixedKeyTimedTree
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) :=
  {timed : TimedPayoffTree J noiseDim support m // timed.majorantKey = key}

noncomputable instance instFintypeFixedKeyTimedTree
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) : Fintype (FixedKeyTimedTree (m := m) key) := by
  classical
  exact Fintype.ofFinite _

/-- A tree shape in the fixed fiber, together with one valid time assignment. -/
abbrev FixedKeyFamilyAssignment
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) :=
  Σ tree : ↥(fixedKeyTreeFamily (J := J) (noiseDim := noiseDim) (m := m) key),
    {assignment : TimeAssignment // assignment.Valid m tree.1}

/-- Forget the labelled wrapper while retaining the valid assignment. -/
def fixedKeyFamilyAssignment
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    {key : MajorantKey support} (timed : FixedKeyTimedTree (m := m) key) :
    FixedKeyFamilyAssignment (m := m) key := by
  classical
  refine ⟨⟨timed.1.tree.data, ?_⟩,
    ⟨timed.1.assignment, timed.1.assignmentValid⟩⟩
  unfold fixedKeyTreeFamily
  apply Finset.mem_image.mpr
  exact ⟨timed.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, timed.2⟩, rfl⟩

theorem fixedKeyFamilyAssignment_injective
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    {key : MajorantKey support} :
    Function.Injective (fixedKeyFamilyAssignment (m := m) (key := key)) := by
  intro left right heq
  apply Subtype.ext
  apply TimedPayoffTree.ext
  · apply LabelledPayoffTree.ext
    exact congrArg (fun pair : FixedKeyFamilyAssignment (m := m) key ↦
      pair.1.1) heq
  · exact congrArg (fun pair : FixedKeyFamilyAssignment (m := m) key ↦
      pair.2.1) heq

/-- Reindexing a fixed timed-tree fiber into shape/assignment pairs can only enlarge the sum,
because the target also contains every other valid assignment of each occurring shape. -/
theorem fixedKey_factored_sum_le_family_sum
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    {support : Finset (Index J noiseDim)}
    (key : MajorantKey support) :
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      ∑ tree ∈ fixedKeyTreeFamily (m := numSteps J) key,
        ∑ assignment : {assignment : TimeAssignment //
            assignment.Valid (numSteps J) tree},
          stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
            PayoffTreeData.analyticCoefficient bounds diffusion tree *
            payoffTreeNonrootDirectionProduct diffusion T tree assignment.1 := by
  let embed : FixedKeyTimedTree (m := numSteps J) key →
      FixedKeyFamilyAssignment (m := numSteps J) key :=
    fixedKeyFamilyAssignment
  let weight : FixedKeyFamilyAssignment (m := numSteps J) key → ℝ := fun pair ↦
    stepSize T J ^ (pair.1.1.children.map DriftTreeData.vertexCount).sum *
      PayoffTreeData.analyticCoefficient bounds diffusion pair.1.1 *
      payoffTreeNonrootDirectionProduct diffusion T pair.1.1 pair.2.1
  have hembed : Function.Injective embed := fixedKeyFamilyAssignment_injective
  have hnonneg : ∀ pair : FixedKeyFamilyAssignment (m := numSteps J) key,
      0 ≤ weight pair := by
    intro pair
    have hdirection : 0 ≤ payoffTreeNonrootDirectionProduct diffusion T
        pair.1.1 pair.2.1 := by
      rw [payoffTreeNonrootDirectionProduct_eq_encoding diffusion T
        pair.1.1 pair.2.1 pair.2.2]
      positivity
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (stepSize_nonneg hT J) _)
        (GevreyBounds.PayoffTreeData.analyticCoefficient_nonneg
          bounds diffusion pair.1.1))
      hdirection
  calc
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) =
      ∑ timed : FixedKeyTimedTree (m := numSteps J) key, weight (embed timed) := by
        apply Fintype.sum_congr
        intro timed
        rfl
    _ = ∑ pair ∈ Finset.image embed Finset.univ, weight pair := by
      symm
      exact Finset.sum_image (Set.injOn_of_injective hembed)
    _ ≤ ∑ pair : FixedKeyFamilyAssignment (m := numSteps J) key,
        weight pair := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro pair _ _
      exact hnonneg pair
    _ = ∑ tree ∈ fixedKeyTreeFamily (m := numSteps J) key,
        ∑ assignment : {assignment : TimeAssignment //
            assignment.Valid (numSteps J) tree},
          stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
            PayoffTreeData.analyticCoefficient bounds diffusion tree *
            payoffTreeNonrootDirectionProduct diffusion T tree assignment.1 := by
      rw [Fintype.sum_sigma]
      symm
      exact Finset.sum_subtype _ (by simp) _

/-- Bound for one nontrivial `(E, π)` fiber of timed payoff trees. -/
theorem fixedKey_factored_sum_le
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    {support : Finset (Index J noiseDim)}
    (key : MajorantKey support) (hparts : key.2.parts.Nonempty) :
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      (max 1 T ^ key.2.parts.card *
          ∏ block ∈ key.2.parts, eta diffusion T block) *
        (bounds.coefficientCountBase ^ (support.card + key.2.parts.card) *
          ((key.1.1.card.factorial : ℝ) ^ bounds.τ *
            ∏ j ∈ key.1.1, ‖diffusionCoefficient diffusion T j T‖) *
          (∏ block ∈ key.2.parts,
            (block.card.factorial : ℝ) ^ bounds.τ) *
          (64 : ℝ) ^ key.2.parts.card *
          (key.2.parts.card.factorial : ℝ) ^ bounds.τ) := by
  calc
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      ∑ tree ∈ fixedKeyTreeFamily (m := numSteps J) key,
        ∑ assignment : {assignment : TimeAssignment //
            assignment.Valid (numSteps J) tree},
          stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
            PayoffTreeData.analyticCoefficient bounds diffusion tree *
            payoffTreeNonrootDirectionProduct diffusion T tree assignment.1 :=
      fixedKey_factored_sum_le_family_sum bounds diffusion hT key
    _ ≤ _ := fixedPartition_factoredMajorant_sum_le bounds diffusion hT
      (fixedKeyTreeFamily (m := numSteps J) key) key.2.parts support key.1.1
      hparts
      (fun tree htree ↦ fixedKeyTreeFamily_valid key tree htree)
      (fun tree htree ↦ fixedKeyTreeFamily_root key tree htree)
      (fun tree htree ↦ fixedKeyTreeFamily_blocks key tree htree)

/-- The nontrivial fixed-key estimate after absorbing the tree, coefficient, and time-counting
geometric factors into `majorantConstant`.  The remaining factors are exactly the root factor,
the block factorials, and the paper's time weights. -/
theorem fixedKey_factored_sum_le_majorantConstant
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    {support : Finset (Index J noiseDim)}
    (key : MajorantKey support) (hparts : key.2.parts.Nonempty) :
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      bounds.majorantConstant ^ (support.card + key.2.parts.card) *
        ((key.1.1.card.factorial : ℝ) ^ bounds.τ *
          ∏ j ∈ key.1.1, ‖diffusionCoefficient diffusion T j T‖) *
        (key.2.parts.card.factorial : ℝ) ^ bounds.τ *
        ∏ block ∈ key.2.parts,
          (block.card.factorial : ℝ) ^ bounds.τ * eta diffusion T block := by
  let rootFactor : ℝ :=
    (key.1.1.card.factorial : ℝ) ^ bounds.τ *
      ∏ j ∈ key.1.1, ‖diffusionCoefficient diffusion T j T‖
  let blockFactor : ℝ :=
    ∏ block ∈ key.2.parts, (block.card.factorial : ℝ) ^ bounds.τ
  let etaFactor : ℝ := ∏ block ∈ key.2.parts, eta diffusion T block
  let countFactor : ℝ := (key.2.parts.card.factorial : ℝ) ^ bounds.τ
  have hroot : 0 ≤ rootFactor := by
    dsimp [rootFactor]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  have hblock : 0 ≤ blockFactor := by
    dsimp [blockFactor]
    exact Finset.prod_nonneg fun _ _ ↦ Real.rpow_nonneg (by positivity) _
  have heta : 0 ≤ etaFactor := by
    dsimp [etaFactor]
    exact Finset.prod_nonneg fun block _ ↦ eta_nonneg diffusion hT block
  have hcount : 0 ≤ countFactor := by
    dsimp [countFactor]
    exact Real.rpow_nonneg (by positivity) _
  have hgeometric := bounds.coefficient_time_count_le_majorantConstant_pow
    support.card key.2.parts.card
  calc
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      (max 1 T ^ key.2.parts.card * etaFactor) *
        (bounds.coefficientCountBase ^ (support.card + key.2.parts.card) *
          rootFactor * blockFactor * (64 : ℝ) ^ key.2.parts.card * countFactor) := by
        simpa [rootFactor, blockFactor, etaFactor, countFactor] using
          fixedKey_factored_sum_le bounds diffusion hT key hparts
    _ = (max 1 T ^ key.2.parts.card *
          bounds.coefficientCountBase ^ (support.card + key.2.parts.card) *
          (64 : ℝ) ^ key.2.parts.card) *
        (rootFactor * blockFactor * countFactor * etaFactor) := by ring
    _ ≤ bounds.majorantConstant ^ (support.card + key.2.parts.card) *
        (rootFactor * blockFactor * countFactor * etaFactor) :=
      mul_le_mul_of_nonneg_right hgeometric
        (mul_nonneg (mul_nonneg (mul_nonneg hroot hblock) hcount) heta)
    _ = bounds.majorantConstant ^ (support.card + key.2.parts.card) *
        rootFactor * countFactor *
        ∏ block ∈ key.2.parts,
          (block.card.factorial : ℝ) ^ bounds.τ * eta diffusion T block := by
      rw [Finset.prod_mul_distrib]
      dsimp [rootFactor, blockFactor, etaFactor, countFactor]
      ring

/-- An empty partition fiber has root direct set equal to the whole support. -/
theorem MajorantKey.root_eq_support_of_parts_empty
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (key : MajorantKey support) (hparts : key.2.parts = ∅) :
    key.1.1 = support := by
  have hdiff : support \ key.1.1 = ∅ := by
    rw [← key.2.sup_parts, hparts]
    simp
  have hsupportRoot : support ⊆ key.1.1 :=
    Finset.sdiff_eq_empty_iff_subset.mp hdiff
  have hrootSupport : key.1.1 ⊆ support := by
    have hfiltered := Finset.mem_powerset.mp key.1.2
    intro coordinate hcoordinate
    exact (Finset.mem_filter.mp (hfiltered hcoordinate)).1
  exact Finset.Subset.antisymm hrootSupport hsupportRoot

/-- Every shape in an empty-partition fiber is the root-only shape. -/
theorem fixedKeyTreeFamily_eq_rootOnly_of_parts_empty
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)} {m : ℕ}
    (key : MajorantKey support) (hparts : key.2.parts = ∅)
    (tree : PayoffTreeData J noiseDim)
    (htree : tree ∈ fixedKeyTreeFamily (m := m) key) :
    tree = PayoffTreeData.mk support [] := by
  have hvalid := fixedKeyTreeFamily_valid key tree htree
  have hroot := fixedKeyTreeFamily_root key tree htree
  rw [key.root_eq_support_of_parts_empty hparts] at hroot
  have hlabelsPerm := fixedKeyTreeFamily_blocks key tree htree
  rw [hparts] at hlabelsPerm
  simp only [Finset.toList_empty] at hlabelsPerm
  have hlabels : tree.nonemptyDirectLabels = [] := hlabelsPerm.eq_nil
  have hchildren :=
    tree.valid_children_eq_nil_of_nonemptyDirectLabels_eq_nil hvalid hlabels
  cases tree
  simp_all

/-- Bound for the exceptional empty-partition fiber, consisting only of the payoff root. -/
theorem fixedKey_factored_sum_le_of_parts_empty
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    {support : Finset (Index J noiseDim)}
    (key : MajorantKey support) (hparts : key.2.parts = ∅) :
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      (bounds.G₀ * bounds.G₁ ^ support.card *
          (support.card.factorial : ℝ) ^ bounds.τ) *
        ∏ j ∈ support, ‖diffusionCoefficient diffusion T j T‖ := by
  let rootData : PayoffTreeData J noiseDim := PayoffTreeData.mk support []
  let familyWeight : PayoffTreeData J noiseDim → ℝ := fun tree ↦
    ∑ assignment : {assignment : TimeAssignment //
        assignment.Valid (numSteps J) tree},
      stepSize T J ^ (tree.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion tree *
        payoffTreeNonrootDirectionProduct diffusion T tree assignment.1
  have hfamilySubset : fixedKeyTreeFamily (m := numSteps J) key ⊆ {rootData} := by
    intro tree htree
    rw [Finset.mem_singleton]
    exact fixedKeyTreeFamily_eq_rootOnly_of_parts_empty key hparts tree htree
  have hrootWeight : familyWeight rootData =
      (bounds.G₀ * bounds.G₁ ^ support.card *
          (support.card.factorial : ℝ) ^ bounds.τ) *
        ∏ j ∈ support, ‖diffusionCoefficient diffusion T j T‖ := by
    let rootAssignment : {assignment : TimeAssignment //
        assignment.Valid (numSteps J) rootData} :=
      ⟨TimeAssignment.rootOnly (numSteps J),
        TimeAssignment.rootOnly_valid (numSteps J) support⟩
    letI : Unique {assignment : TimeAssignment //
        assignment.Valid (numSteps J) rootData} :=
      { default := rootAssignment
        uniq := fun assignment ↦ by
          apply Subtype.ext
          exact TimeAssignment.eq_rootOnly_of_valid support
            assignment.1 assignment.2 }
    dsimp [familyWeight]
    rw [Fintype.sum_unique]
    simp [rootData, rootAssignment, PayoffTreeData.analyticCoefficient,
      payoffTreeNonrootDirectionProduct, TimeAssignment.rootOnly,
      driftTreeDirectionProducts]
  calc
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      ∑ tree ∈ fixedKeyTreeFamily (m := numSteps J) key, familyWeight tree := by
        simpa [familyWeight] using
          (fixedKey_factored_sum_le_family_sum bounds diffusion hT key)
    _ ≤ ∑ tree ∈ ({rootData} : Finset (PayoffTreeData J noiseDim)),
        familyWeight tree := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hfamilySubset
      intro tree htree _
      rw [Finset.mem_singleton.mp htree, hrootWeight]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg bounds.G₀_pos.le (pow_nonneg bounds.G₁_pos.le _))
          (Real.rpow_nonneg (by positivity) _))
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    _ = _ := by simp [hrootWeight]

/-- Root-only version of the fixed-key majorant, expressed with the common geometric constant. -/
theorem fixedKey_factored_sum_le_majorantConstant_of_parts_empty
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    {support : Finset (Index J noiseDim)} (hsupport : support.Nonempty)
    (key : MajorantKey support) (hparts : key.2.parts = ∅) :
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      bounds.majorantConstant ^ support.card *
        ((support.card.factorial : ℝ) ^ bounds.τ *
          ∏ j ∈ support, ‖diffusionCoefficient diffusion T j T‖) := by
  have hcoefficient := bounds.rootCoefficient_le_majorantConstant_pow
    support.card (Finset.card_pos.mpr hsupport)
  have hfactor : 0 ≤
      (support.card.factorial : ℝ) ^ bounds.τ *
        ∏ j ∈ support, ‖diffusionCoefficient diffusion T j T‖ :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  calc
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤
      (bounds.G₀ * bounds.G₁ ^ support.card *
          (support.card.factorial : ℝ) ^ bounds.τ) *
        ∏ j ∈ support, ‖diffusionCoefficient diffusion T j T‖ :=
      fixedKey_factored_sum_le_of_parts_empty bounds diffusion hT key hparts
    _ = (bounds.G₀ * bounds.G₁ ^ support.card) *
        ((support.card.factorial : ℝ) ^ bounds.τ *
          ∏ j ∈ support, ‖diffusionCoefficient diffusion T j T‖) := by ring
    _ ≤ bounds.majorantConstant ^ support.card *
        ((support.card.factorial : ℝ) ^ bounds.τ *
          ∏ j ∈ support, ‖diffusionCoefficient diffusion T j T‖) :=
      mul_le_mul_of_nonneg_right hcoefficient hfactor

/-- The paper majorant attached to a root set and an unordered partition of its complement. -/
def keyMajorant
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim)
    {support : Finset (Index J noiseDim)} (key : MajorantKey support) : ℝ :=
  bounds.majorantConstant ^ (support.card + key.2.parts.card) *
    ((key.1.1.card.factorial : ℝ) ^ bounds.τ *
      ∏ j ∈ key.1.1, ‖diffusionCoefficient diffusion T j T‖) *
    (key.2.parts.card.factorial : ℝ) ^ bounds.τ *
    ∏ block ∈ key.2.parts,
      (block.card.factorial : ℝ) ^ bounds.τ * eta diffusion T block

theorem keyMajorant_nonneg
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    {support : Finset (Index J noiseDim)} (key : MajorantKey support) :
    0 ≤ keyMajorant bounds diffusion key := by
  unfold keyMajorant
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) _
      · exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    · exact Real.rpow_nonneg (by positivity) _
  · apply Finset.prod_nonneg
    intro block hblock
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (eta_nonneg diffusion hT block)

/-- Both the nontrivial and the root-only fixed-key estimates have the same final form. -/
theorem fixedKey_factored_sum_le_keyMajorant
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    {support : Finset (Index J noiseDim)} (hsupport : support.Nonempty)
    (key : MajorantKey support) :
    (∑ timed : FixedKeyTimedTree (m := numSteps J) key,
      stepSize T J ^
          (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
          timed.1.assignment) ≤ keyMajorant bounds diffusion key := by
  by_cases hparts : key.2.parts = ∅
  · have hroot := key.root_eq_support_of_parts_empty hparts
    simpa [keyMajorant, hparts, hroot] using
      fixedKey_factored_sum_le_majorantConstant_of_parts_empty
        bounds diffusion hT hsupport key hparts
  · exact fixedKey_factored_sum_le_majorantConstant bounds diffusion hT key
      (Finset.nonempty_iff_ne_empty.mpr hparts)

/-- Exact regrouping of the factored timed-tree sum by the finite key `(E, π)`. -/
theorem factored_sum_eq_sum_majorantKeys
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim)
    (support : Finset (Index J noiseDim)) :
    (∑ timed : TimedPayoffTree J noiseDim support (numSteps J),
      stepSize T J ^
          (timed.tree.data.children.map DriftTreeData.vertexCount).sum *
        PayoffTreeData.analyticCoefficient bounds diffusion timed.tree.data *
        payoffTreeNonrootDirectionProduct diffusion T timed.tree.data
          timed.assignment) =
      ∑ key : MajorantKey support,
        ∑ timed : FixedKeyTimedTree (m := numSteps J) key,
          stepSize T J ^
              (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
            PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
            payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
              timed.1.assignment := by
  let sourceWeight : TimedPayoffTree J noiseDim support (numSteps J) → ℝ := fun timed ↦
    stepSize T J ^
        (timed.tree.data.children.map DriftTreeData.vertexCount).sum *
      PayoffTreeData.analyticCoefficient bounds diffusion timed.tree.data *
      payoffTreeNonrootDirectionProduct diffusion T timed.tree.data timed.assignment
  let fiberWeight : (Σ key : MajorantKey support,
      FixedKeyTimedTree (m := numSteps J) key) → ℝ := fun pair ↦
    sourceWeight pair.2.1
  let equivalence : TimedPayoffTree J noiseDim support (numSteps J) ≃
      (Σ key : MajorantKey support, FixedKeyTimedTree (m := numSteps J) key) :=
    (Equiv.sigmaFiberEquiv
      (TimedPayoffTree.majorantKey (support := support) (m := numSteps J))).symm
  change (∑ timed, sourceWeight timed) = _
  calc
    (∑ timed, sourceWeight timed) = ∑ pair, fiberWeight pair := by
      exact Fintype.sum_equiv equivalence sourceWeight fiberWeight (fun _ ↦ rfl)
    _ = ∑ key : MajorantKey support,
        ∑ timed : FixedKeyTimedTree (m := numSteps J) key,
          fiberWeight ⟨key, timed⟩ := Fintype.sum_sigma fiberWeight
    _ = _ := by rfl

/-- Triangle inequality plus the single-tree analytic estimate.  This is the point where the
exact derivative tree expansion becomes a nonnegative factored majorant. -/
theorem normalized_mixedDerivative_le_factored_sum
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty) :
    Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
        |mixedDerivative (integrand drift diffusion payoff T x₀) support z| ≤
      ∑ timed : TimedPayoffTree J noiseDim support (numSteps J),
        stepSize T J ^
            (timed.tree.data.children.map DriftTreeData.vertexCount).sum *
          PayoffTreeData.analyticCoefficient bounds diffusion timed.tree.data *
          payoffTreeNonrootDirectionProduct diffusion T timed.tree.data
            timed.assignment := by
  rw [mixedDerivative_integrand_eq_treeExpansionSum drift payoff diffusion T
    hT.ne' x₀ bounds.drift_smooth bounds.payoff_smooth z support]
  unfold treeExpansionSum
  have hexp : 0 ≤ Real.exp
      (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) :=
    (Real.exp_pos _).le
  calc
    Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
        |∑ timed : TimedPayoffTree J noiseDim support (numSteps J),
          timed.value drift payoff diffusion T x₀ z| ≤
      Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
        ∑ timed : TimedPayoffTree J noiseDim support (numSteps J),
          ‖timed.value drift payoff diffusion T x₀ z‖ := by
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hexp
    _ = ∑ timed : TimedPayoffTree J noiseDim support (numSteps J),
        Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
          ‖timed.value drift payoff diffusion T x₀ z‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ timed : TimedPayoffTree J noiseDim support (numSteps J),
        stepSize T J ^
            (timed.tree.data.children.map DriftTreeData.vertexCount).sum *
          PayoffTreeData.analyticCoefficient bounds diffusion timed.tree.data *
          payoffTreeNonrootDirectionProduct diffusion T timed.tree.data
            timed.assignment := by
      apply Finset.sum_le_sum
      intro timed _
      exact TimedPayoffTree.normalized_norm_value_le_factorized
        bounds hT.le diffusion x₀ z hsupport (le_refl (numSteps J)) timed

/-- Proposition 4.3 at the finite `(E, π)` level: the normalized mixed derivative is bounded by
the sum of the paper majorants over all endpoint roots and unordered partitions. -/
theorem normalized_mixedDerivative_le_keyMajorantSum
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (diffusion : Diffusion stateDim noiseDim) (x₀ : State stateDim)
    (z : Input J noiseDim) (support : Finset (Index J noiseDim))
    (hsupport : support.Nonempty) :
    Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
        |mixedDerivative (integrand drift diffusion payoff T x₀) support z| ≤
      ∑ key : MajorantKey support, keyMajorant bounds diffusion key := by
  calc
    Real.exp (-bounds.β * ‖terminalState drift diffusion T x₀ z‖) *
        |mixedDerivative (integrand drift diffusion payoff T x₀) support z| ≤
      ∑ timed : TimedPayoffTree J noiseDim support (numSteps J),
        stepSize T J ^
            (timed.tree.data.children.map DriftTreeData.vertexCount).sum *
          PayoffTreeData.analyticCoefficient bounds diffusion timed.tree.data *
          payoffTreeNonrootDirectionProduct diffusion T timed.tree.data
            timed.assignment :=
      normalized_mixedDerivative_le_factored_sum bounds hT diffusion x₀ z support hsupport
    _ = ∑ key : MajorantKey support,
        ∑ timed : FixedKeyTimedTree (m := numSteps J) key,
          stepSize T J ^
              (timed.1.tree.data.children.map DriftTreeData.vertexCount).sum *
            PayoffTreeData.analyticCoefficient bounds diffusion timed.1.tree.data *
            payoffTreeNonrootDirectionProduct diffusion T timed.1.tree.data
              timed.1.assignment :=
      factored_sum_eq_sum_majorantKeys bounds diffusion support
    _ ≤ ∑ key : MajorantKey support, keyMajorant bounds diffusion key := by
      apply Finset.sum_le_sum
      intro key hkey
      exact fixedKey_factored_sum_le_keyMajorant bounds diffusion hT.le hsupport key

end

end TimeDependentLattice.Trees
