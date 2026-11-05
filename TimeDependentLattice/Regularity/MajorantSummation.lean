/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Regularity.Envelope
import TimeDependentLattice.Regularity.AllSubsetSummability
import TimeDependentLattice.Regularity.PaperSummability
import TimeDependentLattice.Regularity.FiniteSums

/-!
# Summing the tree majorant

This file carries out the finite reindexing in the proof of Theorem 4.1.  A support together
with a majorant key `(E, π)` is injected into the pair consisting of the endpoint coordinates
of `E` and the unordered family of blocks of `π`.
-/

namespace TimeDependentLattice.Regularity

noncomputable section

open scoped BigOperators
open TimeDependentLattice
open TimeDependentLattice.Analysis
open TimeDependentLattice.BrownianBridge
open TimeDependentLattice.Euler
open TimeDependentLattice.Trees

/-- Recover the endpoint components occurring in a finset of full bridge indices. -/
def endpointComponents {J noiseDim : ℕ} (indices : Finset (Index J noiseDim)) :
    Finset (Fin noiseDim) :=
  Finset.univ.filter fun r ↦ Sum.inl r ∈ indices

theorem endpointIndices_endpointComponents
    {J noiseDim : ℕ} (indices : Finset (Index J noiseDim))
    (hendpoint : ∀ j ∈ indices, IsEndpoint j) :
    endpointIndices (J := J) (endpointComponents indices) = indices := by
  ext coordinate
  cases coordinate with
  | inl r => simp [endpointIndices, endpointComponents]
  | inr j =>
      constructor
      · simp [endpointIndices]
      · intro hj
        have := hendpoint (Sum.inr j) hj
        simp [IsEndpoint] at this

theorem card_endpointComponents
    {J noiseDim : ℕ} (indices : Finset (Index J noiseDim))
    (hendpoint : ∀ j ∈ indices, IsEndpoint j) :
    (endpointComponents indices).card = indices.card := by
  have heq := endpointIndices_endpointComponents indices hendpoint
  calc
    (endpointComponents indices).card =
        (endpointIndices (J := J) (endpointComponents indices)).card := by
      simp [endpointIndices]
    _ = indices.card := congrArg Finset.card heq

theorem endpoint_terminal_product_eq
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T : ℝ} (hT : 0 ≤ T) (indices : Finset (Index J noiseDim))
    (hendpoint : ∀ j ∈ indices, IsEndpoint j) :
    (∏ j ∈ indices, ‖diffusionCoefficient diffusion T j T‖) =
      ∏ r ∈ endpointComponents indices, endpointFactor diffusion T r := by
  have heq := endpointIndices_endpointComponents indices hendpoint
  have hreindex :
      (∏ j ∈ indices, ‖diffusionCoefficient diffusion T j T‖) =
        ∏ j ∈ endpointIndices (J := J) (endpointComponents indices),
          ‖diffusionCoefficient diffusion T j T‖ :=
    congrArg (fun set : Finset (Index J noiseDim) ↦
      ∏ j ∈ set, ‖diffusionCoefficient diffusion T j T‖) heq.symm
  calc
    (∏ j ∈ indices, ‖diffusionCoefficient diffusion T j T‖) =
        ∏ j ∈ endpointIndices (J := J) (endpointComponents indices),
          ‖diffusionCoefficient diffusion T j T‖ := hreindex
    _ = ∏ r ∈ endpointComponents indices, endpointFactor diffusion T r := by
      unfold endpointIndices
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro r hr
      simp [diffusionCoefficient_endpoint_terminal, endpointFactor, columnNorm,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg T)]

/-- All possible unordered families of nonempty coordinate subsets. -/
abbrev BlockFamily {J noiseDim : ℕ} :=
  ↥(((Finset.univ : Finset (Index J noiseDim)).powerset.erase ∅).powerset)

/-- The enlarged configuration space used after dropping disjointness restrictions. -/
abbrev MajorantConfiguration {J noiseDim : ℕ} :=
  Finset (Fin noiseDim) × BlockFamily (J := J) (noiseDim := noiseDim)

/-- A support together with one of its paper keys `(E, π)`. -/
abbrev GlobalMajorantKey {J noiseDim : ℕ} :=
  Σ support : Finset (Index J noiseDim), MajorantKey support

/-- Forget the support while retaining the endpoint root and the block family. -/
def globalMajorantConfiguration
    {J noiseDim : ℕ} (source : GlobalMajorantKey (J := J) (noiseDim := noiseDim)) :
    MajorantConfiguration (J := J) (noiseDim := noiseDim) := by
  let root := source.2.1.1
  refine ⟨endpointComponents root, ⟨source.2.2.parts, ?_⟩⟩
  apply Finset.mem_powerset.mpr
  intro block hblock
  apply Finset.mem_erase.mpr
  constructor
  · exact (source.2.2.nonempty_of_mem_parts hblock).ne_empty
  · apply Finset.mem_powerset.mpr
    exact Finset.subset_univ block

private theorem majorantKey_ext_underlying
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (left right : MajorantKey support)
    (hroot : left.1.1 = right.1.1)
    (hparts : left.2.parts = right.2.parts) :
    left = right := by
  rcases left with ⟨leftRoot, leftPartition⟩
  rcases right with ⟨rightRoot, rightPartition⟩
  have hrootSubtype : leftRoot = rightRoot := Subtype.ext hroot
  subst rightRoot
  congr
  exact Finpartition.ext hparts

theorem globalMajorantConfiguration_injective
    {J noiseDim : ℕ} :
    Function.Injective
      (globalMajorantConfiguration (J := J) (noiseDim := noiseDim)) := by
  rintro ⟨leftSupport, leftKey⟩ ⟨rightSupport, rightKey⟩ heq
  have hcomponents : endpointComponents leftKey.1.1 =
      endpointComponents rightKey.1.1 := congrArg Prod.fst heq
  have hleftEndpoint : ∀ j ∈ leftKey.1.1, IsEndpoint j := by
    intro j hj
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp leftKey.1.2) hj)).2
  have hrightEndpoint : ∀ j ∈ rightKey.1.1, IsEndpoint j := by
    intro j hj
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp rightKey.1.2) hj)).2
  have hroot : leftKey.1.1 = rightKey.1.1 := by
    rw [← endpointIndices_endpointComponents leftKey.1.1 hleftEndpoint,
      ← endpointIndices_endpointComponents rightKey.1.1 hrightEndpoint,
      hcomponents]
  have hparts : leftKey.2.parts = rightKey.2.parts := by
    exact congrArg (fun configuration : MajorantConfiguration (J := J)
      (noiseDim := noiseDim) ↦ configuration.2.1) heq
  have hleftRootSubset : leftKey.1.1 ⊆ leftSupport := by
    intro j hj
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp leftKey.1.2) hj)).1
  have hrightRootSubset : rightKey.1.1 ⊆ rightSupport := by
    intro j hj
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp rightKey.1.2) hj)).1
  have hsupport : leftSupport = rightSupport := by
    calc
      leftSupport = leftKey.1.1 ∪ (leftSupport \ leftKey.1.1) :=
        (Finset.union_sdiff_of_subset hleftRootSubset).symm
      _ = leftKey.1.1 ∪ leftKey.2.parts.sup id := by
        rw [leftKey.2.sup_parts]
      _ = rightKey.1.1 ∪ leftKey.2.parts.sup id := by
        exact congrArg (fun root ↦ root ∪ leftKey.2.parts.sup id) hroot
      _ = rightKey.1.1 ∪ rightKey.2.parts.sup id := by
        exact congrArg (fun parts ↦ rightKey.1.1 ∪ parts.sup id) hparts
      _ = rightKey.1.1 ∪ (rightSupport \ rightKey.1.1) := by
        rw [rightKey.2.sup_parts]
      _ = rightSupport := Finset.union_sdiff_of_subset hrightRootSubset
  apply Sigma.ext hsupport
  cases hsupport
  apply heq_of_eq
  exact majorantKey_ext_underlying leftKey rightKey hroot hparts

theorem MajorantKey.support_card_eq
    {J noiseDim : ℕ} {support : Finset (Index J noiseDim)}
    (key : MajorantKey support) :
    support.card = key.1.1.card + ∑ block ∈ key.2.parts, block.card := by
  have hrootSubset : key.1.1 ⊆ support := by
    intro j hj
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp key.1.2) hj)).1
  have hcomplement := Finset.card_sdiff_of_subset hrootSubset
  have hparts := key.2.sum_card_parts
  have hcard := Finset.card_le_card hrootSubset
  omega

private theorem rpow_natPow {x ρ : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (x ^ n) ^ ρ = (x ^ ρ) ^ n := by
  calc
    (x ^ n) ^ ρ = x ^ ((n : ℝ) * ρ) := by
      rw [← Real.rpow_natCast x n]
      exact (Real.rpow_mul hx (n : ℝ) ρ).symm
    _ = x ^ (ρ * (n : ℝ)) := by ring
    _ = (x ^ ρ) ^ (n : ℝ) := Real.rpow_mul hx ρ (n : ℝ)
    _ = (x ^ ρ) ^ n := Real.rpow_natCast _ _

/-- Endpoint weight `r(E)` from the proof of Theorem 4.1. -/
def endpointMajorantWeight
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A τ ρ : ℝ) (endpoints : Finset (Fin noiseDim)) : ℝ :=
  A ^ endpoints.card * (endpoints.card.factorial : ℝ) ^ (τ * ρ) *
    ∏ r ∈ endpoints, endpointFactor diffusion T r ^ ρ

/-- Block weight `w(S)` from the proof of Theorem 4.1. -/
def blockMajorantWeight
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A τ ρ : ℝ) (block : Finset (Index J noiseDim)) : ℝ :=
  A ^ block.card * (block.card.factorial : ℝ) ^ (τ * ρ) *
    eta diffusion T block ^ ρ

/-- The product weight of an enlarged endpoint/block-family configuration. -/
def configurationMajorantWeight
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A Cmaj τ ρ : ℝ)
    (configuration : MajorantConfiguration (J := J) (noiseDim := noiseDim)) : ℝ :=
  endpointMajorantWeight diffusion T A τ ρ configuration.1 *
    Cmaj ^ (ρ * configuration.2.1.card) *
    (configuration.2.1.card.factorial : ℝ) ^ (τ * ρ) *
    ∏ block ∈ configuration.2.1,
      blockMajorantWeight diffusion T A τ ρ block

theorem endpointMajorantWeight_nonneg
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T A τ ρ : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (endpoints : Finset (Fin noiseDim)) :
    0 ≤ endpointMajorantWeight diffusion T A τ ρ endpoints := by
  unfold endpointMajorantWeight
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hA _) (Real.rpow_nonneg (by positivity) _))
    (Finset.prod_nonneg fun r _ ↦
      Real.rpow_nonneg (endpointFactor_nonneg diffusion T r) _)

theorem blockMajorantWeight_nonneg
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T A τ ρ : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (block : Finset (Index J noiseDim)) :
    0 ≤ blockMajorantWeight diffusion T A τ ρ block := by
  unfold blockMajorantWeight
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hA _) (Real.rpow_nonneg (by positivity) _))
    (Real.rpow_nonneg (eta_nonneg diffusion hT block) _)

theorem weighted_keyMajorant_rpow_eq_configurationMajorantWeight
    {J stateDim noiseDim : ℕ} {drift : Drift stateDim} {payoff : Payoff stateDim}
    {T : ℝ} (bounds : GevreyBounds drift payoff T)
    (diffusion : Diffusion stateDim noiseDim) (hT : 0 ≤ T)
    (κ ρ : ℝ) (hκ : 0 ≤ κ)
    (source : GlobalMajorantKey (J := J) (noiseDim := noiseDim)) :
    κ ^ source.1.card * (keyMajorant bounds diffusion source.2) ^ ρ =
      configurationMajorantWeight diffusion T
        (κ * bounds.majorantConstant ^ ρ) bounds.majorantConstant bounds.τ ρ
        (globalMajorantConfiguration source) := by
  let root := source.2.1.1
  let parts := source.2.2.parts
  let M := bounds.majorantConstant
  let A := κ * M ^ ρ
  have hM : 0 ≤ M := zero_le_one.trans bounds.one_le_majorantConstant
  have hA : 0 ≤ A := mul_nonneg hκ (Real.rpow_nonneg hM ρ)
  have hrootEndpoint : ∀ j ∈ root, IsEndpoint j := by
    intro j hj
    exact (Finset.mem_filter.mp
      ((Finset.mem_powerset.mp source.2.1.2) hj)).2
  have hrootCard : (endpointComponents root).card = root.card :=
    card_endpointComponents root hrootEndpoint
  have hrootProduct :
      (∏ j ∈ root, ‖diffusionCoefficient diffusion T j T‖) =
        ∏ r ∈ endpointComponents root, endpointFactor diffusion T r :=
    endpoint_terminal_product_eq diffusion hT root hrootEndpoint
  have hrootProductRpow :
      (∏ j ∈ root, ‖diffusionCoefficient diffusion T j T‖) ^ ρ =
        ∏ r ∈ endpointComponents root, endpointFactor diffusion T r ^ ρ := by
    rw [hrootProduct]
    exact (Real.finsetProd_rpow (endpointComponents root)
      (endpointFactor diffusion T)
      (fun r _ ↦ endpointFactor_nonneg diffusion T r) ρ).symm
  have hrootFactorial :
      ((root.card.factorial : ℝ) ^ bounds.τ) ^ ρ =
        (root.card.factorial : ℝ) ^ (bounds.τ * ρ) :=
    (Real.rpow_mul (by positivity) bounds.τ ρ).symm
  have hpartFactorial (block : Finset (Index J noiseDim)) :
      ((block.card.factorial : ℝ) ^ bounds.τ) ^ ρ =
        (block.card.factorial : ℝ) ^ (bounds.τ * ρ) :=
    (Real.rpow_mul (by positivity) bounds.τ ρ).symm
  have hcountFactorial :
      ((parts.card.factorial : ℝ) ^ bounds.τ) ^ ρ =
        (parts.card.factorial : ℝ) ^ (bounds.τ * ρ) :=
    (Real.rpow_mul (by positivity) bounds.τ ρ).symm
  have hblockProduct :
      (∏ block ∈ parts,
          (block.card.factorial : ℝ) ^ bounds.τ * eta diffusion T block) ^ ρ =
        ∏ block ∈ parts,
          (block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
            eta diffusion T block ^ ρ := by
    rw [← Real.finsetProd_rpow parts
      (fun block ↦ (block.card.factorial : ℝ) ^ bounds.τ *
        eta diffusion T block)
      (fun block _ ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (eta_nonneg diffusion hT block)) ρ]
    apply Finset.prod_congr rfl
    intro block hblock
    rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _)
      (eta_nonneg diffusion hT block), hpartFactorial]
  have hblockNonneg : 0 ≤ ∏ block ∈ parts,
      (block.card.factorial : ℝ) ^ bounds.τ * eta diffusion T block := by
    exact Finset.prod_nonneg fun block _ ↦
      mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (eta_nonneg diffusion hT block)
  have hmajorantRpow :
      (keyMajorant bounds diffusion source.2) ^ ρ =
        (M ^ ρ) ^ (source.1.card + parts.card) *
          ((root.card.factorial : ℝ) ^ (bounds.τ * ρ) *
            ∏ r ∈ endpointComponents root, endpointFactor diffusion T r ^ ρ) *
          (parts.card.factorial : ℝ) ^ (bounds.τ * ρ) *
          ∏ block ∈ parts,
            (block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
              eta diffusion T block ^ ρ := by
    unfold keyMajorant
    change (M ^ (source.1.card + parts.card) *
      ((root.card.factorial : ℝ) ^ bounds.τ *
        ∏ j ∈ root, ‖diffusionCoefficient diffusion T j T‖) *
      (parts.card.factorial : ℝ) ^ bounds.τ *
      (∏ block ∈ parts,
        (block.card.factorial : ℝ) ^ bounds.τ * eta diffusion T block)) ^ ρ = _
    rw [Real.mul_rpow (by positivity) hblockNonneg,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      rpow_natPow hM, hrootFactorial, hrootProductRpow,
      hcountFactorial, hblockProduct]
  have hsupportCard :=
    TimeDependentLattice.Regularity.MajorantKey.support_card_eq source.2
  have hMcount : M ^ (ρ * parts.card) = (M ^ ρ) ^ parts.card := by
    calc
      M ^ (ρ * parts.card) = (M ^ ρ) ^ (parts.card : ℝ) :=
        Real.rpow_mul hM ρ (parts.card : ℝ)
      _ = (M ^ ρ) ^ parts.card := Real.rpow_natCast _ _
  have hAparts :
      ∏ block ∈ parts, A ^ block.card =
        A ^ (∑ block ∈ parts, block.card) :=
    Finset.prod_pow_eq_pow_sum parts (fun block ↦ block.card) A
  have hweightedBlocks :
      (∏ block ∈ parts,
        A ^ block.card * (block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
          eta diffusion T block ^ ρ) =
        A ^ (∑ block ∈ parts, block.card) *
          ∏ block ∈ parts,
            (block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
              eta diffusion T block ^ ρ := by
    calc
      (∏ block ∈ parts,
        A ^ block.card * (block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
          eta diffusion T block ^ ρ) =
        ∏ block ∈ parts,
          A ^ block.card *
            ((block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
              eta diffusion T block ^ ρ) := by
            apply Finset.prod_congr rfl
            intro block hblock
            ring
      _ = (∏ block ∈ parts, A ^ block.card) *
          ∏ block ∈ parts,
            (block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
              eta diffusion T block ^ ρ := Finset.prod_mul_distrib
      _ = _ := by rw [hAparts]
  rw [hmajorantRpow]
  unfold configurationMajorantWeight endpointMajorantWeight blockMajorantWeight
  change κ ^ source.1.card * _ =
    A ^ (endpointComponents root).card *
        ((endpointComponents root).card.factorial : ℝ) ^ (bounds.τ * ρ) *
        (∏ r ∈ endpointComponents root, endpointFactor diffusion T r ^ ρ) *
      M ^ (ρ * parts.card) *
      (parts.card.factorial : ℝ) ^ (bounds.τ * ρ) *
      ∏ block ∈ parts,
        A ^ block.card * (block.card.factorial : ℝ) ^ (bounds.τ * ρ) *
          eta diffusion T block ^ ρ
  rw [hrootCard, hMcount, hweightedBlocks]
  rw [show source.1.card = root.card + ∑ block ∈ parts, block.card by
    simpa [root, parts] using hsupportCard]
  dsimp [A]
  rw [mul_pow, mul_pow, pow_add, pow_add, pow_add]
  ring

/-- The finite sum over all unordered families of nonempty coordinate blocks. -/
def blockFamilyMajorantSum
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A M τ ρ : ℝ) : ℝ :=
  ∑ family : BlockFamily (J := J) (noiseDim := noiseDim),
    M ^ (ρ * family.1.card) *
      (family.1.card.factorial : ℝ) ^ (τ * ρ) *
      ∏ block ∈ family.1,
        blockMajorantWeight (J := J) diffusion T A τ ρ block

/-- The enlarged block-family sum is bounded by the factorial-decay series used in (4.18). -/
theorem blockFamilyMajorantSum_le_factorialDecaySeries
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T A M τ ρ H : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hM : 0 < M) (hH : 0 < H) (hτρ : τ * ρ < 1)
    (hblockSum : allSubsetTimeFactorSum (J := J) diffusion T A ρ τ ≤ H) :
    blockFamilyMajorantSum (J := J) diffusion T A M τ ρ ≤
      factorialDecaySeries (M ^ ρ * H) (τ * ρ) := by
  classical
  let blockUniverse := (Finset.univ : Finset (Index J noiseDim)).powerset.erase ∅
  let w : Finset (Index J noiseDim) → ℝ :=
    blockMajorantWeight (J := J) diffusion T A τ ρ
  let familyWeight : Finset (Finset (Index J noiseDim)) → ℝ := fun family ↦
    M ^ (ρ * family.card) * (family.card.factorial : ℝ) ^ (τ * ρ) *
      ∏ block ∈ family, w block
  have hw : ∀ block ∈ blockUniverse, 0 ≤ w block := by
    intro block hblock
    exact blockMajorantWeight_nonneg diffusion hT hA block
  have hwsum : (∑ block ∈ blockUniverse, w block) ≤ H := by
    have hall : allSubsetTimeFactorSum (J := J) diffusion T A ρ τ =
        ∑ block ∈ blockUniverse, w block := by
      unfold allSubsetTimeFactorSum
      dsimp [blockUniverse, w, blockMajorantWeight]
      change (∑ support ∈
          (Finset.univ : Finset (Finset (Index J noiseDim))),
        if support.Nonempty then
          A ^ support.card * (support.card.factorial : ℝ) ^ (τ * ρ) *
            eta diffusion T support ^ ρ
        else 0) = _
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext block
        simp [blockUniverse, Finset.nonempty_iff_ne_empty]
      · intro block hblock
        rfl
    rw [← hall]
    exact hblockSum
  have hM0 : 0 ≤ M := hM.le
  have hfixed (k : ℕ) :
      (∑ family ∈ blockUniverse.powersetCard k, familyWeight family) ≤
        (M ^ ρ * H) ^ k * (k.factorial : ℝ) ^ (τ * ρ - 1) := by
    have hsym := sum_powersetCard_prod_le_sum_pow_div_factorial
      blockUniverse w k hw
    have hcommon : 0 ≤ M ^ (ρ * k) * (k.factorial : ℝ) ^ (τ * ρ) :=
      mul_nonneg (Real.rpow_nonneg hM0 _)
        (Real.rpow_nonneg (by positivity) _)
    calc
      (∑ family ∈ blockUniverse.powersetCard k, familyWeight family) =
          M ^ (ρ * k) * (k.factorial : ℝ) ^ (τ * ρ) *
            (∑ family ∈ blockUniverse.powersetCard k,
              ∏ block ∈ family, w block) := by
        dsimp [familyWeight]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro family hfamily
        rw [(Finset.mem_powersetCard.mp hfamily).2]
      _ ≤ M ^ (ρ * k) * (k.factorial : ℝ) ^ (τ * ρ) *
          ((∑ block ∈ blockUniverse, w block) ^ k / k.factorial) :=
        mul_le_mul_of_nonneg_left hsym hcommon
      _ ≤ M ^ (ρ * k) * (k.factorial : ℝ) ^ (τ * ρ) *
          (H ^ k / k.factorial) := by
        apply mul_le_mul_of_nonneg_left _ hcommon
        apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ k.factorial)
        exact pow_le_pow_left₀ (Finset.sum_nonneg hw) hwsum k
      _ = (M ^ ρ * H) ^ k * (k.factorial : ℝ) ^ (τ * ρ - 1) := by
        have hMcount : M ^ (ρ * k) = (M ^ ρ) ^ k := by
          calc
            M ^ (ρ * k) = (M ^ ρ) ^ (k : ℝ) :=
              Real.rpow_mul hM0 ρ (k : ℝ)
            _ = (M ^ ρ) ^ k := Real.rpow_natCast _ _
        rw [hMcount, Real.rpow_sub_one (by positivity : (k.factorial : ℝ) ≠ 0),
          mul_pow]
        field_simp
  have hseries := derivativeRhoConstant_series_summable hH hM
    (show τ * ρ < 1 from hτρ)
  unfold blockFamilyMajorantSum
  change (∑ family : BlockFamily (J := J) (noiseDim := noiseDim),
      familyWeight family.1) ≤ _
  calc
    (∑ family : BlockFamily (J := J) (noiseDim := noiseDim),
      familyWeight family.1) =
        ∑ family ∈ blockUniverse.powerset, familyWeight family := by
      symm
      exact Finset.sum_subtype _ (fun family ↦ by simp [blockUniverse]) _
    _ = ∑ k ∈ Finset.range (blockUniverse.card + 1),
        ∑ family ∈ blockUniverse.powersetCard k, familyWeight family := by
      rw [Finset.powerset_card_biUnion]
      apply Finset.sum_biUnion
      intro left hleft right hright hne
      exact Finset.disjoint_powersetCard_of_ne hne blockUniverse blockUniverse
    _ ≤ ∑ k ∈ Finset.range (blockUniverse.card + 1),
        (M ^ ρ * H) ^ k * (k.factorial : ℝ) ^ (τ * ρ - 1) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hfixed k
    _ ≤ ∑' k : ℕ,
        (M ^ ρ * H) ^ k * (k.factorial : ℝ) ^ (τ * ρ - 1) := by
      exact hseries.sum_le_tsum _ (fun k hk ↦
        mul_nonneg (pow_nonneg (mul_nonneg (Real.rpow_nonneg hM0 ρ) hH.le) _)
          (Real.rpow_nonneg (by positivity) _))
    _ = factorialDecaySeries (M ^ ρ * H) (τ * ρ) := rfl

/-- Sum of the enlarged endpoint/block-family majorant. -/
def configurationMajorantSum
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A M τ ρ : ℝ) : ℝ :=
  ∑ configuration : MajorantConfiguration (J := J) (noiseDim := noiseDim),
    configurationMajorantWeight diffusion T A M τ ρ configuration

theorem configurationMajorantSum_le_derivativeRhoConstant
    {J stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T A M τ ρ H : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hM : 0 < M) (hH : 0 < H) (hτρ : τ * ρ < 1)
    (hendpointSum : endpointWeightedSum diffusion T A ρ τ ≤ H)
    (hblockSum : allSubsetTimeFactorSum (J := J) diffusion T A ρ τ ≤ H) :
    configurationMajorantSum (J := J) diffusion T A M τ ρ ≤
      derivativeRhoConstant H M τ ρ := by
  let endpointSum := ∑ endpoints : Finset (Fin noiseDim),
    endpointMajorantWeight diffusion T A τ ρ endpoints
  let familySum := blockFamilyMajorantSum (J := J) diffusion T A M τ ρ
  have hendpoint : endpointSum ≤ H := by
    rw [endpointWeightedSum_eq_fintypeSum] at hendpointSum
    simpa [endpointSum, endpointMajorantWeight] using hendpointSum
  have hfamily : familySum ≤ factorialDecaySeries (M ^ ρ * H) (τ * ρ) :=
    blockFamilyMajorantSum_le_factorialDecaySeries diffusion hT hA hM hH hτρ
      hblockSum
  have hendpointNonneg : 0 ≤ endpointSum := by
    dsimp [endpointSum]
    exact Finset.sum_nonneg fun endpoints _ ↦
      endpointMajorantWeight_nonneg diffusion hT hA endpoints
  have hfamilyNonneg : 0 ≤ familySum := by
    unfold familySum blockFamilyMajorantSum
    apply Finset.sum_nonneg
    intro family hfamilyMem
    unfold blockMajorantWeight
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hM.le _)
        (Real.rpow_nonneg (by positivity) _))
      (Finset.prod_nonneg fun block _ ↦
        mul_nonneg
          (mul_nonneg (pow_nonneg hA _) (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (eta_nonneg diffusion hT block) _))
  have hseriesNonneg : 0 ≤ factorialDecaySeries (M ^ ρ * H) (τ * ρ) := by
    unfold factorialDecaySeries
    exact tsum_nonneg fun k ↦
      mul_nonneg (pow_nonneg (mul_nonneg (Real.rpow_nonneg hM.le _) hH.le) _)
        (Real.rpow_nonneg (by positivity) _)
  have hfactorization :
      configurationMajorantSum (J := J) diffusion T A M τ ρ =
        endpointSum * familySum := by
    unfold configurationMajorantSum
    rw [Fintype.sum_prod_type]
    dsimp [endpointSum, familySum, blockFamilyMajorantSum]
    calc
      (∑ endpoints : Finset (Fin noiseDim),
        ∑ family : BlockFamily (J := J) (noiseDim := noiseDim),
          configurationMajorantWeight diffusion T A M τ ρ
            (endpoints, family)) =
        ∑ endpoints : Finset (Fin noiseDim),
          endpointMajorantWeight diffusion T A τ ρ endpoints *
            (∑ family : BlockFamily (J := J) (noiseDim := noiseDim),
              M ^ (ρ * family.1.card) *
                (family.1.card.factorial : ℝ) ^ (τ * ρ) *
                ∏ block ∈ family.1,
                  blockMajorantWeight (J := J) diffusion T A τ ρ block) := by
          apply Finset.sum_congr rfl
          intro endpoints hendpoints
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro family hfamilyMem
          unfold configurationMajorantWeight
          ring
      _ = (∑ endpoints : Finset (Fin noiseDim),
          endpointMajorantWeight diffusion T A τ ρ endpoints) *
          (∑ family : BlockFamily (J := J) (noiseDim := noiseDim),
            M ^ (ρ * family.1.card) *
              (family.1.card.factorial : ℝ) ^ (τ * ρ) *
              ∏ block ∈ family.1,
                blockMajorantWeight (J := J) diffusion T A τ ρ block) := by
        rw [Finset.sum_mul]
  rw [hfactorization]
  calc
    endpointSum * familySum ≤ H * familySum :=
      mul_le_mul_of_nonneg_right hendpoint hfamilyNonneg
    _ ≤ H * factorialDecaySeries (M ^ ρ * H) (τ * ρ) :=
      mul_le_mul_of_nonneg_left hfamily hH.le
    _ = derivativeRhoConstant H M τ ρ := rfl

/-- Subadditivity of `x ↦ x^ρ` for a finite sum when `0 < ρ ≤ 1`. -/
theorem rpow_finset_sum_le_sum_rpow
    {α : Type*} (entries : Finset α) (value : α → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hvalue : ∀ entry ∈ entries, 0 ≤ value entry) :
    (∑ entry ∈ entries, value entry) ^ ρ ≤
      ∑ entry ∈ entries, value entry ^ ρ := by
  classical
  induction entries using Finset.induction_on with
  | empty => simp [hρ.ne']
  | @insert entry entries hentry ih =>
      rw [Finset.sum_insert hentry, Finset.sum_insert hentry]
      exact (Real.rpow_add_le_add_rpow (hvalue entry (by simp))
        (Finset.sum_nonneg fun other hother ↦ hvalue other (by simp [hother]))
        hρ.le hρone).trans
        (add_le_add (le_refl (value entry ^ ρ))
          (ih (fun other hother ↦ hvalue other (by simp [hother]))))

/-- Nonempty support/key pairs, the exact source of the global reindexing. -/
abbrev NonemptyGlobalMajorantKey {J noiseDim : ℕ} :=
  Σ support : {support : Finset (Index J noiseDim) // support.Nonempty},
    MajorantKey support.1

def nonemptyGlobalMajorantConfiguration
    {J noiseDim : ℕ}
    (source : NonemptyGlobalMajorantKey (J := J) (noiseDim := noiseDim)) :
    MajorantConfiguration (J := J) (noiseDim := noiseDim) :=
  globalMajorantConfiguration ⟨source.1.1, source.2⟩

theorem nonemptyGlobalMajorantConfiguration_injective
    {J noiseDim : ℕ} :
    Function.Injective
      (nonemptyGlobalMajorantConfiguration (J := J) (noiseDim := noiseDim)) := by
  rintro ⟨⟨leftSupport, hleft⟩, leftKey⟩
    ⟨⟨rightSupport, hright⟩, rightKey⟩ heq
  have hglobal :
      (⟨leftSupport, leftKey⟩ : GlobalMajorantKey (J := J) (noiseDim := noiseDim)) =
        ⟨rightSupport, rightKey⟩ :=
    globalMajorantConfiguration_injective heq
  cases hglobal
  rfl

theorem derivativeEnvelopeRhoSum_le_configurationMajorantSum
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {κ ρ : ℝ} (hκ : 0 ≤ κ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) :
    (∑ support ∈ Finset.univ.powerset.filter
        (fun support : Finset (Index J noiseDim) ↦ support.Nonempty),
      κ ^ support.card *
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ ρ) ≤
      configurationMajorantSum (J := J) diffusion T
        (κ * bounds.majorantConstant ^ ρ) bounds.majorantConstant bounds.τ ρ := by
  classical
  let sourceWeight : NonemptyGlobalMajorantKey (J := J) (noiseDim := noiseDim) → ℝ :=
    fun source ↦ κ ^ source.1.1.card *
      keyMajorant bounds diffusion source.2 ^ ρ
  let configurationWeight : MajorantConfiguration (J := J) (noiseDim := noiseDim) → ℝ :=
    configurationMajorantWeight diffusion T
      (κ * bounds.majorantConstant ^ ρ) bounds.majorantConstant bounds.τ ρ
  have hsourceConfiguration (source : NonemptyGlobalMajorantKey
      (J := J) (noiseDim := noiseDim)) :
      sourceWeight source =
        configurationWeight (nonemptyGlobalMajorantConfiguration source) := by
    exact weighted_keyMajorant_rpow_eq_configurationMajorantWeight
      bounds diffusion hT.le κ ρ hκ ⟨source.1.1, source.2⟩
  have hconfigurationNonneg (configuration : MajorantConfiguration
      (J := J) (noiseDim := noiseDim)) : 0 ≤ configurationWeight configuration := by
    unfold configurationWeight configurationMajorantWeight
    have hA : 0 ≤ κ * bounds.majorantConstant ^ ρ :=
      mul_nonneg hκ (Real.rpow_nonneg
        (zero_le_one.trans bounds.one_le_majorantConstant) ρ)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (endpointMajorantWeight_nonneg diffusion hT.le hA configuration.1)
          (Real.rpow_nonneg
            (zero_le_one.trans bounds.one_le_majorantConstant) _))
        (Real.rpow_nonneg (by positivity) _))
      (Finset.prod_nonneg fun block _ ↦
        blockMajorantWeight_nonneg diffusion hT.le hA block)
  have hsupportBound
      (support : {support : Finset (Index J noiseDim) // support.Nonempty}) :
      κ ^ support.1.card *
          normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support.1 ^ ρ ≤
        ∑ key : MajorantKey support.1,
          κ ^ support.1.card * keyMajorant bounds diffusion key ^ ρ := by
    have hbdd := normalizedMixedDerivativeAt_bddAbove
      (diffusion := diffusion) bounds hT x₀ support.1 support.2
    have henvelopeNonneg := normalizedDerivativeEnvelope_nonneg
      drift diffusion payoff T bounds.β x₀ support.1 hbdd
    have hmajorant := normalizedDerivativeEnvelope_le_keyMajorantSum
      (diffusion := diffusion) bounds hT x₀ support.1 support.2
    have hkeyNonneg : ∀ key : MajorantKey support.1,
        0 ≤ keyMajorant bounds diffusion key := fun key ↦
      keyMajorant_nonneg bounds diffusion hT.le key
    have hrpow :
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support.1 ^ ρ ≤
          ∑ key : MajorantKey support.1, keyMajorant bounds diffusion key ^ ρ := by
      calc
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support.1 ^ ρ ≤
            (∑ key : MajorantKey support.1,
              keyMajorant bounds diffusion key) ^ ρ :=
          Real.rpow_le_rpow henvelopeNonneg hmajorant hρ.le
        _ ≤ ∑ key : MajorantKey support.1,
              keyMajorant bounds diffusion key ^ ρ :=
          rpow_finset_sum_le_sum_rpow Finset.univ
            (keyMajorant bounds diffusion) hρ hρone
            (fun key _ ↦ hkeyNonneg key)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hrpow (pow_nonneg hκ _)
  calc
    (∑ support ∈ Finset.univ.powerset.filter
        (fun support : Finset (Index J noiseDim) ↦ support.Nonempty),
      κ ^ support.card *
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ ρ) ≤
      ∑ support ∈ Finset.univ.powerset.filter
          (fun support : Finset (Index J noiseDim) ↦ support.Nonempty),
        ∑ key : MajorantKey support,
          κ ^ support.card * keyMajorant bounds diffusion key ^ ρ := by
      apply Finset.sum_le_sum
      intro support hsupport
      exact hsupportBound ⟨support, (Finset.mem_filter.mp hsupport).2⟩
    _ = ∑ support : {support : Finset (Index J noiseDim) // support.Nonempty},
        ∑ key : MajorantKey support.1,
          κ ^ support.1.card * keyMajorant bounds diffusion key ^ ρ := by
      exact Finset.sum_subtype _ (fun support ↦ by simp) _
    _ = ∑ source : NonemptyGlobalMajorantKey (J := J) (noiseDim := noiseDim),
        sourceWeight source := by
      rw [Fintype.sum_sigma]
    _ = ∑ source : NonemptyGlobalMajorantKey (J := J) (noiseDim := noiseDim),
        configurationWeight (nonemptyGlobalMajorantConfiguration source) := by
      apply Finset.sum_congr rfl
      intro source hsource
      exact hsourceConfiguration source
    _ = ∑ configuration ∈ Finset.image nonemptyGlobalMajorantConfiguration Finset.univ,
        configurationWeight configuration := by
      symm
      exact Finset.sum_image
        (Set.injOn_of_injective nonemptyGlobalMajorantConfiguration_injective)
    _ ≤ ∑ configuration : MajorantConfiguration (J := J) (noiseDim := noiseDim),
        configurationWeight configuration := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro configuration hconfiguration himage
      exact hconfigurationNonneg configuration
    _ = configurationMajorantSum (J := J) diffusion T
        (κ * bounds.majorantConstant ^ ρ) bounds.majorantConstant bounds.τ ρ := rfl

/-- A single positive constant dominating both subset sums in Lemma 4.5. -/
def legacyTreeSubsetConstant
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A ρ τ : ℝ) : ℝ :=
  1 + max 0 (max
    (endpointSeriesConstant diffusion T A ρ τ)
    (allSubsetSeriesConstant diffusion T A ρ τ))

theorem legacyTreeSubsetConstant_pos
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A ρ τ : ℝ) :
    0 < legacyTreeSubsetConstant diffusion T A ρ τ := by
  unfold legacyTreeSubsetConstant
  have : (0 : ℝ) ≤ max 0 (max
      (endpointSeriesConstant diffusion T A ρ τ)
      (allSubsetSeriesConstant diffusion T A ρ τ)) := le_max_left _ _
  linarith

theorem endpointSeriesConstant_le_legacyTreeSubsetConstant
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A ρ τ : ℝ) :
    endpointSeriesConstant diffusion T A ρ τ ≤
      legacyTreeSubsetConstant diffusion T A ρ τ := by
  unfold legacyTreeSubsetConstant
  have hinner : endpointSeriesConstant diffusion T A ρ τ ≤
      max (endpointSeriesConstant diffusion T A ρ τ)
        (allSubsetSeriesConstant diffusion T A ρ τ) := le_max_left _ _
  have houter := le_max_right (0 : ℝ) (max
    (endpointSeriesConstant diffusion T A ρ τ)
    (allSubsetSeriesConstant diffusion T A ρ τ))
  linarith

theorem allSubsetSeriesConstant_le_legacyTreeSubsetConstant
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A ρ τ : ℝ) :
    allSubsetSeriesConstant diffusion T A ρ τ ≤
      legacyTreeSubsetConstant diffusion T A ρ τ := by
  unfold legacyTreeSubsetConstant
  have hinner : allSubsetSeriesConstant diffusion T A ρ τ ≤
      max (endpointSeriesConstant diffusion T A ρ τ)
        (allSubsetSeriesConstant diffusion T A ρ τ) := le_max_right _ _
  have houter := le_max_right (0 : ℝ) (max
    (endpointSeriesConstant diffusion T A ρ τ)
    (allSubsetSeriesConstant diffusion T A ρ τ))
  linarith

/-- The exact `C_H` from the paper on its parameter domain. The maximum with one
only totalizes the definition outside that domain, where a real `tsum` may be zero. -/
def treeSubsetConstant
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A ρ τ : ℝ) : ℝ :=
  max 1 (paperTimeFactorConstant T A ρ τ (columnRhoSum diffusion ρ))

theorem treeSubsetConstant_pos
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    (T A ρ τ : ℝ) :
    0 < treeSubsetConstant diffusion T A ρ τ :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem treeSubsetConstant_eq_paperTimeFactorConstant
    {stateDim noiseDim : ℕ} (diffusion : Diffusion stateDim noiseDim)
    {T A ρ τ : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hρ : 2 / 3 < ρ)
    (hτρ : τ * ρ < 1) :
    treeSubsetConstant diffusion T A ρ τ =
      paperTimeFactorConstant T A ρ τ (columnRhoSum diffusion ρ) :=
  max_eq_right (one_le_paperTimeFactorConstant hT hA
    (columnRhoSum_nonneg diffusion ρ) hρ hτρ)

/-- Equation (4.17), derived directly from Proposition 4.3 and Lemma 4.5. -/
theorem derivativeEnvelopeRhoSum_le_derivativeRhoConstant
    {J stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {κ ρ : ℝ} (hκ : 0 ≤ κ)
    (hρ : 2 / 3 < ρ) (hρone : ρ ≤ 1) (hτρ : bounds.τ * ρ < 1) :
    (∑ support ∈ Finset.univ.powerset.filter
        (fun support : Finset (Index J noiseDim) ↦ support.Nonempty),
      κ ^ support.card *
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ ρ) ≤
      let A := κ * bounds.majorantConstant ^ ρ
      let H := treeSubsetConstant diffusion T A ρ bounds.τ
      derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ := by
  let A := κ * bounds.majorantConstant ^ ρ
  let H := treeSubsetConstant diffusion T A ρ bounds.τ
  have hA : 0 ≤ A := mul_nonneg hκ
    (Real.rpow_nonneg (zero_le_one.trans bounds.one_le_majorantConstant) ρ)
  have hH : 0 < H := treeSubsetConstant_pos diffusion T A ρ bounds.τ
  have hendpoint : endpointWeightedSum diffusion T A ρ bounds.τ ≤ H := by
    exact (endpointWeightedSum_le_paperTimeFactorConstant diffusion hT hA hρ
      (zero_le_one.trans bounds.τ_mem.1) hτρ).trans (le_max_right _ _)
  have hall : allSubsetTimeFactorSum (J := J) diffusion T A ρ bounds.τ ≤ H := by
    exact (allSubsetTimeFactorSum_le_paperTimeFactorConstant diffusion hT hA hρ
      (zero_le_one.trans bounds.τ_mem.1) hτρ).trans (le_max_right _ _)
  calc
    (∑ support ∈ Finset.univ.powerset.filter
        (fun support : Finset (Index J noiseDim) ↦ support.Nonempty),
      κ ^ support.card *
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ ρ) ≤
      configurationMajorantSum (J := J) diffusion T A
        bounds.majorantConstant bounds.τ ρ := by
          simpa [A] using derivativeEnvelopeRhoSum_le_configurationMajorantSum
            bounds hT x₀ hκ (by linarith : 0 < ρ) hρone
    _ ≤ derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ :=
      configurationMajorantSum_le_derivativeRhoConstant diffusion hT.le hA
        (zero_lt_one.trans_le bounds.one_le_majorantConstant) hH hτρ
        hendpoint hall

/-- Paper Theorem 4.1 for the actual normalized Euler mixed-derivative envelopes.  All earlier
analytic, tree, counting, and Brownian-bridge estimates are discharged in this statement. -/
theorem theorem4_1
    {stateDim noiseDim : ℕ}
    {drift : Drift stateDim} {diffusion : Diffusion stateDim noiseDim}
    {payoff : Payoff stateDim} {T : ℝ}
    (bounds : GevreyBounds drift payoff T) (hT : 0 < T)
    (x₀ : State stateDim) {κ p : ℝ} (hκ : 0 < κ) (hp : 2 / 3 < p) :
    ∀ J,
      weightedDerivativeSum κ p
        (normalizedDerivativeEnvelope (J := J)
          drift diffusion payoff T bounds.β x₀) ≤
        let ρ := intermediateExponent bounds.τ p
        let κρ := κ ^ (ρ / p)
        let A := κρ * bounds.majorantConstant ^ ρ
        let H := treeSubsetConstant diffusion T A ρ bounds.τ
        derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ ^ (p / ρ) := by
  intro J
  let ρ := intermediateExponent bounds.τ p
  let κρ := κ ^ (ρ / p)
  let A := κρ * bounds.majorantConstant ^ ρ
  let H := treeSubsetConstant diffusion T A ρ bounds.τ
  let R := derivativeRhoConstant H bounds.majorantConstant bounds.τ ρ
  have hspec := intermediateExponent_spec bounds.τ_mem.1 bounds.τ_mem.2 hp
  have hρcritical : 2 / 3 < ρ := hspec.1
  have hρp : ρ < p := hspec.2.1
  have hρinv : ρ < 1 / bounds.τ := hspec.2.2.1
  have hρ : 0 < ρ := hspec.2.2.2
  have hp0 : 0 < p := hρ.trans hρp
  have hτ0 : 0 < bounds.τ := zero_lt_one.trans_le bounds.τ_mem.1
  have hτρ : bounds.τ * ρ < 1 := by
    rw [lt_div_iff₀ hτ0] at hρinv
    simpa [mul_comm] using hρinv
  have hρone : ρ ≤ 1 := by
    have hinvOne : 1 / bounds.τ ≤ 1 := by
      rw [div_le_one hτ0]
      exact bounds.τ_mem.1
    exact hρinv.le.trans hinvOne
  have hκρ : 0 < κρ := Real.rpow_pos_of_pos hκ _
  have hRhoSum :
      (∑ support ∈ Finset.univ.powerset.filter
          (fun support : Finset (Index J noiseDim) ↦ support.Nonempty),
        κρ ^ support.card *
          normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ ρ) ≤ R := by
    exact derivativeEnvelopeRhoSum_le_derivativeRhoConstant
      bounds hT x₀ hκρ.le hρcritical hρone hτρ
  let entries := Finset.univ.powerset.filter
    (fun support : Finset (Index J noiseDim) ↦ support.Nonempty)
  let scaled : Finset (Index J noiseDim) → ℝ := fun support ↦
    κ ^ ((support.card : ℝ) / p) *
      normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support
  have henvelope (support : Finset (Index J noiseDim))
      (hsupport : support ∈ entries) :
      0 ≤ normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support := by
    have hnonempty : support.Nonempty := (Finset.mem_filter.mp hsupport).2
    exact normalizedDerivativeEnvelope_nonneg drift diffusion payoff T bounds.β x₀ support
      (normalizedMixedDerivativeAt_bddAbove
        (diffusion := diffusion) bounds hT x₀ support hnonempty)
  have hscaled : ∀ support ∈ entries, 0 ≤ scaled support := by
    intro support hsupport
    exact mul_nonneg (Real.rpow_nonneg hκ.le _)
      (henvelope support hsupport)
  have hscaledRho :
      (∑ support ∈ entries, scaled support ^ ρ) =
        ∑ support ∈ entries,
          κρ ^ support.card *
            normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ ρ := by
    apply Finset.sum_congr rfl
    intro support hsupport
    have hκpower :
        (κ ^ ((support.card : ℝ) / p)) ^ ρ = κρ ^ support.card := by
      calc
        (κ ^ ((support.card : ℝ) / p)) ^ ρ =
            κ ^ (((support.card : ℝ) / p) * ρ) :=
          (Real.rpow_mul hκ.le ((support.card : ℝ) / p) ρ).symm
        _ = κ ^ ((ρ / p) * (support.card : ℝ)) := by congr 1 <;> ring
        _ = (κ ^ (ρ / p)) ^ (support.card : ℝ) :=
          Real.rpow_mul hκ.le (ρ / p) (support.card : ℝ)
        _ = κρ ^ support.card := by
          rw [Real.rpow_natCast]
    unfold scaled
    rw [Real.mul_rpow (Real.rpow_nonneg hκ.le _)
      (henvelope support hsupport), hκpower]
  have hscaledSum : ∑ support ∈ entries, scaled support ^ ρ ≤ R := by
    rw [hscaledRho]
    exact hRhoSum
  have hlift := sum_rpow_lift entries scaled hρ hρp hscaled hscaledSum
  change (∑ support ∈ entries,
    κ ^ support.card *
      normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ p) ≤ _
  calc
    (∑ support ∈ entries,
      κ ^ support.card *
        normalizedDerivativeEnvelope drift diffusion payoff T bounds.β x₀ support ^ p) =
        ∑ support ∈ entries, scaled support ^ p := by
      apply Finset.sum_congr rfl
      intro support hsupport
      unfold scaled
      rw [Real.mul_rpow (Real.rpow_nonneg hκ.le _)
        (henvelope support hsupport), ← Real.rpow_mul hκ.le]
      rw [show κ ^ support.card = κ ^ (support.card : ℝ) by
        exact (Real.rpow_natCast κ support.card).symm]
      congr 2
      field_simp
    _ ≤ R ^ (p / ρ) := hlift

end

end TimeDependentLattice.Regularity

