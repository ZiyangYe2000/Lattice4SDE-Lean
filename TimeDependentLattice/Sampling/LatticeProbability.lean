/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import TimeDependentLattice.Sampling.LatticeEstimator
import Mathlib.Probability.UniformOn

/-!
# Probability laws for randomized lattice rules

The generating vector is uniform on `{1, ..., N - 1}^s`.  The shift coordinates are independent
and uniform on `[0,1)`.  These are precisely the two laws used in paper Theorem 3.1.
-/

namespace TimeDependentLattice.Sampling

noncomputable section

open Set
open MeasureTheory ProbabilityTheory

/-- For `N ≥ 2`, the finite set `{1, ..., N - 1}^s` of generating vectors is nonempty. -/
theorem latticeGenerator_nonempty {ι : Type*} {N : ℕ} (hN : 2 ≤ N) :
    Nonempty (LatticeGenerator ι N) := by
  have hpos : 0 < N - 1 := by omega
  exact ⟨fun _ ↦ ⟨0, hpos⟩⟩

/-- Uniform law on all generating vectors with coordinates in `{1, ..., N - 1}`. -/
def uniformGeneratorMeasure {ι : Type*} [Fintype ι] (N : ℕ) :
    Measure (LatticeGenerator ι N) :=
  uniformOn Set.univ

instance uniformGeneratorMeasure_isProbability
    {ι : Type*} [Fintype ι] (N : ℕ) [Nonempty (LatticeGenerator ι N)] :
    IsProbabilityMeasure (uniformGeneratorMeasure (ι := ι) N) := by
  unfold uniformGeneratorMeasure
  infer_instance

/-- Uniform probability measure on the half-open unit interval `[0,1)`. -/
def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Ico 0 1)

instance unitIntervalMeasure_isProbability : IsProbabilityMeasure unitIntervalMeasure := by
  refine ⟨?_⟩
  simp [unitIntervalMeasure, Real.volume_Ico]

/-- Product-uniform law of the random shift `Delta ∈ [0,1)^s`. -/
def uniformShiftMeasure (ι : Type*) [Fintype ι] : Measure (LatticeShift ι) :=
  Measure.pi (fun _ : ι ↦ unitIntervalMeasure)

instance uniformShiftMeasure_isProbability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (uniformShiftMeasure ι) := by
  unfold uniformShiftMeasure
  infer_instance

/-- Joint law of an independently chosen generating vector and random shift. -/
def randomizedLatticeMeasure {ι : Type*} [Fintype ι] (N : ℕ)
    : Measure (LatticeGenerator ι N × LatticeShift ι) :=
  (uniformGeneratorMeasure (ι := ι) N).prod (uniformShiftMeasure ι)

instance randomizedLatticeMeasure_isProbability
    {ι : Type*} [Fintype ι] (N : ℕ) [Nonempty (LatticeGenerator ι N)] :
    IsProbabilityMeasure (randomizedLatticeMeasure (ι := ι) N) := by
  unfold randomizedLatticeMeasure
  infer_instance

/-- The sample space of `R` independently randomized lattice rules. -/
abbrev RepeatedRandomizedLatticeInput (ι : Type*) (N R : ℕ) :=
  Fin R → (LatticeGenerator ι N × LatticeShift ι)

/-- Product law of `R` independent generating-vector/shift pairs. -/
def repeatedRandomizedLatticeMeasure
    {ι : Type*} [Fintype ι] (N R : ℕ) :
    Measure (RepeatedRandomizedLatticeInput ι N R) :=
  Measure.pi (fun _ : Fin R ↦ randomizedLatticeMeasure (ι := ι) N)

instance repeatedRandomizedLatticeMeasure_isProbability
    {ι : Type*} [Fintype ι] (N R : ℕ)
    [Nonempty (LatticeGenerator ι N)] :
    IsProbabilityMeasure (repeatedRandomizedLatticeMeasure (ι := ι) N R) := by
  unfold repeatedRandomizedLatticeMeasure
  infer_instance

end

end TimeDependentLattice.Sampling
