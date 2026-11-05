/-
Copyright (c) 2026 QMC for SDE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Du Ouyang, Josef Dick, Ziyang Ye
-/
import Mathlib

/-!
# Basic setup

This module contains the first compile check for the time-dependent lattice formalization.
-/

namespace TimeDependentLattice

/-- A minimal theorem used to verify that Lean and Mathlib are available. -/
theorem add_zero_smoke_test (n : ℕ) : n + 0 = n := by
  simp

end TimeDependentLattice
