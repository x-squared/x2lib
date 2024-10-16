/-
Copyright (c) 2024 Stephan maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.Quot
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.AddTorsor
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Algebra.MulAction

/-!
# Auxiliary results for modules

This file extends contains auxiliary results for modules.
-/

-- ********************************************************************
section «Submodules»
/-!
## Submodules

. -/

namespace Submodule

/-- A submodule is cofonite iff the quotient by the submodule is finite. -/
def IsCofinite
  {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]
  (N : Submodule R M) : Prop
  :=  Module.Finite R (M ⧸ N)

/--
TODO Eliminate this
-/
@[simp] def as_subset
    {𝕜 : Type u} [Ring 𝕜]
    {V : Type v} [AddCommGroup V] [Module 𝕜 V]
    {s : Set V} (sm : Submodule 𝕜 V) --(_ : s ⊆ sm)
      := --{ m : sm | (m : V) ∈ s}
  Submodule.subtype sm ⁻¹' s

/-- Mathlib does not seem to contain a defintion for the trivial
submodule consisting of `0` only. -/
@[simp] def trivial
    {𝕜 : Type u} [Ring 𝕜]
    {V : Type v} [AddCommGroup V] [hmv : Module 𝕜 V] :  Submodule 𝕜 V where
  carrier := { (0:V) }
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_singleton_iff.mp ha]
    rw [Set.mem_singleton_iff.mp hb]
    exact add_zero 0
  zero_mem' := by simp
  smul_mem' := by simp

end Submodule

end «Submodules»

-- ********************************************************************
#lint
