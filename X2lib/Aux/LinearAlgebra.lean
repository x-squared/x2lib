/-
Copyright (c) 2024 Stephan Maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Subset
import Mathlib.Order.SetNotation
import Mathlib.Algebra.AddTorsor
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Topology.Algebra.Affine
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.LinearAlgebra.Ray
import Mathlib.LinearAlgebra.Dimension.Finrank

import X2lib.Topology.PiecewiseLinear.Aux.Set
import X2lib.Topology.PiecewiseLinear.Aux.Affine
import X2lib.Topology.PiecewiseLinear.Aux.Module

/-!
# Joins and cones

In this file we introduce `Join` and `Cone` objects as subsets
of a given affine ambient space. Both join and cone are the fundamental
set-constructions for piecewise-linear topology.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Rourke] for ann introduction to PL-topology.
-/

universe u v w

-- ********************************************************************
section «Finite dimensional»

/-- In finite dimensional vector space each set of linear subspaces
has maximal  elements. -/
theorem FiniteDimensional.exists_max_submodule
    {𝕜 : Type u} [DivisionRing 𝕜]
    {V : Type v} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (sms : Set (Submodule 𝕜 V)) (hsmne : sms.Nonempty) :
    ∃ sm ∈ sms, ∀ sm', sm' ∈ sms → sm ≤ sm' → sm = sm' := by
  let fdim := (fun s : Submodule 𝕜 V => FiniteDimensional.finrank 𝕜 s)
  let dims : Set ℕ := fdim '' sms
  have h : dims.Nonempty := by exact Set.Nonempty.image fdim hsmne
  have h0 : ∀ d ∈ dims, d <= FiniteDimensional.finrank 𝕜 V := by
    intro d hd; rcases (Set.mem_image fdim sms d).mp hd with ⟨sd, ⟨_, fdimsdd⟩⟩
    rw [←fdimsdd]; exact Submodule.finrank_le sd
  let s := { n | n <= FiniteDimensional.finrank 𝕜 V }
  have h1 : s.Finite := by exact Set.finite_le_nat $ FiniteDimensional.finrank 𝕜 V
  have h2 : dims ⊆ s := by intro m hm; rw [Set.mem_setOf]; exact h0 m hm
  have h3 : dims.Finite := by exact Set.Finite.subset h1 h2
  have h4 : ∃ n ∈ dims, ∀ n' ∈ dims, n' ≤ n := by
    rcases Set.Finite.exists_maximal_wrt id dims h3 h with ⟨n, ⟨hndims, hn⟩⟩
    dsimp at hn; use n; apply And.intro hndims; intro n' hn'
    by_contra hc; simp only [Nat.gt_of_not_le] at hc
    have ha := hn n' hn' $ le_of_lt $ Nat.gt_of_not_le hc
    have hb := (ne_of_gt $ Nat.gt_of_not_le hc).symm
    contradiction
  rcases h4 with ⟨n, ⟨hndims, hnmax⟩⟩
  rcases (Set.mem_image fdim sms n).mp hndims with ⟨sm, ⟨hsms, fdimsmn⟩⟩
  use sm
  apply And.intro hsms
  intro sm' hsm' hsmsm'
  have h5 : fdim sm' ≤ fdim sm := by
    rw [fdimsmn]
    exact hnmax (fdim sm') (Set.mem_image_of_mem fdim hsm')
  exact FiniteDimensional.eq_of_le_of_finrank_le hsmsm' h5

  end «Finite dimensional»
