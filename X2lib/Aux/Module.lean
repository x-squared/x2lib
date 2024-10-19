/-
Copyright (c) 2024 Stephan maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib

/-!
# Auxiliary results for modules

This file extends contains auxiliary results for modules.
-/

-- ********************************************************************
section «Submodules»

namespace Submodule

/-- A submodule is cofinite iff the quotient by the submodule is finite. -/
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
section «Finite dimensional spaces»

/-- In a finite dimensional vector space each set of linear subspaces
has maximal elements. -/
theorem Module.exists_max_submodule
    {𝕜 : Type u} [DivisionRing 𝕜]
    {V : Type v} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (sms : Set (Submodule 𝕜 V)) (hsmne : sms.Nonempty) :
    ∃ sm ∈ sms, ∀ sm', sm' ∈ sms → sm ≤ sm' → sm = sm' := by
  let fdim := (fun s : Submodule 𝕜 V => Module.finrank 𝕜 s)
  let dims : Set ℕ := fdim '' sms
  have h : dims.Nonempty := by exact Set.Nonempty.image fdim hsmne
  have h0 : ∀ d ∈ dims, d <= Module.finrank 𝕜 V := by
    intro d hd; rcases (Set.mem_image fdim sms d).mp hd with ⟨sd, ⟨_, fdimsdd⟩⟩
    rw [←fdimsdd]; exact Submodule.finrank_le sd
  let s := { n | n <= Module.finrank 𝕜 V }
  have h1 : s.Finite := by exact Set.finite_le_nat $ Module.finrank 𝕜 V
  have h2 : dims ⊆ s := by intro m hm; rw [Set.mem_setOf]; exact h0 m hm
  have : dims.Finite := by exact Set.Finite.subset h1 h2
  have : ∃ n ∈ dims, ∀ n' ∈ dims, n' ≤ n := by
    rcases Set.Finite.exists_maximal_wrt id dims this h with ⟨n, ⟨hndims, hn⟩⟩
    dsimp at hn; use n; apply And.intro hndims; intro n' hn'
    by_contra hc; simp only [Nat.gt_of_not_le] at hc
    have ha := hn n' hn' $ le_of_lt $ Nat.gt_of_not_le hc
    have hb := (ne_of_gt $ Nat.gt_of_not_le hc).symm
    contradiction
  rcases this with ⟨n, ⟨hndims, hnmax⟩⟩
  rcases (Set.mem_image fdim sms n).mp hndims with ⟨sm, ⟨hsms, fdimsmn⟩⟩
  use sm
  apply And.intro hsms
  intro sm' hsm' hsmsm'
  have : fdim sm' ≤ fdim sm := by
    rw [fdimsmn]
    exact hnmax (fdim sm') (Set.mem_image_of_mem fdim hsm')
  exact Submodule.eq_of_le_of_finrank_le hsmsm' this

  end «Finite dimensional spaces»

-- ********************************************************************
