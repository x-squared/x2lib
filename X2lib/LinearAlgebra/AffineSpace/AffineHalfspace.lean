/-
Copyright (c) 2024 Stephan Maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib

import X2lib.Aux.Set
import X2lib.Aux.Affine
import X2lib.Aux.Module

import X2lib.LinearAlgebra.AffineSpace.AffineHyperplane

/-!
# Affine halfspaces

In this section we introduce several different ways to view halfspaces.
We provide the necessary theorems to pass seamlessly from one view
to another.
-/

universe u v w
open Set

-- ********************************************************************
section «Definition»

namespace Affine

variable (𝕜 : Type u) [LinearOrderedRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- A halfspace is a set in an affine space that consists of all points
that are mapped by a nontrivial functional to the nonnegative elements
of the (necessarily) ordered base ring. -/
structure IsHalfspace (carrier : Set P) : Prop where
  /- There is a witness that defines the carrier. -/
  witness : ∃ φ : P →ᵃ[𝕜] 𝕜, Function.Nonconstant φ ∧ carrier = { p : P | 0 ≤ φ p }

/-- A halfspace is a set in an affine space that consists of all points
that are mapped by a nontrivial functional to the nonnegative elements
of the (necessarily) ordered base ring. -/
structure Halfspace
    (𝕜 : Type u) [LinearOrderedRing 𝕜]
    {V : Type v} [AddCommGroup V] [Module 𝕜 V]
    (P : Type w) [AddTorsor V P] where
  mk' ::
  /- The set defined by the halfspace. -/
  carrier : Set P
  /- There is a witness that defines the carrier. -/
  witness : ∃ φ : P →ᵃ[𝕜] 𝕜, Function.Nonconstant φ ∧ carrier = { p : P | 0 ≤ φ p }

end Affine

end «Definition»

-- --------------------------------------------------------------------
namespace Affine.Halfspace

section «Properties»

section «LinearOrderedRing»

variable {𝕜 : Type u} [LinearOrderedRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- This allows us to view the fact that as set `IsHalfspace`
as `Halfspace`.-/
instance instCoeSort_IsHalfspace_to_Halfspace : CoeSort (IsHalfspace 𝕜 P s) (Halfspace 𝕜 P) where
  coe h := {
    carrier := s
    witness := h.witness
  }

/-- This allows us to view a `Halfspace` as a `Set`.-/
instance : SetLike (Halfspace 𝕜 P) P where
  coe := carrier
  coe_injective' hs0 hs1 heq := by
    rcases hs0.witness with ⟨f0, ⟨nf0nc, hs0c⟩⟩
    rcases hs1.witness with ⟨f1, ⟨nf1nc, hs1c⟩⟩
    calc
      hs0 = ⟨hs0.carrier, hs0.witness⟩ := rfl
      _   = ⟨hs1.carrier, ⟨f0, ⟨nf0nc, heq ▸ hs0c⟩⟩⟩ := by simp only [heq]
      _   = ⟨hs1.carrier, ⟨f1, ⟨nf1nc, heq.symm ▸ hs1c⟩⟩⟩ := by simp only [heq]
      _  = hs1 := rfl

/-- The carrier of the halfspace is the set defined by the halfspace. -/
@[simp] theorem coe_carrier (s : Halfspace 𝕜 P) : ↑s = s.carrier := rfl

/-- This defines what it means to be a witness.  -/
def is_witness (s : Halfspace 𝕜 P) (φ : P →ᵃ[𝕜] 𝕜) : Prop :=
  Function.Nonconstant φ ∧ s = { p : P | 0 ≤ φ p }

/-- Create a hyperplane from a given affine map. -/
def mk (φ : P →ᵃ[𝕜] 𝕜) (h : Function.Nonconstant φ) : Halfspace 𝕜 P where
  carrier := { p : P | 0 ≤ φ p }
  witness := ⟨φ, h, rfl⟩

theorem mk_coe (φ : P →ᵃ[𝕜] 𝕜) (h : Function.Nonconstant φ) :
    ↑(Halfspace.mk φ h) = { p : P | 0 ≤ φ p } := by rfl

/-- The affine map that defines a halfspace is a witness for this halfspace. -/
theorem mk_witness (φ : P →ᵃ[𝕜] 𝕜)(h : Function.Nonconstant φ) :
    (Halfspace.mk φ h).is_witness φ := by
  rw [is_witness, mk_coe]; apply And.intro h; rfl

/-- Condition for a point to be ina halfspace once a witness is given. -/
theorem mem_halfspace (hs : Halfspace 𝕜 P) (hw : is_witness hs φ) :
    p ∈ hs ↔ 0 ≤ φ p := by
  admit

/-- A compatible map for a halfspace is a map that is nonnegative on
the carrier.  -/
def is_compatible_map (s : Halfspace 𝕜 P) (φ : P →ᵃ[𝕜] 𝕜) : Prop :=
  Function.Nonconstant φ ∧ ∀ p ∈ s.carrier, 0 ≤ φ p

/-- A compatible map for a halfspace is in fact a witness -/
theorem compatible_map_is_witness (s : Halfspace 𝕜 P) (hdef : s.is_compatible_map ψ) :
    s.is_witness ψ := by
  admit

/-- The boundary is the set of points in a halfspace that are mapped
to 0 values under a witnessing map.
TODO Show that this is well-defined -/
def boundary (s : Halfspace 𝕜 P) : Hyperplane 𝕜 P :=
  { p : P | ∃ φ : P →ᵃ[𝕜] 𝕜, s.is_witness φ ∧ 0 = φ p }

/-- The interior is the set of points in a halfspace that are mapped
to nonpositive values under a defining map.
TODO Show that this is well-defined -/
def interior (s : Halfspace 𝕜 P) : Set P :=
  { p : P | ∃ φ : P →ᵃ[𝕜] 𝕜, s.is_witness φ ∧ 0 < φ p }

/-- The interor of a `Halfspace` is a subset of the half-space. -/
theorem interior_is_subset (s : Halfspace 𝕜 P) :
    s.interior ⊆ s := by
  admit

/-- The complement of a halfspace is the set of points that are mapped
to negative values under a defining map. -/
theorem compl_eq (s : Halfspace 𝕜 P) : (↑s)ᶜ = { p : P | ∃ φ : P →ᵃ[𝕜] 𝕜, s.is_witness φ ∧ φ p < 0 } := by
  admit

end «LinearOrderedRing»

section «LinearOrderedCommRing»

variable {𝕜 : Type u} [LinearOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- A halfspace is convex. -/
theorem is_convex (s : Halfspace 𝕜 P) : Affine.IsConvex 𝕜 P s := by
  admit

end «LinearOrderedCommRing»

section «LinearOrderedField»

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- An `Affine.Halfspace.interior` is not empty. -/
theorem interior_nonempty (s : Halfspace 𝕜 P) : s.interior.Nonempty := by
  rcases s.witness with ⟨φ, hw⟩
  rcases (Function.neq_const_iff_exists φ).mp hw.left with ⟨p0, p1, hp⟩
  rw [interior, Set.nonempty_def]
  -- Auxiliary lemma to simplify case-by-case argument
  have aux : (q0 q1 : P) → (φ q0 < φ q1) → s.interior.Nonempty := by
    intro q0 q1 hlt
    if h0 : 0 < φ q1 then
      apply Set.nonempty_of_mem; rw [interior, Set.mem_setOf]; use φ
      apply And.intro hw
      exact h0
    else
      let p := ( (1 - φ q0) / (φ q0 - φ q1) ) • (q0 -ᵥ q1) +ᵥ q0
      suffices h : φ p = 1 by
        apply Set.nonempty_of_mem; rw [interior, Set.mem_setOf]; use φ
        apply And.intro hw
        exact h ▸ zero_lt_one
      simp only [p, AffineMap.map_vadd, LinearMapClass.map_smul, AffineMap.linearMap_vsub]
      simp only [AffineMap.linearMap_vsub, smul_eq_mul, vsub_eq_sub, vadd_eq_add]
      rw [div_eq_mul_inv, mul_assoc]; nth_rewrite 2 [mul_comm]; rw [Field.mul_inv_cancel]
      ring_nf
      exact sub_ne_zero_of_ne $ lt_or_lt_iff_ne.mp $ Or.inl hlt
  -- Now complete the proof
  cases lt_or_lt_iff_ne.mpr hp with
  | inl hlt => exact aux p0 p1 hlt
  | inr hgt => exact aux p1 p0 hgt

/-- A `Affine.HalfSpace` is not empty. -/
theorem nonempty (s : Halfspace 𝕜 P) : (s : Set P).Nonempty :=
  Set.Nonempty.mono s.interior_is_subset s.interior_nonempty

/-- The boundary `Affine.HalfSpace.boundary` of a halfspace is not empty. -/
theorem boundary_nonempty (s : Halfspace 𝕜 P) : (s.boundary : Set P).Nonempty := by
  admit

end «LinearOrderedField»

end «Properties»

end Affine.Halfspace

-- --------------------------------------------------------------------
section «Closed Halfspaces»

/-!
## Closed halfspaces

This section passes fron the algebraic to the topological category.
Once we assume continuity (of maps), halfspaces will be closed sets.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜] [NontriviallyNormedField 𝕜] [TopologicalSpace 𝕜] [LocallyCompactSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [T2Space V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P] [TopologicalAddTorsor V P]

namespace Affine.Halfspace

/-- Every witness of a hyperplane is in fact continuous. -/
@[continuity]
theorem witness_is_continuous (h : Halfspace 𝕜 P) (hc : IsClosed (h : Set P))
    {φ : P →ᵃ[𝕜] 𝕜} (hn : h.is_witness φ) : Continuous φ := by
  admit

/-- The hyperplane is the nullspace of continuous affine maps to the
ground ring. -/
theorem witness_continuous (h : Halfspace 𝕜 P) (hc : IsClosed (h : Set P)) :
    ∃ φ : P →ᴬ[𝕜] 𝕜, Function.Nonconstant φ ∧ h = { p : P | 0 ≤ φ p } := by
  rcases h.witness with ⟨φ, hφ⟩
  use ⟨φ, h.witness_is_continuous hc hφ⟩
  exact hφ

end Affine.Halfspace

end «Closed Halfspaces»

-- --------------------------------------------------------------------
