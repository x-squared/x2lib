/-
Copyright (c) 2024 Stephan Maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib

import X2lib.Aux.Set
import X2lib.Aux.Affine
import X2lib.Aux.Module

/-!
# Affine hyperplanes

In this section we introduce several different ways to view hyperplanes.
We provide the necessary theorems to pass seamlessly from one view
to another.
-/

open Set

-- ********************************************************************
section «Hyperplane definitions»

/-!
## Definitions

Hyperplanes cnabe viewed in many ways, for example as null-spaces of
affine maps (see `Affine.IsNullspace`) or as affine subspaces of codimension 1
(see `Affine.IsCodimOneSubspace`).

The notion of hyperplane will be defined through the structure `Affine.Hyperplane`.
The structure will then be extended through defintions and theorems which
allow to pass seamlessly between the various points of view.
-/

-- --------------------------------------------------------------------
namespace AffineSubspace

variable (𝕜 : Type u) [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- An affine subspace is a nullspace iff it is the preimage of `0` of an affine map to the base ring. -/
def IsNullspace (a : AffineSubspace 𝕜 P) : Prop :=
  ∃ φ : P →ᵃ[𝕜] 𝕜, Function.Nonconstant φ ∧ a = { p : P | φ p = 0 }

/-- An affine subspace is a codimension-1 subspace iff there is a point such
that the susbapce and the point together span the entire ambient affine space. -/
def IsCodimOneSubspace (a : AffineSubspace 𝕜 P) : Prop :=
  ∃ x ∉ a, spanPoints 𝕜 ( a ∪ { x } ) = univ

end AffineSubspace

-- --------------------------------------------------------------------
variable (𝕜 : Type u) [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- A hyperplane is a codimension-1 affine subspace that results from
an affine map to the base ring. -/
structure Affine.Hyperplane extends AffineSubspace 𝕜 P where
  mk' ::
  /-- The hyperplane is witnessed by affine maps to the base-ring. -/
  is_nullspace : toAffineSubspace.IsNullspace

/-- This allows us to view a `Affine.Hyperplane` as a `Set`.-/
instance Affine.instSetLikeHyperplane : SetLike (Affine.Hyperplane 𝕜 P) P where
  coe hyp := hyp.carrier
  coe_injective' h0 h1 h := by
    dsimp at h
    have ha0a1 := (inferInstance : SetLike (AffineSubspace 𝕜 P) P).coe_injective h
    calc
      h0 = ⟨h0.toAffineSubspace, h0.is_nullspace⟩ := rfl
      _  = ⟨h1.toAffineSubspace, h1.is_nullspace⟩ := by simp only [ha0a1, h]
      _  = h1 := rfl

/-- A defining map for a hyperplane is an affine map that defines the
hyperplane. -/
def Affine.Hyperplane.IsNullspaceWitness (hp : Affine.Hyperplane 𝕜 P) (φ : P →ᵃ[𝕜] 𝕜) : Prop :=
  Function.Nonconstant φ ∧ hp = { p : P | φ p = 0 }

end «Hyperplane definitions»

-- --------------------------------------------------------------------
section «Hyperplane Properties»

variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Hyperplane

/-- Create a hyperplane from a given affine map. -/
def mk (φ : P →ᵃ[𝕜] 𝕜) (h : Function.Nonconstant φ) : Hyperplane 𝕜 P where
  carrier := (AffineSubspace.comap φ (AffineSubspace.singleton 𝕜 𝕜 (0:𝕜) )).carrier
  smul_vsub_vadd_mem := by
    intro k _ _ _ h0 h1 h2
    exact (AffineSubspace.comap φ (AffineSubspace.singleton 𝕜 𝕜 (0:𝕜) )).smul_vsub_vadd_mem k h0 h1 h2
  is_nullspace := by
    use φ; apply And.intro h
    simp only [AffineSubspace.comap, Set.preimage, AffineSubspace.mem_coe, AffineSubspace.mem_singleton_iff_eq]
    rfl

/-- The nullset defined by an affine map is the carrier of the hyperplane
defined by  `Affine.Hyperplane.mk`. -/
theorem mk_coe_set (φ : P →ᵃ[𝕜] 𝕜)(h : Function.Nonconstant φ) :
  ↑(Hyperplane.mk φ h) = { p : P | φ p = 0 } := by rfl

/-- The affine map that defines a hyperplane through `Affine.Hyperplane.mk`
is a witness for this hyperplane. -/
theorem mk_nullspace_witness (φ : P →ᵃ[𝕜] 𝕜)(h : Function.Nonconstant φ) :
    (Hyperplane.mk φ h).IsNullspaceWitness 𝕜 P φ := by
  rw [Affine.Hyperplane.IsNullspaceWitness, mk_coe_set]; apply And.intro h; rfl

end Affine.Hyperplane

end «Hyperplane Properties»

-- --------------------------------------------------------------------
section «Hyperplane Nullspace-Codim-1 Equivalence»

/-!
## Equivalence of points of view

In this section we show that the various ways of viewing hyperplanes are
equivalent.
-/

namespace AffineSubspace

variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- An affine subspace that satisfies `AffineSubspace.IsNullspace` also satisfies
`AffineSubspace.IsCodimOneSubspace`. -/
theorem is_nullspace_impl_is_codim1 (a : AffineSubspace 𝕜 P) (h : a.IsNullspace) :
    a.IsCodimOneSubspace := by
  rcases h with ⟨φ, hφ, hp⟩
  rcases (Function.neq_const_iff_exists φ).mp hφ with ⟨y, z, hyz⟩
  have : ∃ x : P, φ x ≠ 0 := by
    if h0 : φ y = 0 then use z; rw [←h0]; exact hyz.symm
    else use y
  rcases this with ⟨x, hx⟩
  -- Show there is a point in the affine subspace
  let x0 := (φ y) • (φ y - φ z)⁻¹ • (z -ᵥ y) +ᵥ y
  have : φ x0 = 0 := by admit
  -- Show there is a point which maps to 1 under φ
  let x1 := (φ x)⁻¹ • (x -ᵥ x0) +ᵥ x0
  have : φ x1 = 1 := by admit
  use x1
  have : x1 ∉ a := by by_contra; admit
  apply And.intro this
  -- Now complete argument
  suffices univ ⊆ (affineSpan 𝕜 (↑a ∪ {x1}) : Set P) by
    exact Set.eq_of_subset_of_subset (Set.subset_univ (spanPoints 𝕜 (↑a ∪ {x1}))) this
  simp only [Set.subset_def]
  intro p; simp
  admit

-- Submodule.mem_span_insert

/-- Given an afine subspace and a point ` p` not contained in the subspace, the set
of `spanPoints` of the union of the affine subspace and the point is the union of
lines that connect points in the affine supspace to `p`. The theorem is here stated
in its most direct form. -/
private theorem affineSpan_of_affineSubspace_and_point (a : AffineSubspace 𝕜 P) (hp : p ∉ a) :
    spanPoints 𝕜 ( a ∪ { p } ) = { q : P | ∃ q₀ ∈ a, ∃ k : 𝕜, q = k • (p -ᵥ q₀) +ᵥ q₀} := by
  -- Auxiliary result
  --let hSpanPoints : spanPoints 𝕜 ( a ∪ { p } ) = { x : P | ∃ ∨ : Submodule.span 𝕜 (Set.insert (p -ᵥ q) a.direction), x = v +ᵥ q } := by
    --admit
  ext q; simp only [spanPoints, mem_setOf]
  apply Iff.intro
  · rintro ⟨q0, hq0, v0, hv0, hqq0v0⟩
    admit
  · admit

/-- An affine subspace that satisfies `AffineSubspace.IsCodimOneSubspace` also satisfies
`AffineSubspace.IsNullspace`. -/
theorem is_codim1_impl_is_nullspace (a : AffineSubspace 𝕜 P) (h : a.IsCodimOneSubspace) :
    a.IsNullspace := by
  admit

/-- An affine subspace satisfies `AffineSubspace.IsNullspace` iff if it satisfies
`AffineSubspace.IsCodimOneSubspace`. -/
theorem is_nullspace_iff_is_codim1 (a : AffineSubspace 𝕜 P) :
    a.IsNullspace ↔ a.IsCodimOneSubspace :=
  Iff.intro a.is_nullspace_impl_is_codim1 a.is_codim1_impl_is_nullspace

/-- An affine subspace that satisifies  `AffineSubspace.IsNullspace` is a `Affine.Hyperplane`. -/
def hyperplane_from_nullspace (a : AffineSubspace 𝕜 P) (h : a.IsNullspace) : Affine.Hyperplane 𝕜 P where
  carrier := a.carrier
  smul_vsub_vadd_mem := a.smul_vsub_vadd_mem
  is_nullspace := h

/-- An affine subspace that satisifies  `AffineSubspace.IsNullspace` is a `Affine.Hyperplane`. -/
def hyperplane_from_codim1 (a : AffineSubspace 𝕜 P) (hp : a.IsCodimOneSubspace) : Affine.Hyperplane 𝕜 P where
  carrier := a.carrier
  smul_vsub_vadd_mem := a.smul_vsub_vadd_mem
  is_nullspace := a.is_codim1_impl_is_nullspace hp

/-- An instance of `Affine.Hyperplane` satisfies `AffineSubspace.IsCodimOneSubspace`. -/
theorem is_codimOneSubspace (a : Affine.Hyperplane 𝕜 P) :
    AffineSubspace.IsCodimOneSubspace 𝕜 P a.toAffineSubspace := a.is_nullspace_impl_is_codim1 a.is_nullspace

/- This allows us to view the fact that an affine subspace `IsNullspace`
as `Hyperplane`.-/
instance instCoeSortIsHyperplanToHyperplane : CoeSort (IsNullspace 𝕜 P a) (Affine.Hyperplane 𝕜 P) where
  coe h := ⟨a, h⟩

/- This allows us to view the fact that an affine subspace `IsCodimOneSubspace`
as `Hyperplane`.-/
instance instCoeSortIsCodimOneSubspaceToHyperplane : CoeSort (IsCodimOneSubspace 𝕜 P a) (Affine.Hyperplane 𝕜 P) where
  coe := hyperplane_from_codim1 a

end AffineSubspace

end «Hyperplane Nullspace-Codim-1 Equivalence»

-- --------------------------------------------------------------------
section «Sets as hyperplanes»

/-!
## Sets that are hyperplanes

This section shows how to describe `Set`s as hyperplanes. This section
serves to transfer statements about hyperplanes to statements about sets
that are the carriers of hyperplanes. This allows you to pass from such
sets to the language of affines spaces.
-/

variable (𝕜 : Type u) [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

namespace Set
open Affine
open Affine.Hyperplane

/-- A set is a nullspace iff it is the preimage of `0` of an affine map to the base ring. -/
def IsNullspace (s : Set P) : Prop := ∃ φ : P →ᵃ[𝕜] 𝕜, Function.Nonconstant φ ∧ s = { p : P | φ p = 0 }

/-- A set is a codimension-1 subspace iff it is a codimension-1 affine subspace. -/
def IsCodimOneSubspace (s : Set P) : Prop :=
  ∃ a : AffineSubspace 𝕜 P, s = a ∧ a.IsCodimOneSubspace

/-- A set that satisfies `IsNullspace` uniquely defines a `Hyperplane`. -/
theorem IsNullspace_as_hyperplane (hs : IsNullspace 𝕜 P s) :
    ∃! a : Hyperplane 𝕜 P, s = a := by
  admit

/-- A set that satisfies `IsCodimOneSubspace` uniquely defines a `Hyperplane`. -/
theorem IsCodimOneSubspace_as_hyperplane (hs : IsCodimOneSubspace 𝕜 P s) :
    ∃! a : Hyperplane 𝕜 P, s = a := by
  admit

end Set

end «Sets as hyperplanes»

-- --------------------------------------------------------------------
section «Hyperplane in inner produce spaces»

/-!
## Hyperplanes in inner product spaces
TODO Inner Product Spaces

Note: We regret that `InnerProductSpace`s are defined using the condition
`RCLike` on the base ring. We only need algebraic properties, but `RCLike`
forces us to assume completeness, which is not required.
-/

variable (𝕜 : Type u) [Ring 𝕜] [RCLike 𝕜]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [Module 𝕜 V]
variable (P : Type w) [MetricSpace P] [NormedAddTorsor V P]

end «Hyperplane in inner produce spaces»

-- --------------------------------------------------------------------
section «Various properties of hyperplanes»

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Hyperplane

/-- `Affine.Hyperplane`s are convex. -/
theorem is_convex (h : Hyperplane 𝕜 P)  : Affine.IsConvex 𝕜 P h :=
  h.toAffineSubspace.is_convex

end Affine.Hyperplane

end «Various properties of hyperplanes»

-- --------------------------------------------------------------------
section «Closed Hyperplane»

/-!
## Closed hyperplanes

This section passes fron the algebraic to the topological category.
Once we assume continuity (of maps), hyperplanes will be closed sets.
-/

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [TopologicalSpace 𝕜] [LocallyCompactSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [T2Space V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P] [TopologicalAddTorsor V P]

namespace Affine.Hyperplane
open Set

/-- Every witness of a hyperplane is in fact continuous. -/
@[continuity]
theorem nullspace_witness_is_continuous (h : Hyperplane 𝕜 P) (hc : IsClosed (h : Set P))
    (hn : h.IsNullspaceWitness _ _ φ) : Continuous φ := by
  --exact LinearMap.continuous_iff_isClosed_ker
  admit

/-- The hyperplane is the nullspace of continuous affine maps to the
ground ring. -/
theorem is_nullspace_of_continuous_map (h : Hyperplane 𝕜 P) (hc : IsClosed (h : Set P)) :
    ∃ φ : P →ᴬ[𝕜] 𝕜, Function.Nonconstant φ ∧ h = { p : P | φ p = 0 } := by
  rcases h.is_nullspace with ⟨φ, hφ⟩
  use ⟨φ, h.nullspace_witness_is_continuous hc hφ⟩
  exact hφ

end Affine.Hyperplane

end «Closed Hyperplane»

-- --------------------------------------------------------------------
