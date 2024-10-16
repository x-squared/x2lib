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
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Topology.Algebra.Affine
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.LinearAlgebra.Ray

import X2lib.Topology.PiecewiseLinear.Aux.Set
import X2lib.Topology.PiecewiseLinear.Aux.Topology
import X2lib.Topology.PiecewiseLinear.Aux.Affine
import X2lib.Topology.PiecewiseLinear.Aux.Module
import X2lib.Topology.PiecewiseLinear.AffineCone
import X2lib.Topology.PiecewiseLinear.AffineConeNhd
import X2lib.Topology.PiecewiseLinear.AffinePolyhedron

/-!
# Affine hyperplanes

In this section we introduce several different ways to view hyperplanes.
We provide the necessary theorems to pass seamlessly from one view
to another.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Rourke] for ann introduction to PL-topology.
-/

universe u v w
open Set

-- ********************************************************************
section «Hyperplane»

/-!
## Definitions

-/

-- --------------------------------------------------------------------
section «Hyperplane Definitions»

namespace AffineSubspace

variable {𝕜 : Type u} [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- An affine subspace is a nullspace iff it is the preimage of `0` of an affine map to the base ring. -/
def IsNullspace (a : AffineSubspace 𝕜 P) : Prop :=
  ∃ φ : P →ᵃ[𝕜] 𝕜, Function.Nonconstant φ ∧ a = { p : P | φ p = 0 }

/-- An affine subspace is a codimension-1 subspace iff there is a point such
that the susbapce and the point together span the entire ambient affine space. -/
def IsCodimOneSubspace (a : AffineSubspace 𝕜 P) : Prop :=
  ∃ x ∉ a, spanPoints 𝕜 ( a ∪ { x } ) = univ

end AffineSubspace

variable (𝕜 : Type u) [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- A hyperplane is a codimension-1 affine subspace that results from
an affine map to the base ring. -/
structure Affine.Hyperplane extends AffineSubspace 𝕜 P where
  mk' ::
  /-- The hyperplane is witnessed by affine maps to the base-ring. -/
  is_nullspace : toAffineSubspace.IsNullspace

/-- A set is a nullspace iff it is the preimage of `0` of an affine map to the base ring. -/
def Set.IsNullspace (s : Set P) : Prop := ∃ φ : P →ᵃ[𝕜] 𝕜, Function.Nonconstant φ ∧ s = { p : P | φ p = 0 }

/-- A set is a codimension-1 subspace iff it is a codimension-1 affine subspace. -/
def Set.IsCodimOneSubspace (s : Set P) : Prop :=
  ∃ a : AffineSubspace 𝕜 P, s = a ∧ a.IsCodimOneSubspace

end «Hyperplane Definitions»

-- --------------------------------------------------------------------
section «Hyperplane Properties»

namespace Affine.Hyperplane

variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- This allows us to view a `Hyperplane` as a `Set`.-/
instance : SetLike (Hyperplane 𝕜 P) P where
  coe hyp := hyp.carrier
  coe_injective' h0 h1 h := by
    dsimp at h
    have ha0a1 := (inferInstance : SetLike (AffineSubspace 𝕜 P) P).coe_injective h
    calc
      h0 = ⟨h0.toAffineSubspace, h0.is_nullspace⟩ := rfl
      _  = ⟨h1.toAffineSubspace, h1.is_nullspace⟩ := by simp only [ha0a1, h]
      _  = h1 := rfl

/- This allows us to view the fact that an affine subspace `IsHyperplane`
as `Hyperplane`.-/
-- instance instCoeSort_IsHyperplane_to_Hyperplane : CoeSort (IsHyperplane 𝕜 P s) (Hyperplane 𝕜 P) where
--   coe h := {
--     carrier := s
--     smul_vsub_vadd_mem := by
--      rcases h.nullspace_witness with ⟨φ, _, hs⟩
--      let a : AffineSubspace 𝕜 P := AffineSubspace.comap φ (AffineSubspace.singleton 𝕜 𝕜 (0:𝕜))
--      have : s = a := by
--        rw [AffineSubspace.coe_comap, AffineSubspace.singleton_coe, Set.preimage, hs]; simp
--      rw [this]
--      intro k _ _ _ h0 h1 h2
--      exact (AffineSubspace.comap φ (AffineSubspace.singleton 𝕜 𝕜 (0:𝕜) )).smul_vsub_vadd_mem k h0 h1 h2
--     nullspace_witness := h.nullspace_witness
--   }

/-- A defining map for a hyperplane is an affine map that defines the
hyperplane.  -/
def is_nullspace_witness (hp : Hyperplane 𝕜 P) (φ : P →ᵃ[𝕜] 𝕜) : Prop :=
  Function.Nonconstant φ ∧ hp = { p : P | φ p = 0 }

/-- Create a hyperplane from a given affine map. -/
def mk (φ : P →ᵃ[𝕜] 𝕜) (h : Function.Nonconstant φ) : Hyperplane 𝕜 P where
  carrier := (AffineSubspace.comap φ (AffineSubspace.singleton 𝕜 𝕜 (0:𝕜) )).carrier
  smul_vsub_vadd_mem := by
    intro k _ _ _ h0 h1 h2
    exact (AffineSubspace.comap φ (AffineSubspace.singleton 𝕜 𝕜 (0:𝕜) )).smul_vsub_vadd_mem k h0 h1 h2
  is_nullspace := by
    use φ; apply And.intro h
    simp only [AffineSubspace.comap, Set.preimage, AffineSubspace.mem_coe, AffineSubspace.mem_singleton_iff_eq]


/-- The affine map that defines a hyperplane is a witness for this hyperplane. -/
theorem mk_coe (φ : P →ᵃ[𝕜] 𝕜)(h : Function.Nonconstant φ) :
  ↑(Hyperplane.mk φ h) = { p : P | φ p = 0 } := by rfl

/-- The affine map that defines a hyperplane is a witness for this hyperplane. -/
theorem mk_nullspace_witness (φ : P →ᵃ[𝕜] 𝕜)(h : Function.Nonconstant φ) :
    (Hyperplane.mk φ h).is_nullspace_witness φ := by
  rw [is_nullspace_witness, mk_coe]; apply And.intro h; rfl

end Affine.Hyperplane

end «Hyperplane Properties»

-- --------------------------------------------------------------------
section «Hyperplane Nullspace-Codim-1 Equivalence»

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
  let hSpanPoints : spanPoints 𝕜 ( a ∪ { p } ) = { x : P | ∃ ∨ : Submodule.span 𝕜 (Set.insert (p -ᵥ q) a.direction), x = v +ᵥ q } := by
    admit
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
    AffineSubspace.IsCodimOneSubspace a.toAffineSubspace := a.is_nullspace_impl_is_codim1 a.is_nullspace

end AffineSubspace

end «Hyperplane Nullspace-Codim-1 Equivalence»

-- --------------------------------------------------------------------
section «Hyperplane in Euclidean Space»



end «Hyperplane in Euclidean Space»

-- --------------------------------------------------------------------
section «Closed Hyperplane Definitions»

/-!
## Closed hyperplanes

-/

variable (𝕜 : Type u) [Ring 𝕜] [TopologicalSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P] [TopologicalSpace P]

/-- A closed hyperplane is a hyperplane that is closed as a set. -/
structure Affine.ClosedHyperplane extends Affine.Hyperplane 𝕜 P where
  mk' ::
  /-- The hyperplane is closed as a set. -/
  is_closed : IsClosed carrier

/-- Every closed hyperplane is a hyperplane. -/
instance Affine.ClosedHyperplane.instCoeSort_ClosedHyperplane_to_Hyperplane : CoeSort (ClosedHyperplane 𝕜 P) (Hyperplane 𝕜 P) where
  coe := toHyperplane

end «Closed Hyperplane Definitions»

-- --------------------------------------------------------------------
section «Closed Hyperplane Properties»

variable {𝕜 : Type u} [Ring 𝕜] [TopologicalSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P]

open Affine.Hyperplane

namespace Affine.ClosedHyperplane

/-- Every witness of a hyperplane is in fact continuous. -/
@[continuity]
theorem nullspace_witness_continuous (ch : ClosedHyperplane 𝕜 P)
    (h : ch.is_nullspace_witness φ) : Continuous φ := by
  admit

/-- The hyperplane is the nullspace of continuous affine maps to the
ground ring. -/
theorem is_cont_nullspace (ch : ClosedHyperplane 𝕜 P) :
    ∃ φ : P →ᴬ[𝕜] 𝕜, Function.Nonconstant φ ∧ ch = { p : P | φ p = 0 } := by
  rcases ch.is_nullspace with ⟨φ, hφ⟩
  use ⟨φ, ch.nullspace_witness_continuous hφ⟩
  exact hφ

end Affine.ClosedHyperplane

end «Closed Hyperplane Properties»

-- --------------------------------------------------------------------
end «Hyperplane»
