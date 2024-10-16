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
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Algebra.Affine
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Normed.Module.FiniteDimension

import X2lib.Topology.PiecewiseLinear.Aux.Set
import X2lib.Topology.PiecewiseLinear.Aux.Topology
import X2lib.Topology.PiecewiseLinear.Aux.Affine
import X2lib.Topology.PiecewiseLinear.Aux.Module
import X2lib.Topology.PiecewiseLinear.AffineCone
import X2lib.Topology.PiecewiseLinear.AffineConeNhd
import X2lib.Topology.PiecewiseLinear.AffineHalfspace
import X2lib.Topology.PiecewiseLinear.AffinePolyhedron

/-!
# Cells

We introduce several perspectives on cells. It will then
be shown that (under certain assumptions) these notions
agree, giving us different ways to work with cells.

 [(i : ι) → AddCommMonoid (φ i)]

## Different definitions of cells

- `exists_foo`: the main existence theorem of `foo`s.

## References

See [Rourke] for ann introduction to PL-topology.
-/

universe u v w
open Set

namespace Affine

-- ********************************************************************
section «Definitions»

variable (𝕜 : Type u) [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P] [TopologicalSpace P]

/-- A polyhedral-cell is a polyhedron that is also a convex set -/
structure IsPCell (carrier : Set P) where
  /-- The carrier must be nonempty. -/
  is_nonempty : carrier.Nonempty
  /-- The set is a polyhedron. -/
  is_polyhedron : Polyhedron 𝕜 P carrier
  /-- The carrier is a convex set. -/
  is_convex : IsConvex 𝕜 P carrier

-- -------------------------------------------------------------------

/-- A vertex-spanned-cell is a set that is spanned by a finite set of vertices.
The set of vertices is minimal in the sense that no subset of the vertices
spans the set. -/
structure VCell {ι : Type*} (hf : Finset ι) [DecidableEq ι] [Nonempty ι] where
  /-- The vertices spanning the set. -/
  vertices : ι → P
  /-- The vertices form a minimal spanning set for the carrier. -/
  is_minimal : IsMinimalJoinedPoints 𝕜 P ι vertices

/-- A vertex-spanned-cell is a set that is spanned by a finite set of vertices.
The set of vertices is minimal in the sense that no subset of the vertices
spans the set. -/
structure IsVCell
    {ι : Type*} (hf : Finset ι) [DecidableEq ι] [Nonempty ι]
    (carrier : Set P) where
  /-- The vertices spanning the set. -/
  vertices : ι → P
  /-- The carrier is spanned by the vertices. -/
  is_joined_points : IsJoinedPoints 𝕜 P ι vertices carrier
  /-- The vertices form a minimal spanning set for the carrier. -/
  is_minimal : IsMinimalJoinedPoints 𝕜 P ι vertices

-- -------------------------------------------------------------------

-- This is needed to make the following defintion compile.
attribute [local instance] AffineSubspace.toAddTorsor

/-- A halfspace-cell is the intersection of finitely many halfspaces.
The defintion will not yet use the intersection of halfspaces, but we
show below that an halfspace-cell is in fact an intersection of
half-spaces. In order to avoid the axiom of choice this structure asks
that there is a witness for all of the halfspaces at once. -/
structure IsHCell
    [TopologicalSpace 𝕜]
    {ι : Type*}  (hf : Finset ι) [DecidableEq ι] [Nonempty ι]
    (carrier : Set P) where
  /-- The cell is defined in an affine subspace. -/
  subspace : AffineSubspace 𝕜 P
  /-- The subspace is closed. -/
  subspace_is_closed : IsClosed (subspace : Set P)
  /-- The subspace is not empty. -/
  subspace_nonempty: Nonempty subspace
  /-- The halfspaces defining the quadrant. -/
  halfspaces : ι → Halfspace 𝕜 ↥subspace
  /-- There is a witness for the halfspaces. -/
  has_witness : ∃  φ : ι → ↥subspace →ᴬ[𝕜] 𝕜, ( ∀ i : ι, (halfspaces i).is_witness (φ i) )
                                            ∧ ( carrier = { p : ↥subspace | ∀ i : ι, 0 ≤ (φ i) p} )

end «Definitions»

-- ********************************************************************
section «IsVCell»

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {ι : Type*} (hfi : Finset ι) [DecidableEq ι] [Nonempty ι]

namespace IsVCell

/-- The carrier given through weighted sums of vertices is nonempty. -/
theorem carrier_nonempty (hs : IsVCell 𝕜 P hfi s) : s.Nonempty :=
  by admit

/-- The carrier given through weighted sums of vertices is convex. -/
theorem carrier_is_convex (hs : IsVCell 𝕜 P hfi s) : IsConvex 𝕜 P s :=
  IsJoinedPoints.is_convex hs.vertices hs.is_joined_points

/-- The subspace spanned by the vertices. -/
def spanned_subspace (hs : IsVCell 𝕜 P hfi s) : AffineSubspace 𝕜 P :=
  affineSpan 𝕜 (hs.vertices '' univ)

/-- The subspace spanned by the vertices is finite dimensional. -/
def spanned_subspace_finite (hs : IsVCell 𝕜 P hfi s) :
    FiniteDimensional 𝕜 (hs.spanned_subspace).direction :=
  by admit

end IsVCell

end «IsVCell»

-- -------------------------------------------------------------------
section «IsVCell-IsPCell»

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {ι : Type*} (hfi : Finset ι) [DecidableEq ι] [Nonempty ι]

namespace IsVCell

/-- A cell given through weighted sums of vertices is a polyhedron. -/
theorem carrier_is_polyhedron [TopologicalSpace P] (hs : IsVCell 𝕜 P hfi s) : Polyhedron 𝕜 P s where
  topology_is_generated_by_cone_nhds := by
    admit
  is_locally_closed := by
    admit

/-- A set that satisfies `IsICell` also satisfies `IsPCell`. -/
def carrier_is_pcell [TopologicalSpace P] (hs : IsVCell 𝕜 P hfi s) : IsPCell 𝕜 P s where
  is_nonempty := hs.carrier_nonempty
  is_polyhedron := hs.carrier_is_polyhedron
  is_convex := hs.carrier_is_convex

end IsVCell

end «IsVCell-IsPCell»

-- -------------------------------------------------------------------
section «IsVCell-IsICell»

variable {𝕜 : Type u} [LinearOrderedField 𝕜] [CompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P]
variable {ι : Type*} (hfi : Finset ι) [DecidableEq ι] [Nonempty ι]

namespace IsVCell

/-- The subspace spanned by the vertices is closed. -/
theorem spanned_subspace_is_closed
    (hs : IsVCell 𝕜 P hfi s) : IsClosed $ (hs.spanned_subspace : Set P) := by
  have : FiniteDimensional 𝕜 (hs.spanned_subspace).direction := hs.spanned_subspace_finite
  exact AffineSubspace.closed_of_finiteDimensional' hs.spanned_subspace

/-- A set that satisfies `IsVCell` also satisfies `IsICell`. -/
def as_IsICell (hs : IsVCell 𝕜 P hfi s) : IsHCell 𝕜 P hfi s where
  subspace := hs.spanned_subspace
  subspace_is_closed := hs.spanned_subspace_is_closed
  subspace_nonempty := by admit
  halfspaces := by admit
  has_witness := by admit

end IsVCell

end «IsVCell-IsICell»

-- ********************************************************************
section «IsICell-IsPCell»

variable {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P]
variable {ι : Type*} (hfi : Finset ι) [DecidableEq ι] [Nonempty ι]

namespace IsICell

/-- The carrier is nonempty. -/
theorem carrier_nonempty (hs : IsHCell 𝕜 P hfi s) : s.Nonempty :=
  by admit

/-- This shows that the subspace involved in the defintion of `IsICell`
is `Nonempty`.-/
instance instNonempty_subspace (hc : IsHCell 𝕜 P hfi s) : (Nonempty hc.subspace)
  := hc.subspace_nonempty

/-- The carrier is a subset of the subspace of the cell. -/
theorem carrier_sub_subspace (hc : IsHCell 𝕜 P hfi s) : s ⊆  hc.subspace := by
  admit

/-- The carrier of a cell is the intersection of the halfspaces. -/
theorem carrier_eq_iInter (hc : IsHCell 𝕜 P hfi s) :
    s = ⋂ i : ι, hc.subspace.subtype '' (hc.halfspaces i) := by
  rcases hc.has_witness with ⟨φ, ⟨wφ, hφs⟩⟩
  simp only [hφs]
  ext x
  rw [Set.image, Set.mem_iInter, Set.mem_setOf]
  constructor
  · rintro ⟨y, ⟨hyφ, hyx⟩⟩; intro i
    rw [Set.image, Set.mem_setOf]
    use y
    simp
    have hh := Set.mem_setOf.mp hyφ i
    --have hhh := Halfspace.mem_halfspace (hc.halfspaces i) (wφ i)
    --rw [Halfspace.mem_halfspace $ wφ i]
    --apply And.intro $ Set.mem_setOf.mp hyφ i
    admit
  · admit

/-- The carrier of a cell is the intersection of the halfspaces. -/
theorem carrier_is_convex (hc : IsHCell 𝕜 P hfi s) : IsConvex 𝕜 P s := by
  admit

/-- A cell given by halfspaces is a polyhedron. -/
theorem carrier_is_polyhedron (hc : IsHCell 𝕜 P hfi s) : Polyhedron 𝕜 P s where
  topology_is_generated_by_cone_nhds := by
    admit
  is_locally_closed := by
    admit

/-- A set that satisfies `IsICell` also satisfies `IsPCell`. -/
def carrier_is_pcell (hc : IsHCell 𝕜 P hfi s) : IsPCell 𝕜 P s where
  is_nonempty := hc.carrier_nonempty
  is_polyhedron := hc.carrier_is_polyhedron
  is_convex := hc.carrier_is_convex

end IsICell

end «IsICell-IsPCell»

-- ********************************************************************
section «IsPCell»

variable {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P]

namespace IsPCell

/-- The carrier is closed. -/
theorem carrier_closed (hs : IsPCell 𝕜 P s) : IsClosed s :=
  by admit

end IsPCell

end «IsPCell»

-- ********************************************************************
section «Equivalences»

variable {𝕜 : Type u} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P]


end «Equivalences»
