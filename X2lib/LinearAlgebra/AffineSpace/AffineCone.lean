/-
Copyright (c) 2024 Stephan Maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib

import X2lib.Aux.Set
import X2lib.Aux.Affine
import X2lib.Aux.Module

import X2lib.LinearAlgebra.AffineSpace.AffineJoin

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
open Set

-- ********************************************************************
section «Affine Cone Def»

namespace Affine

/-!
## Affine cone

The main construction of elementary PL-objects (in affine space) is given
by `Affine.Cone`. A cone results from taking union of all lines that connect
a given point, the vertex, to a gviven set, the base. To make become a useful
device the lines between vertex and base do not intersect (apart from the
vertex) unless they are identical.

The defintion of `Affine.Cone` includes the essential sets that result from
the definition as we will later extend the definition into the topological
realm, and we will then need to access these definitions.

An `Affine.Join` is an `Affine.Cone`, but the definition does not make
this explicit as the terminology of join and cone are different. Instead,
a coercion is provided that shows this relation.

Note that affine cones determine sets in the ambient affine space. Affine cones
cannot, however, implement the `SetLike` interface as the same set can be
written as a cone in many ways. Compare, however, `carrier_eq_iff_eq`
which shows that cones are uniquely determined by their sets once the vertex
of the cone is given.
-/

variable (𝕜 : Type u) [LinearOrderedField 𝕜]
variable (V : Type v) [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- An affine cone is an affine join, where `side0` consists of only one point,
called the vertex. -/
structure Cone where
  /-- This is the tip of the cone. -/
  vertex : P
  /-- The base. -/
  base : Set P
  /-- The cone must not be in the cone's base. -/
  vertex_not_in_base : vertex ∉ base
  /-- If lines from the vertex to two base-points intersect the base-points are the same. -/
  lines_intersect_eq_base_points
    (hb : b ∈ base) (hb' : b' ∈ base) (hi : Affine.segmentOO 𝕜 vertex b ∩ Affine.segmentOO 𝕜 vertex b' ≠ ∅ ) : b = b'
  /-- The points in the ambient space that lie on the segments connecting the vertex
  to base point (endpoints excluded). -/
  segment_points : Set P := ⋃ b : base, Affine.segmentOO 𝕜 vertex b
  /-- The defintion of `segment_points`. -/
  segment_points_def : segment_points = ⋃ b : base, Affine.segmentOO 𝕜 vertex b := by simp
  /-- The carrier is the set of points defined by an affine join. -/
  carrier : Set P := { vertex } ∪ base ∪ segment_points
  /-- The defintion of the carrier. -/
  carrier_def : carrier = { vertex } ∪ base ∪ segment_points := by simp
  /-- The carrier's interior of an `Cone` is the set consisting of the vertex
  and the segment points. -/
  carrier_interior : Set P := { vertex } ∪ segment_points
  /-- The defintion of the carrier. -/
  carrier_interior_def : carrier_interior = { vertex } ∪ segment_points := by simp

/-- An affine cone is an affine join, where `side0` consists of only one point,
called the vertex. -/
structure IsCone (vertex : P) (base : Set P) : Prop where
  /-- The cone must not be in the cone's base. -/
  vertex_not_in_base : vertex ∉ base
  /-- If lines from the vertex to two base-points intersect the base-points are the same. -/
  lines_intersect_eq_base_points
    (hb : b ∈ base) (hb' : b' ∈ base) (hi : Affine.segmentOO 𝕜 vertex b ∩ Affine.segmentOO 𝕜 vertex b' ≠ ∅ ) : b = b'

end Affine

namespace Set

/-- A set is an affine cone...
TODO. -/
structure IsConeCarrier (s : Set P) (vertex : P) : Prop where

end Set

end «Affine Cone Def»

-- ********************************************************************
section «Cone basics»

/-!
## Basic of cones

In this section we look at the structure of cones and show that an affine
cone is an affine join. This is exhibited by the map `Cone.toJoin`.
 -/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

open Affine

-- -------------------------------------------------------------------
section «Basics»

/-- This allows us to transform the condition `IsCone` to a `Cone`. -/
def IsCone.to_Cone (h : IsCone 𝕜 V P v b) : Cone 𝕜 V P where
  vertex := v
  base := b
  vertex_not_in_base := h.vertex_not_in_base
  lines_intersect_eq_base_points := h.lines_intersect_eq_base_points

end «Basics»

namespace Affine.Cone

-- -------------------------------------------------------------------
section «Affine cone equality»

/-!
### Equality of joins

Two cones are equal iff their vertices and bases are equal.
 -/

/-- Affine joins with equal vertices and bases have equal segment
oint sets. -/
theorem eq_vertex_base_eq_segment_points (c c': Cone 𝕜 V P) (heq : c.vertex = c'.vertex ∧ c.base = c'.base) :
    c.segment_points = c'.segment_points := by
  ext x
  simp only [segment_points_def, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨b, hb⟩, hh⟩; simp [heq.left] at hh
    use ⟨b, heq.right ▸ hb⟩
  · rintro ⟨⟨b, hb⟩, hh⟩; simp [←heq.left] at hh
    use ⟨b, heq.right ▸ hb⟩

/-- Affine joins with equal vertices and bases have equal carriers. -/
theorem eq_vertex_base_eq_carrier (c c': Cone 𝕜 V P) (heq : c.vertex = c'.vertex ∧ c.base = c'.base) :
    c.carrier = c'.carrier := by
  ext x
  simp only [carrier_def, heq.left, heq.right, eq_vertex_base_eq_segment_points c c' heq]

/-- Affine joins with equal vertices and bases have equal carrier interiors. -/
theorem eq_vertex_base_eq_carrier_interior (c c': Cone 𝕜 V P) (heq : c.vertex = c'.vertex ∧ c.base = c'.base) :
    c.carrier_interior = c'.carrier_interior := by
  ext x
  simp only [carrier_interior_def, heq.left, heq.right, eq_vertex_base_eq_segment_points c c' heq]

/-- Two affine cones are equal iff their vertices and bases are equal.
The theorem `carrier_eq_iff_eq` shows that two affine cones based at
the same vertex are equal iff their carriers are equal. -/
theorem eq (c c': Cone 𝕜 V P) : c = c' ↔ c.vertex = c'.vertex ∧ c.base = c'.base := by
  constructor
  · intro h; rw [h]; simp
  · rintro h
    calc
      c = ⟨ c.vertex, c.base, c.vertex_not_in_base, c.lines_intersect_eq_base_points, c.segment_points, c.segment_points_def, c.carrier, c.carrier_def, c.carrier_interior, c.carrier_interior_def ⟩ := rfl
      _ = ⟨ c'.vertex, c'.base, c'.vertex_not_in_base, c'.lines_intersect_eq_base_points, c'.segment_points, c'.segment_points_def, c'.carrier, c'.carrier_def, c'.carrier_interior, c'.carrier_interior_def ⟩ := by
        simp only [h.left, h.right, eq_vertex_base_eq_segment_points c c' h, eq_vertex_base_eq_carrier c c' h, eq_vertex_base_eq_carrier_interior c c' h]
      _ = c' := rfl

end «Affine cone equality»

/- ---------- Join ------------------------------------------------- -/
section «Affine cone is join»

/-!
### Affine cones are affine joins

This section provides the translation between affine cones and affine
joins.
 -/

/-- This allows us to view the condition `IsCone` as a `Cone`. -/
instance CoeSort_IsCone_to_Cone : CoeSort (IsCone 𝕜 V P v b) (Cone 𝕜 V P) where
  coe := IsCone.to_Cone

/-- This allows us to view a `Affine.Join` as a `Set P`. The set is the
carrier of the join. -/
instance CoeSort_Cone_to_Set : CoeSort (Cone 𝕜 V P) (Set P) where coe := carrier

/-- An affine `Cone` is an affine `Join`. -/
def toJoin (c : Cone 𝕜 V P) : Join 𝕜 V P where
  side0 := { c.vertex }
  side1 := c.base
  sides_disjoint := by
    rw [Set.inter_comm, Set.inter_singleton_eq_empty]; exact c.vertex_not_in_base
  lines_do_not_intersect := by
    intro a b a' b' ha hb ha' hb'
    rw [Set.mem_singleton_iff] at ha; rw [Set.mem_singleton_iff] at ha'
    rw [ha, ha']
    intro h; simp only [true_and]
    exact c.lines_intersect_eq_base_points hb hb' h

/-- This coerces `Cone` to `Join`.-/
instance CoeSort_to_Join: CoeSort (Cone 𝕜 V P) (Join 𝕜 V P) where
  coe := toJoin

/-- The vertex is the only element of `Join.side0`. -/
theorem vertex_toJoin_side0 (c : Cone 𝕜 V P) : c.toJoin.side0 = { c.vertex } := by
  simp only [Cone.toJoin]

/-- The vertex is in `Join.side0`. -/
theorem vertex_toJoin_in_side0 (c : Cone 𝕜 V P) : c.vertex ∈ c.toJoin.side0 :=
  Set.mem_singleton c.vertex

/-- The base is `Join.side1` of the join. -/
theorem base_toJoin_side1 (c : Cone 𝕜 V P) : c.toJoin.side1 = c.base := rfl

/-- The segment-point sets are the same for cone and join. -/
theorem segment_points_toJoin_segment_points (c : Cone 𝕜 V P) : c.segment_points = c.toJoin.segment_points := by
  simp only [segment_points_def, Join.segment_points_def]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨b, hxb⟩; use ⟨⟨c.vertex, c.vertex_toJoin_in_side0⟩, b⟩
  · rintro ⟨⟨v, b⟩, h⟩; simp at h; use b

/-- The carriers of an affine cone and the affine join it represents
are the same. -/
theorem carrier_toJoin_same (c : Cone 𝕜 V P) :
    c.toJoin.carrier = c.carrier := by
  simp only [carrier_def, Join.carrier_def, vertex_toJoin_side0, base_toJoin_side1,
    segment_points_toJoin_segment_points]

/-- The carrier interior of an affine cone and the `Join.carrier_interior0`
of the affine join it represents are the same. -/
theorem carrier_interior_toJoin_carrier_interior0 (c : Cone 𝕜 V P) :
    c.toJoin.carrier_interior0 = c.carrier_interior := by
  simp only [carrier_interior_def, Join.carrier_interior0_def, vertex_toJoin_side0,
    base_toJoin_side1, segment_points_toJoin_segment_points]

/-- Two affine cones are equal iff they are equals as joins. -/
theorem eq_iff_toJoin_eq (c c' : Cone 𝕜 V P) : c = c' ↔ c.toJoin = c'.toJoin := by
  rw [Join.eq, Cone.eq, vertex_toJoin_side0, vertex_toJoin_side0, base_toJoin_side1, base_toJoin_side1, singleton_eq_singleton_iff]

end «Affine cone is join»

/- ---------- Sets ------------------------------------------------------ -/
section «Affine cone sets»

/-!
### Sets of cones

This section discusses the various subsets of a cone and their elementary
relations.
 -/

/-- The carrier of a cone contains the vertex. -/
theorem vertex_in_carrier (c : Cone 𝕜 V P) : c.vertex ∈ c.carrier := by
  rw [←c.carrier_toJoin_same]
  exact mem_of_subset_of_mem c.toJoin.side0_subset_carrier c.vertex_toJoin_in_side0

/-- The base is in the carrier of a cone. -/
theorem base_subset_of_carrier (c : Cone 𝕜 V P) : c.base ⊆ c.carrier := by
  rw [←c.carrier_toJoin_same, ←c.base_toJoin_side1]
  exact c.toJoin.side1_subset_carrier

/-- The vertex and all base points are different. -/
theorem vertex_neq_base_point (c : Cone 𝕜 V P) (hb : b ∈ c.base) : c.vertex ≠ b := by
  by_contra hc; rw [←hc] at hb; exact c.vertex_not_in_base hb

/-- The vertex and all base points are different. -/
theorem base_point_neq_vertex (c : Cone 𝕜 V P) (hb : b ∈ c.base) : b ≠ c.vertex :=
  (c.vertex_neq_base_point hb).symm

/-- The vertex is not in the segment point set. -/
theorem vertex_not_in_segment_points (c : Cone 𝕜 V P) :
    c.vertex ∉ c.segment_points := by
  admit

/-- The base and the segment point set are disjoint. -/
theorem segment_points_disjoint_base (c : Cone 𝕜 V P) :
    Disjoint c.segment_points c.base  := by
  admit

/-- The open segment between the vertex and a base-point. -/
def segmentOO (c : Cone 𝕜 V P) (_ : b ∈ c.base) : Set P := Affine.segmentOO 𝕜 c.vertex b

/-- The half-open segment between the vertex and a base-point. -/
def segmentOC (c : Cone 𝕜 V P) (_ : b ∈ c.base) : Set P := Affine.segmentOC 𝕜 c.vertex b

/-- The closed segment between the vertex and a base-point. -/
def segmentCC (c : Cone 𝕜 V P) (_ : b ∈ c.base) : Set P := Affine.segmentCC 𝕜 c.vertex b

/-- The half-infinite segment starting at the vertex and extending through a second point. -/
def segmentOI (c : Cone 𝕜 V P) (_ : p ≠ c.vertex) : Set P := Affine.segmentOI 𝕜 c.vertex p

/-- `segmentOC` is `segmentOO` with base-point added. -/
theorem segmentOC_eq_segmentOO_union_base_point (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.segmentOC hb = c.segmentOO hb ∪ { b } := by
  apply Affine.segmentOC_is_segmentOO_union_endpoint 𝕜 c.vertex b

/-- The base-point is in `segmentOC`. -/
theorem base_point_in_segmentOC (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    b ∈ c.segmentOC hb := by
  rw [segmentOC_eq_segmentOO_union_base_point]; simp

/-- The set `segmentOO` is not empty. -/
def segmentOO_nonempty (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.segmentOO hb ≠ ∅ := by
  let half := (1:𝕜) / 2
  have h1 : half < 1 := one_half_lt_one
  have h0 : 0 < half := one_half_pos
  exact Set.nonempty_iff_ne_empty.mp <| Set.nonempty_of_mem <| Set.mem_image_of_mem (AffineMap.lineMap c.vertex b) $ Set.mem_Ioo.mpr ⟨h0, h1⟩

/-- If lines to different base-points intersect the base-points are the same. -/
theorem segmentOO_do_not_intersect (c : Cone 𝕜 V P)
    (hb : b ∈ c.base) (hb' : b' ∈ c.base)
    (hi : c.segmentOO hb ∩ c.segmentOO hb' ≠ ∅ ) : b = b' := by
  exact c.lines_intersect_eq_base_points hb hb' hi

/-- If lines to different base-points intersect the base-points are the same. -/
theorem segmentOC_do_not_intersect (c : Cone 𝕜 V P)
    (hb₁ : b₁ ∈ c.base) (hb₂ : b₂ ∈ c.base)
    (hi : c.segmentOC hb₁ ∩ c.segmentOC hb₂ ≠ ∅ ) : b₁ = b₂ := by
  repeat rw [c.segmentOC_eq_segmentOO_union_base_point] at hi
  rcases Set.nonempty_iff_ne_empty.mpr hi with ⟨p, ⟨hp1, hp2⟩⟩
  match hp1, hp2 with
  | Or.inl a , Or.inl b =>
    exact c.segmentOO_do_not_intersect hb₁ hb₂ <| Set.nonempty_iff_ne_empty.mp <| Set.nonempty_of_mem $ Set.mem_inter a b
  | Or.inl a , Or.inr b =>
    suffices hs : c.segmentOO hb₂ ∩ c.segmentOO hb₁ ≠ ∅ by
      exact (c.segmentOO_do_not_intersect hb₂ hb₁ hs).symm
    rw [Set.mem_singleton_iff] at b; rw [b] at a
    have haux := Set.inter_eq_left.mpr $ Affine.segmentOO_subset_segmentOO 𝕜 c.vertex b₂ b₁ a
    rw [segmentOO, segmentOO, haux]
    exact c.segmentOO_nonempty hb₂
  | Or.inr a , Or.inl b =>
    suffices hs : c.segmentOO hb₁ ∩ c.segmentOO hb₂ ≠ ∅ by
      exact c.segmentOO_do_not_intersect hb₁ hb₂ hs
    rw [Set.mem_singleton_iff] at a; rw [a] at b
    have haux := Set.inter_eq_left.mpr $ Affine.segmentOO_subset_segmentOO 𝕜 c.vertex b₁ b₂ b
    rw [segmentOO, segmentOO, haux]
    exact c.segmentOO_nonempty hb₁
  | Or.inr a , Or.inr b =>
    exact Eq.trans (Set.mem_singleton_iff.mp a).symm (Set.mem_singleton_iff.mp b)

/-- The points given by all `segmentOC` between the vertex and base points. -/
def segment_pointsOC (c : Cone 𝕜 V P) : Set P :=
  ⋃ b : c.base, c.segmentOC b.property

/-- The points given by all `segmentOC` between the vertex and base points. -/
theorem segment_pointsOC_segment_point_union_base (c : Cone 𝕜 V P) :
  c.segment_pointsOC = c.segment_points ∪ c.base := by
ext p
simp only [segment_pointsOC, segment_points_def, Set.mem_iUnion, Set.mem_iUnion, Set.mem_union]
constructor
· rintro ⟨b, hpb⟩
  simp only [segmentOC, Affine.segmentOC_is_segmentOO_union_endpoint 𝕜 c.vertex b, Set.mem_union, Set.mem_singleton_iff] at hpb
  match hpb with
  | Or.inl h => exact Or.inl ⟨b, h⟩
  | Or.inr h => rw [h]; exact Or.inr b.property
· simp only [segmentOO, segmentOC]
  intro h'
  match h' with
  | Or.inl h =>
    rcases h with ⟨b, hb⟩
    use b
    exact Set.mem_of_subset_of_mem (Affine.segmentOO_subset_segmentOC 𝕜 c.vertex b) hb
  | Or.inr h =>
    use ⟨p, h⟩
    simp only [Affine.segmentOC, Set.mem_image]
    use 1
    simp

/-- The `segmentOO` is subset of the `segment_points`. -/
theorem segmentOO_subset_segment_points (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.segmentOO hb ⊆ c.segment_points := by
  simp only [segment_points_def]
  rw [Set.subset_def]
  simp only [Set.mem_iUnion]
  intro x hx
  use ⟨b, hb⟩
  exact hx

end «Affine cone sets»

end Affine.Cone

end «Cone basics»

-- ********************************************************************
section «Cone carrier»

/-!
## The carrier of an affine cone

In this section we prove properties of the carrier of an affine cone.

TODO Move much of the stuff to the join-file and reference it.
 -/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Cone

/-- This states the condition for a point to be in an `Cone`'s carrier. -/
theorem carrier_mem (c : Cone 𝕜 V P) :
    p ∈ c.carrier ↔ (p = c.vertex) ∨ (p ∈ c.base) ∨ (∃ b : c.base, p ∈ c.segmentOO b.property) := by
  simp only [carrier_def, segment_points_def, Set.union_def, Set.mem_setOf, Set.mem_iUnion, Set.mem_singleton_iff, segmentOO, or_assoc]

/-- This restates the definition of the carrier at `Cone.carrier` using
half-closed intervals insted of open intervals. -/
theorem carrier_def_OC (c : Cone 𝕜 V P) :
    c.carrier = { c.vertex } ∪ c.segment_pointsOC := by
  simp only [carrier_def, Join.carrier_def]
  suffices c.base ∪ c.segment_points = c.segment_pointsOC by
    rw [←this]; simp only [Set.union_assoc]
  rw [segment_pointsOC_segment_point_union_base]
  simp only [Set.union_comm]

/-- The `segmentCC` is subset of the carrier. -/
theorem segmentCC_subset_of_carrier (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.segmentCC hb ⊆ c.carrier := by
  simp only [carrier_def, segmentCC]
  rw [Affine.segmentCC_eq_segmentOO_union_endpoints]
  intro p hu; simp only [Set.union_assoc] at hu; simp only [Set.union_assoc]; match hu with
  | Or.inl h => exact Or.inl h
  | Or.inr (Or.inr h) =>
    rw [←Set.singleton_subset_iff] at hb
    exact Or.inr (Or.inl $ Set.mem_of_subset_of_mem hb h)
  | Or.inr (Or.inl h) =>
    exact Or.inr (Or.inr $ (c.segmentOO_subset_segment_points hb $ h))

/-- If `base` is empty then the affine cone reduces to `vertex`. -/
theorem base_empty_imp_vertex (c : Cone 𝕜 V P) (hbe : c.base = ∅) : c.carrier = { c.vertex } := by
  rw [←carrier_toJoin_same]
  rw [c.toJoin.side1_empty_imp_side0 hbe]
  exact c.vertex_toJoin_side0

/-- Two affine cones based at the same vertex are equal iff their cariers are
equal. -/
theorem carrier_eq_iff_eq (c c': Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
      c.carrier = c'.carrier ↔ c = c' := by
  rw [eq_iff_toJoin_eq, ←carrier_toJoin_same, ←carrier_toJoin_same]
  rw [←singleton_eq_singleton_iff, ←vertex_toJoin_side0, ←vertex_toJoin_side0] at hv
  exact c.toJoin.carrier_eq_iff_eq c'.toJoin hv

end Affine.Cone

end «Cone carrier»

-- ********************************************************************
section «Cone carrier interior»

/-!
## The carrier interior of an affine cone

This section provides theorems on the `Cone.carrier_interior`.
 -/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Cone

/-- This states the condition for a point to be in an `Cone`'s carrier. -/
theorem carrier_interior_mem (c : Cone 𝕜 V P) :
    p ∈ c.carrier_interior ↔ ( p = c.vertex ) ∨ ( ∃ b : c.base, p ∈ c.segmentOO b.property ) := by
  simp only [carrier_interior_def, segment_points_def, Set.union_def, Set.mem_setOf, Set.mem_iUnion, or_assoc, segmentOO]
  rw [Set.mem_singleton_iff]

/-- The carrier's interior of a cone contains the vertex. -/
theorem vertex_in_carrier_interior (c : Cone 𝕜 V P) : c.vertex ∈ c.carrier_interior := by
  rw [carrier_interior_def]; simp

/-- The carrier of an affine cone is the unon of the carrier's interior and the base. -/
theorem carrier_eq_carrier_interior_union_base (c : Cone 𝕜 V P) :
    c.carrier = c.carrier_interior ∪ c.base := by
  simp only [carrier_def, Set.union_assoc]
  nth_rewrite 2 [Set.union_comm]
  rw [←Set.union_assoc]
  simp only [carrier_interior_def]

/-- The carrier's interior of an affine cone is a subset of its carrier. -/
theorem carrier_interior_subset_carrier (c : Cone 𝕜 V P) :
    c.carrier_interior ⊆ c.carrier:= by
  rw [carrier_eq_carrier_interior_union_base]
  apply Set.subset_union_left

/-- The base and the segment point set are disjoint. -/
theorem carrier_interior_disjoint_base (c : Cone 𝕜 V P) :
    Disjoint c.carrier_interior c.base := by
  rw [Set.disjoint_iff_inter_eq_empty, carrier_interior_def, Set.union_inter_distrib_right {c.vertex} c.segment_points c.base]
  rw [Set.disjoint_iff_inter_eq_empty.mp c.segment_points_disjoint_base]
  rw [Set.singleton_inter_eq_empty.mpr  c.vertex_not_in_base]
  simp only [Set.empty_union]

/-- The `segmentOO` is subset of the carrier's interior. -/
theorem segmentOO_subset_of_carrier_interior (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.segmentOO hb ⊆ c.carrier_interior := by
  simp only [carrier_interior_def, segmentOO]
  exact Set.subset_union_of_subset_right (c.segmentOO_subset_segment_points hb) { c.vertex }

end Affine.Cone

end «Cone carrier interior»

-- ********************************************************************
section «Cone vector-map and lineMap»

/-!
## Lines in cones

In this section we look at the lines defined by the vertex and base-points.
These lines are essential in analysing affine cones in a topological
setting.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Cone

/-- The complement of the vertex. -/
def vertexC (c : Cone 𝕜 V P) : Set P := { c.vertex }ᶜ

/-- The base of an affine cone is a subset of the complement of the vertex. -/
theorem base_subset_of_vertexC (c : Cone 𝕜 V P) :
    c.base ⊆ c.vertexC := by
  rw [Set.subset_def]; intro x hxb
  exact Set.mem_compl_singleton_iff.mpr $ (c.vertex_neq_base_point hxb).symm

/-- The vector pointing from the vertex to the given point, i.e. `p -ᵥ c.vertex`.-/
def vector_to (c : Cone 𝕜 V P) (p : P) : V := p -ᵥ c.vertex

/-- The defintion of the method `vector_to`. -/
theorem vector_to_def (c : Cone 𝕜 V P) (p : P) : c.vector_to p = p -ᵥ c.vertex := rfl

/-- The vector pointing from the vertex to a point in the vertex-complement is not zero. -/
def vector_to_vertexC_neq_0 (c : Cone 𝕜 V P) (hp : p ∈ c.vertexC) : c.vector_to p ≠ 0 := by
  rw [vector_to_def, ne_eq, vsub_eq_zero_iff_eq]
  exact mem_compl_singleton_iff.mpr hp

/-- The vector pointing from the vertex to the given point, i.e. `p -ᵥ c.vertex`.-/
def vector_to' (c : Cone 𝕜 V P) (p : c.vertexC) : RayVector 𝕜 V := ⟨c.vector_to p, c.vector_to_vertexC_neq_0 p.property⟩

/-- The defintion of the method `vector_to'`. -/
theorem vector_to_def' (c : Cone 𝕜 V P) (p : c.vertexC) : c.vector_to' p = ⟨c.vector_to p, c.vector_to_vertexC_neq_0 p.property⟩ := rfl

/-- The defintion of `vector_to` is independent of the affine cone used to define it. -/
theorem vector_to_independent_of_cone (c c': Cone 𝕜 V P) (hv : c.vertex = c'.vertex) (p : P) :
    c.vector_to p = c'.vector_to p := by
  unfold vector_to; rw [hv]

/-- Two points are equal iff their vectors are equal. -/
theorem vector_to_eq_iff_points_eq (c : Cone 𝕜 V P) :
    c.vector_to p = c.vector_to p' ↔ p = p' := by
  unfold vector_to; constructor
  · intro h; exact vsub_left_cancel h
  · intro h; rw [h]

/-- `vector_to` zero iff point is equal to vertex.-/
def vector_to_0_iff_vertex (c : Cone 𝕜 V P) (p : P) :
    c.vector_to p = (0:V) ↔ p = c.vertex := by
  exact vsub_eq_zero_iff_eq

/-- `vector_to` on base points is non-zero.-/
def vector_to_base_point_neq_0 (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.vector_to b ≠ (0:V) := by
  simp only [vector_to]; intro hc
  apply c.vertex_neq_base_point hb
  exact(vsub_eq_zero_iff_eq.mp hc).symm

/-- The line defined by a base-point and the vertex. -/
def lineMap (c : Cone 𝕜 V P) (p : P) : 𝕜 →ᵃ[𝕜] P := AffineMap.lineMap c.vertex p

/-- The defintion of `lineMap` is independent of the affine cone used to define it. -/
theorem lineMap_independent_of_cone (c : Cone 𝕜 V P) (c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) (p : P) :
    c.lineMap p = c'.lineMap p := by
  unfold lineMap; rw [hv]

/-- The vector pointing to a point on the line given by `lineMap` is
is the vector to the line's base-point scaled suitably. -/
theorem vector_to_lineMap_k (c : Cone 𝕜 V P) (p : P) (k : 𝕜) :
    c.vector_to (c.lineMap p k) = k • (c.vector_to p) := by
  dsimp [lineMap, AffineMap.lineMap, vector_to]; simp

/-- The segment line map is injective. -/
theorem lineMap_injective (c : Cone 𝕜 V P) (hp : p ≠ c.vertex) : Function.Injective (c.lineMap p) := by
  intro k1 k2 hk1k2
  simp [lineMap, AffineMap.lineMap ] at hk1k2
  exact smul_left_injective 𝕜 ((not_iff_not.mpr $ c.vector_to_0_iff_vertex p).mpr hp) hk1k2

/-- The segment line map maps 0 to the vertex. -/
theorem lineMap_0_to_vertex (c : Cone 𝕜 V P) (p : P) :
    c.lineMap p 0 = c.vertex := by dsimp [lineMap, AffineMap.lineMap]; simp

/-- The segment line map maps 1 to the end-point. -/
theorem lineMap_1_to_end_point (c : Cone 𝕜 V P) (p : P) :
    c.lineMap p 1 = p := by dsimp [lineMap, AffineMap.lineMap]; simp

/-- The segment line map maps `k ≠ 0` to points different from the vertex. -/
theorem lineMap_k_neq_vertex (c : Cone 𝕜 V P) (hp : p ≠ c.vertex) (hk : (0:𝕜) < k) :
    c.lineMap p k ≠ c.vertex := by
  have hh0 := (c.lineMap_injective hp).ne (ne_of_gt hk)
  rw [c.lineMap_0_to_vertex p] at hh0
  exact hh0

/-- The segment line map maps `k ≠ 1` to points different from the end-point. -/
theorem lineMap_k_neq_base_point (c : Cone 𝕜 V P) (hp : p ≠ c.vertex) (hk : k ≠ (1:𝕜)) :
    c.lineMap p k ≠ p := by
  have hh1 := (c.lineMap_injective hp).ne hk
  rw [c.lineMap_1_to_end_point p] at hh1
  exact hh1

/-- The `lineMap` maps `[0, 1]` to `segmentCC`. -/
theorem lineMap_Icc_to_segmentCC (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.lineMap b '' Set.Icc (0:𝕜) 1 = c.segmentCC hb := rfl

/-- The `lineMap` maps `(0, 1]` to `segmentOC`. -/
theorem lineMap_Ioc_to_segmentOC (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.lineMap b '' Set.Ioc (0:𝕜) 1 = c.segmentOC hb := rfl

/-- The `lineMap` maps `(0, 1)` to `segmentOO`. -/
theorem lineMap_Ioo_to_segmentOO (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.lineMap b '' Set.Ioo (0:𝕜) 1 = c.segmentOO hb := rfl

/-- A point in the carrier is on a `lineMap`. -/
theorem point_in_carrier_on_lineMap (c : Cone 𝕜 V P) (hpc : p ∈ c.carrier) (hpv : p ≠ c.vertex) :
    ∃ b : c.base, ∃ k : 𝕜, 0 < k ∧ k ≤ 1 ∧ p = c.lineMap b k := by
  match c.carrier_mem.mp hpc with
  | Or.inl h => contradiction
  | Or.inr (Or.inl h) =>
    use ⟨p, h⟩, 1; simp only [c.lineMap_1_to_end_point]; simp
  | Or.inr (Or.inr h) =>
    simp only [segmentOO, Affine.segmentOO, Set.mem_image] at h
    rcases h with ⟨b, ⟨k, ⟨hk, hlbkp⟩⟩⟩
    use b, k
    apply And.intro $ (Set.mem_Ioo.mp hk).left
    apply And.intro $ le_of_lt (Set.mem_Ioo.mp hk).right
    exact hlbkp.symm

/-- `lineMap` maps into the carrier of the cone. -/
theorem lineMap_into_carrier (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.lineMap b '' Set.Icc (0:𝕜) 1 ⊆ c.carrier := by
  rw [c.lineMap_Icc_to_segmentCC hb]
  simp only [segmentCC_subset_of_carrier]

end Affine.Cone

end «Cone vector-map and lineMap»

-- ********************************************************************
section «Spanned spaces»

/-!
## The tangent space and the affine subspaces defined by cones

This section defines nitions of "tangent space" for affine cones:

- The `spanned_submodule` is the minmal submodule that is generated
  by the cone.
- The `spanned_subspace` is the minmal affine subspace that is spanned
  by the cone.

The `dim`ension of an affine cone is given by the dimension of the
`spanned_submodule`.

The local structure of an affine cone is captured by the notion
of a fan: The `fan` of an affine cone is the set of vectors that are
on lines that pass through vertex and some base-point.

A fan contains affine subspaces which are called leaves. They are
identified by the `IsLeaf` property. The `core` is the intersection
of all leaves and thus a submodule. Its dimension is less than the
cone's dimension. If the two dimensions coincide the cone `IsFlat`.
If there is only one leaf then the cone is said to be `IsFold`.

Analyzing affine cones is not of any particular interest in
PL-topology as the cone-structure is in itself of no great use.
We will use these notions to show that there is a lower bound to
the way a polyhedron can be written as a stratification by
polyhedra of increasing dimension.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Cone

/-- The set of vectors pointing from the vertex to a base-point.-/
def base_vectors (c : Cone 𝕜 V P) : Set V := c.base -ᵥ { c.vertex }

/-- This is the module subspace generated by a cone. -/
def spanned_submodule (c : Cone 𝕜 V P) : Submodule 𝕜 V := Submodule.span 𝕜 c.base_vectors

/-- An affine cone is finite-dimensional if its `spanned_submodule` is. -/
class IsFinite (c : Cone 𝕜 V P) extends Module.Finite 𝕜 c.spanned_submodule

/-- The dimension of a cone is the dimension of the `spanned_submodule`.
Note that the value is `0` if the `spanned_submodule` is not finite dimensional. -/
noncomputable def dim (c : Cone 𝕜 V P) : Cardinal := Module.rank 𝕜 c.spanned_submodule

/-- This is the affine subspace generated by a cone. -/
def spanned_subspace (c : Cone 𝕜 V P) : AffineSubspace 𝕜 P := AffineSubspace.mk' c.vertex c.spanned_submodule

/-- Given two cones, their `spanned_submodule`s are subsets of each other if the same
is true of their `spanned_subspace`s. -/
theorem spanned_submodule_sub_iff_spanned_subspace_sub (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    c.spanned_submodule ≤ c'.spanned_submodule ↔ c.spanned_subspace ≤ c'.spanned_subspace := by
  admit

/-- Given two cones, their `spanned_submodule`s are equal iff the same
is true of their `spanned_subspace`s. -/
theorem spanned_submodule_eq_iff_spanned_subspace_eq (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    c.spanned_submodule = c'.spanned_submodule ↔ c.spanned_subspace = c'.spanned_subspace := by
  constructor
  · intro h
    exact eq_of_le_of_le ((c.spanned_submodule_sub_iff_spanned_subspace_sub c' hv).mp $ le_of_eq h)
                         ((c'.spanned_submodule_sub_iff_spanned_subspace_sub c hv.symm).mp $ le_of_eq h.symm)
  · intro h
    exact eq_of_le_of_le ((c.spanned_submodule_sub_iff_spanned_subspace_sub c' hv).mpr $ le_of_eq h)
                         ((c'.spanned_submodule_sub_iff_spanned_subspace_sub c hv.symm).mpr $ le_of_eq h.symm)

/-- This shows that for a given base-point the vector from the vertex to the
base-point is in the spanned module subspace. -/
theorem vector_to_base_in_spanned_submodule (c : Cone 𝕜 V P) (b : c.base) :
    c.vector_to b ∈ c.spanned_submodule := by
  simp only [spanned_submodule]
  have h : ↑b -ᵥ c.vertex ∈ c.base -ᵥ { c.vertex } := by
    simp only [Set.mem_vsub, Set.mem_def.mp]
    use ↑b
    apply And.intro b.property
    use c.vertex
    exact ⟨Set.mem_singleton c.vertex, rfl⟩
  exact Submodule.subset_span h

/-- Given two cones, if for every base-point the line passing through the base point meets
the carrier of the second, then the `spanned_submodule` of the first cone is contained
in the `spanned_submodule` of the second cone. -/
theorem spanned_submodule_le_spanned_submodule (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    (∀ b : c.base, ∃ k : 𝕜, 0 < k ∧ (c.lineMap b k) ∈ c'.carrier) → c.spanned_submodule ≤ c'.spanned_submodule := by
  admit

/-- Given two cones, if for every base-point the line passing through the base point meets
the carrier of the second, then the `spanned_submodule` of the first cone is contained
in the `spanned_submodule` of the second cone. -/
theorem spanned_submodule_le_spanned_submodule' (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    ∀ b : c.base, (c.segmentOI $ c.base_point_neq_vertex b.property) ∩ c'.carrier ≠ ∅ → c.spanned_submodule ≤ c'.spanned_submodule := by
  admit

/-- The carrier is in the spanned affine subspace. -/
theorem carrier_subset_of_spanned_subspace (c : Cone 𝕜 V P) : c.carrier ⊆ c.spanned_subspace := by
  admit

/-- The spanned module subspace is the least subspace in the module that
contains all base-vectors. -/
theorem spanned_submodule_least_submodule (c : Cone 𝕜 V P) (sm : Submodule 𝕜 V) :
    c.spanned_submodule ≤ sm ↔ c.base_vectors ⊆ sm := by
  --Submodule.span_le
  admit

/-- The spanned affine subspace is the least subspace in the affine space
that contains the carrier of the cone. -/
theorem spanned_subspace_least_subspace (c : Cone 𝕜 V P) (as : AffineSubspace 𝕜 P) :
    c.spanned_subspace ≤ as ↔ c.carrier ⊆ as := by
  -- affineSpan_le
  admit

/-- The fan of an affine cone is the set of vectors that are on lines
that pass through vertex and some base-point. Note that in the definition
we include a union with the singleton `{ 0 }` to ensure that `0` is
contaned in the fan even if the base of the affine cone is empty. -/
def fan (c : Cone 𝕜 V P) : Set V := { 0 } ∪ { v | ∃ b : c.base, ∃ k : 𝕜, v = k • (c.vector_to b)}

/-- Given two cones, if for every base-point the line passing through the base
point meets the carrier of the second, then the `fan` of the first cone is contained
in the `fan` of the second cone. -/
theorem fan_le_fan (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    (∀ b : c.base, ∃ k : 𝕜, 0 < k ∧ (c.lineMap b k) ∈ c'.carrier) → c.fan ⊆ c'.fan := by
  admit

/-- The `fan` contains `0`. -/
theorem fan_contains_0 (c : Cone 𝕜 V P) : 0 ∈ c.fan := by
  apply Set.subset_union_left; apply Set.mem_singleton_iff.mpr; simp

/-- The `fan` is a subset of the `spanned_submodule`. -/
theorem fan_subset_of_spanned_module (c : Cone 𝕜 V P) :
    c.fan ⊆ c.spanned_submodule := by
  admit

/-- A submodule that lies in the  `Fan` is a submodule of the `spanned_submodule`. -/
def fan_subset_as_submodule_spanned_submodule (c : Cone 𝕜 V P)
    (sm : Submodule 𝕜 V) (hsm : sm.carrier ⊆ c.fan) : Submodule 𝕜 c.spanned_submodule :=
  by admit --Submodule.map c.spanned_submodule.subtype sm

/-- A leave of a `Fan` is a submodule that is contained in the `Fan` and
is maximal with this property with respect to the submodule-order. -/
structure IsLeaf (c : Cone 𝕜 V P) (sm : Submodule 𝕜 V) : Prop where
  /-- The leave is a subset of the fan. -/
  subset_of_fan : (sm : Set V) ⊆ c.fan
  /-- The leave is a maximal submodule with respect to the submodule-order. -/
  maximal_subset (sm' : Submodule 𝕜 V) (hsub : sm ≤ sm') (hsm' : sm'.carrier ⊆ c.fan) : sm = sm'

/-- The set of `IsLeaf`s of an affine cone. -/
def leaves (c : Cone 𝕜 V P) : Set (Submodule 𝕜 V) := { sm : Submodule 𝕜 V | IsLeaf c sm }

/-- A leaf of a fan is less then `spanned_submodule` in the submodule-order. -/
theorem leaf_le_spanned_submodule (c : Cone 𝕜 V P) (hlf : IsLeaf c sm) :
    sm ≤ c.spanned_submodule := subset_trans hlf.subset_of_fan c.fan_subset_of_spanned_module

/-- A leaf of a fan is a submodule of the `spanned_submodule`. -/
def leaf_as_submodule_of_spanned_submodule (c : Cone 𝕜 V P) (lf : IsLeaf c sm) :
    Submodule 𝕜 c.spanned_submodule := by
  admit

/-- The set of `leaves` is not empty provided some conditions ensures
that maximal submodules of the fan exist. We prove this only for the case
when the `spanned_submodule` is finite-dimensional. -/
theorem leaves_not_empty_if_finite (c : Cone 𝕜 V P)
    [hf : IsFinite c] : c.leaves.Nonempty := by
  let sms := { sm : Submodule 𝕜 c.spanned_submodule | sm.carrier ⊆ Submodule.subtype c.spanned_submodule ⁻¹' c.fan }
  have hne : Submodule.trivial ∈ sms := by admit
  have h2 := Module.exists_max_submodule sms $ (Set.nonempty_of_mem hne)
  rcases h2 with ⟨sm, ⟨hsm, hsmmax⟩⟩
  let smv := sm.map $ Submodule.subtype c.spanned_submodule
  have h3 : smv.carrier ⊆ c.fan := by admit
  have h4 (sm' : Submodule 𝕜 V) (hsub : smv ≤ sm') (hsm' : sm'.carrier ⊆ c.fan) : smv = sm' := by
    --have h : c.Fan.as_submodule_spanned_submodule sm' ∈ sms := Set.mem_setOf.mpr $ hsm'
    admit
  exact Set.nonempty_of_mem $ Set.mem_setOf.mpr $ IsLeaf.mk h3 h4

/-- The core is the intersection of all `leaves` of an affine cone. -/
def core (c : Cone 𝕜 V P) : Submodule 𝕜 V := sInf c.leaves

/-- The stratum-dimension is the rank of the `core` of an affine cone.
Note that the value is `0` if the `core` is not finite dimensional. -/
noncomputable def dim_core (c : Cone 𝕜 V P) : Cardinal := Module.rank 𝕜 c.core

/-- The `stratum_dim` of an affine cone is less than the dimension `dim`. -/
theorem dim_stratum_le_dim (c : Cone 𝕜 V P) : c.dim_core ≤ c.dim := by
  admit

/-- An affine cone is flat if its only `IsLeaf` is the `spanned_submodule`.
This corresponds to the intuition that a flat affine cone spans an entire
subspace, and there are wrinkles. -/
def IsFlat (c : Cone 𝕜 V P) : Prop := c.leaves = { c.spanned_submodule }

/-- If an affine cone `IsFlat` then its `core` is the `spanned_submodule`.
The theorem assumes that the set of `leaves` is not empty. -/
theorem IsFlat_iff_core_eq_spanned_submodule (c : Cone 𝕜 V P) (hlne : c.leaves.Nonempty) :
    c.IsFlat ↔ c.core = c.spanned_submodule := by
  constructor
  · intro hif; rw [core, hif]; simp
  · intro heq
    rw [core] at heq
    ext sm; simp only [Set.mem_singleton_iff]; constructor
    · intro hsm
      have := le_antisymm (heq ▸ CompleteSemilatticeInf.sInf_le c.leaves sm hsm) (c.leaf_le_spanned_submodule hsm)
      exact this.symm
    · intro hsm; rw [hsm]; rcases hlne with ⟨lf, hlf⟩
      have hsmeqss := le_antisymm (heq ▸ CompleteSemilatticeInf.sInf_le c.leaves lf hlf) (c.leaf_le_spanned_submodule hlf)
      rw [←hsmeqss] at hlf
      exact hlf

/-- An affine cone is flat iff its `dim_core` and its `dim`ension
are the same. -/
theorem IsFlat_iff_dim_core_eq_dim (c : Cone 𝕜 V P) : c.IsFlat ↔ c.dim_core = c.dim := by
  admit

/-- An affine cone is a fold if it has only one leaf which is a proper
submodule of the `spanned_submodule`. This corresponds to the intuition
that space of the cone folds exactly along the subspace defined by the
fold, but it folds in no other direction. -/
def IsFold (c : Cone 𝕜 V P) : Prop := ∃ sm : Submodule 𝕜 V, c.leaves = { sm } ∧ sm < c.spanned_submodule

end Affine.Cone

end «Spanned spaces»

-- ********************************************************************
section «Join under affine maps»

/-!
## Cones under affine maps

This section shows that affine cones map to affine cones under injective
affine transformations.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {W : Type v} [AddCommGroup W] [Module 𝕜 W]
variable {Q : Type w} [AddTorsor W Q]

namespace Affine.Cone

/-- Affine cones map to affine cones under injective affine transformations. -/
def map_affine_injective (c : Cone 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) : Cone 𝕜 W Q where
  vertex := m c.vertex
  base := m '' (c.base)
  vertex_not_in_base := by
    exact (not_iff_not.mpr (Function.Injective.mem_set_image hmi)).mpr c.vertex_not_in_base
  lines_intersect_eq_base_points := by
    rintro q1 q2 ⟨b1, ⟨hb1, hb1mq1⟩⟩ ⟨b2, ⟨hb2, hb2mq2⟩⟩ hine
    simp only [Subtype.mk_eq_mk, ←hb1mq1, ←hb2mq2] at hine
    rw [←Affine.segmentOO_maps_to_segmentOO 𝕜 m c.vertex b1] at hine
    rw [←Affine.segmentOO_maps_to_segmentOO 𝕜 m c.vertex b2] at hine
    rw [←Set.image_inter, Set.image_eq_not_empty] at hine
    rw [←hb1mq1, ←hb2mq2]
    rw [c.lines_intersect_eq_base_points hb1 hb2 hine]
    exact hmi

/-- Given an affine cone, the two functions `map_affine_injective` and `toJoin`
commute. -/
theorem map_affine_injective_toJoin_commute
    (c : Cone 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (c.map_affine_injective m hmi).toJoin = c.toJoin.map_affine_injective m hmi := by
  simp only [map_affine_injective, Join.map_affine_injective, toJoin, Set.image_singleton]
  rw [Join.eq]
  simp

/-- The carrier of the affine cone given by `Cone.map_affine_injective`
is the image of the carrier of the original affine cone under the
affine map . -/
theorem map_affine_injective_carrier
    (c : Cone 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    c.map_affine_injective m hmi = m '' c := by
  rw [←carrier_toJoin_same]; rw [←carrier_toJoin_same]
  simp only [map_affine_injective_toJoin_commute]
  rw [Join.map_affine_injective_carrier]

/-- The carrier's interior of the affine cone given by `Cone.map_affine_injective`
is the image of the carrier's interior of the original affine cone
under the affine map . -/
theorem map_affine_injective_carrier_interior
    (c : Cone 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (c.map_affine_injective m hmi).carrier_interior = m '' c.carrier_interior := by
  rw [←carrier_interior_toJoin_carrier_interior0]; rw [←carrier_interior_toJoin_carrier_interior0]
  simp only [map_affine_injective_toJoin_commute]
  rw [Join.map_affine_injective_carrier_interior0]

end Affine.Cone

end «Join under affine maps»

-- ********************************************************************
section «Cone scaling»

/-!
## Contraction of cones

Affine cones can be rescaled from the vertex by stretching the entire
affine cone by a factor (a so called homothety). This section translates
the relevant therems of `AffineMap.homothety` for cones. For practical
purposes, we only need to contract cones.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Cone

/-- The affine homothety (dilation) about the vertex given by the scaling factor less than 1. -/
def contraction (c : Cone 𝕜 V P) (_ : k ∈ Set.Ioo (0:𝕜) 1) : P →ᵃ[𝕜] P := AffineMap.homothety c.vertex k

/-- The defintion of `contraction` does not depend on the cone. -/
theorem contraction_independent_of_cone (c : Cone 𝕜 V P) {c' : Cone 𝕜 V P} (hv : c.vertex = c'.vertex) (hk : k ∈ Set.Ioo (0:𝕜) 1) :
    c.contraction hk = c'.contraction hk := by
  rw [contraction, contraction, hv]

/-- This applies a homothety (dilation) at the vertex to the given cone.
For the definition of homothety, see `AffineMap.homothety`. This function
defines the resulting cone. -/
def contract (c : Cone 𝕜 V P) (hk : k ∈ Set.Ioo (0:𝕜) 1) : Cone 𝕜 V P :=
  c.map_affine_injective (AffineMap.homothety c.vertex k) (AffineMap.homothety_injective c.vertex (ne_of_gt (Set.mem_Ioo.mp hk).left))

/-- Contraction leaves the vertex fixed. -/
def contract_fixes_vertex (c : Cone 𝕜 V P) (hk : k ∈ Set.Ioo (0:𝕜) 1) :
    (c.contract hk).vertex = c.vertex := by
  simp only [contract, map_affine_injective]; simp

/-- The image of the carrier of an affine cone under contraction is the carrier
of the contracted cone. -/
theorem contract_carrier (c : Cone 𝕜 V P) (hk : k ∈ Set.Ioo (0:𝕜) 1) :
    c.contract hk = (c.contraction hk) '' c.carrier := by
  simp only [contract, contraction]; rw [map_affine_injective_carrier]

/-- The image of the carrier of an affine cone under contraction is the carrier
of the contracted cone. -/
theorem contract_carrier_interior (c : Cone 𝕜 V P) (hk : k ∈ Set.Ioo (0:𝕜) 1) :
    (c.contract hk).carrier_interior = (c.contraction hk) '' c.carrier_interior := by
  simp [contract, contraction]; rw [map_affine_injective_carrier_interior]; done

/-- When contracting a cone, the carrier moves into the interior carrier of the cone. -/
theorem contracted_subset_carrier_interior (c : Cone 𝕜 V P) (hk : k ∈ Set.Ioo (0:𝕜) 1) :
    (c.contract hk).carrier ⊆ c.carrier_interior := by
  simp only [carrier_def_OC, contract_fixes_vertex, segment_pointsOC, carrier_interior_def]
  suffices (c.contract hk).segment_pointsOC ⊆ c.segment_points by
    exact Set.union_subset_union_right { c.vertex } this
  suffices (c.contract hk).segment_pointsOC = (c.contraction hk) '' c.segment_pointsOC by
    rw [this]
    simp only [segment_pointsOC, Set.image_iUnion, segmentOC, AffineMap.homothety_fixes_vertex, Set.subset_def]
    intro x
    simp only [Set.mem_iUnion]
    rintro ⟨b, hxb⟩
    have _ := Set.mem_of_subset_of_mem (Affine.segmentOC_contracts_into_segmentOO 𝕜 hk c.vertex b) hxb
    simp only [segment_points_def, Set.mem_iUnion]
    use b
  simp only [segment_pointsOC, contract, contraction, map_affine_injective, segmentOC,
    Set.image_iUnion, Affine.segmentOC_maps_to_segmentOC, AffineMap.homothety_fixes_vertex]
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨_, ⟨b, ⟨hb, hbb'⟩⟩⟩, hp⟩; use ⟨b, hb⟩; rw [hbb']; assumption
  · rintro ⟨b, hp⟩; use Set.apply_subtype (AffineMap.homothety c.vertex k) b; assumption

/-- When contracting a cone, the carrier moves into the carrier of the cone. -/
theorem contracted_subset_carrier (c : Cone 𝕜 V P) (hk : k ∈ Set.Ioo (0:𝕜) 1) :
    (c.contract hk).carrier ⊆ c.carrier := subset_trans (c.contracted_subset_carrier_interior hk) c.carrier_interior_subset_carrier

end Affine.Cone

end «Cone scaling»

-- ********************************************************************
section «Cone set operations»

/-!
## Set operations with affine cones

This section shows how to construct new affine cones from given affine
cones through set-operation. The operations we consider are:

- Subsets / subcones of affine cones: `Affine.Cone.subcone`
- Intersection of affine cones: `Affine.Cone.inter`

The union of cones can be defined as the union of their carriers.
However, the base of this union is usually a "jagged" set that
is not useful in PL-topology. We thus refrain from introducing
the union of affine cones.

Both sub-cones and intersections behave well with respect to the cone's
carrier: The resulting carrier of the intersection, for example, is
the intersection of the two cone's carriers.

Note that the union of two affine cones is not necessarily what is
required in the practice of PL-topology as the base of the union is
not as a rule a suitable base.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Cone

-- -------------------------------------------------------------------
/-!
### Sub-cones
-/

/-- Taking a subset of the base yields a cone. -/
def subcone (c : Cone 𝕜 V P) (hbs : bs ⊆ c.base) : Cone 𝕜 V P where
  vertex := c.vertex
  base := bs
  vertex_not_in_base := by
    by_contra h
    exact c.vertex_not_in_base $ Set.mem_of_subset_of_mem hbs h
  lines_intersect_eq_base_points := by
    intro b1 b2 hb1 hb2 hi
    exact c.lines_intersect_eq_base_points (Set.mem_of_subset_of_mem hbs hb1) (Set.mem_of_subset_of_mem hbs hb2) hi

/-- An affine cone obtained from a given affine cone through `sub_cone`
is a subset of this affine cone. -/
theorem subcone_subset_cone (c : Cone 𝕜 V P) (hbs : bs ⊆ c.base) :
    (c.subcone hbs : Set P) ⊆ c := by
  simp only [carrier_def, Set.union_assoc]
  suffices haux : (c.subcone hbs).segment_points ⊆ c.segment_points by
    apply Set.union_subset_union_right
    apply Set.union_subset_union hbs
    exact haux
  simp only [Set.subset_def, subcone, segment_points_def]
  intro x
  simp only [Set.mem_iUnion]
  rintro ⟨⟨b, hb⟩, hxs⟩
  use ⟨b, Set.mem_of_subset_of_mem hbs hb⟩

-- -------------------------------------------------------------------
/-!
### Intersection of cones
-/

/-- This defines the base of the intersection of two affine cones. Note that
the sets are chosen mutually disjoint. -/
private def inter_base (c₁ c₂ : Cone 𝕜 V P) (_ : c₁.vertex = c₂.vertex) : Set P :=
  { b ∈ c₁.base | ∃ b₂ : c₂.base, b ∈ c₂.segmentOO b₂.property} ∪ { b ∈ c₂.base | ∃ b₁ : c₁.base, b ∈ c₁.segmentOO b₁.property} ∪ (c₁.base ∩ c₂.base)

/-- The set `inter_base` is subset of the union of the affine cone's bases. -/
private theorem inter_base_subset_bases (c₁ c₂ : Cone 𝕜 V P) (hv : c₁.vertex = c₂.vertex) :
    inter_base c₁ c₂ hv ⊆ c₁.base ∪ c₂.base := by
  simp only [inter_base, Set.subset_def]
  intro x hx
  match hx with
  | Or.inl (Or.inl h) => exact Or.inl h.left
  | Or.inl (Or.inr h) => exact Or.inr h.left
  | Or.inr h => exact Or.inl h.left

/-- The set `inter_base` is subset of the union of the affine cone's bases. -/
private theorem vertex_not_in_inter_base (c₁ c₂ : Cone 𝕜 V P) (hv : c₁.vertex = c₂.vertex) :
    c₁.vertex ∉ inter_base c₁ c₂ hv ∧ c₂.vertex ∉ inter_base c₁ c₂ hv := by
  suffices h : c₁.vertex ∉ inter_base c₁ c₂ hv by exact ⟨h, hv.symm ▸ h⟩
  suffices h : c₁.vertex ∉ c₁.base ∪ c₂.base by
    by_contra hc
    have _ := Set.mem_of_subset_of_mem (inter_base_subset_bases c₁ c₂ hv) hc
    contradiction
  by_contra hc
  match hc with
  | Or.inl h => exact c₁.vertex_not_in_base h
  | Or.inr h => exact (hv.symm ▸ c₂.vertex_not_in_base) h

/-- The intersection of two affine cones based at the same vertex is an
affine cone. -/
def inter (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) : Cone 𝕜 V P where
  vertex := c.vertex
  base := inter_base c c' hv
  vertex_not_in_base := (c.vertex_not_in_inter_base c' hv).left
  lines_intersect_eq_base_points := by
    intro b1 b2 hb1 hb2 hi
    admit

/-- The vertex of the intersection of two affine cones is the vertex of the
first cone. -/
@[simp] theorem inter_vertex0 (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    (c.inter c' hv).vertex = c.vertex := rfl

/-- The vertex of the intersection of two affine cones is the vertex of the
second cone. -/
@[simp] theorem inter_vertex1 (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    (c.inter c' hv).vertex = c'.vertex := hv ▸ inter_vertex0 c c' hv

/-- The base of the intersection of two affine cones. -/
theorem inter_base_def (c₁ c₂ : Cone 𝕜 V P) (hv : c₁.vertex = c₂.vertex) :
    (c₁.inter c₂ hv).base = { b ∈ c₁.base | ∃ b₂ : c₂.base, b ∈ c₂.segmentOO b₂.property}
                          ∪ { b ∈ c₂.base | ∃ b₁ : c₁.base, b ∈ c₁.segmentOO b₁.property}
                          ∪ (c₁.base ∩ c₂.base) := by rfl

/-- An alternative view of the base of the intersection of two affine cones. -/
theorem inter_base_def' (c₁ c₂ : Cone 𝕜 V P) (hv : c₁.vertex = c₂.vertex) :
    (c₁.inter c₂ hv).base = { b ∈ c₁.base | ∃ b₂ : c₂.base, b ∈ c₂.segmentOC b₂.property}
                          ∪ { b ∈ c₂.base | ∃ b₁ : c₁.base, b ∈ c₁.segmentOC b₁.property} := by
  admit

/-- The carrier of the intersection of two affine cones is the intersection
of the two cones' carriers. -/
@[simp] theorem inter_carrier (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    (c.inter c' hv).carrier = c.carrier ∩ c'.carrier := by

  admit

/-- The intersection of two cones is contained in the first cone. -/
theorem inter_subset_cone (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    (c.inter c' hv : Set P) ⊆ c := by
  rw [c.inter_carrier c' hv]
  apply Set.inter_subset_left

/-- The intersection of affine cones is a symmetric operation. -/
@[simp] theorem inter_symm (c c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) :
    (c.inter c' hv) = (c'.inter c hv.symm) := by

  admit

/-- The intersection of affine cones is an associative operation. -/
@[simp] theorem inter_assoc (c c' c'' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) (hv' : c'.vertex = c''.vertex) :
    (c.inter (c'.inter c'' hv') hv) = (c.inter c' hv).inter c'' (Eq.trans hv hv') := by

  admit

end Affine.Cone

end «Cone set operations»

-- -------------------------------------------------------------------
section «Convex sets»

/-!
### Relation to convex sets

Sets that satisfiy `IsStarConvex` are affine connes provided they
are bounded.
TODO Introduce the notion of bounded star convex sets.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine

/-- A `IsStarConvex` set is an affine cone... -/
theorem starConvex_is_cone (hs : IsStarConvex 𝕜 P p s) :
    IsCone 𝕜 V P p hs.base := by
  admit

end Affine

namespace Affine.Cone

/-- The intersection of an affine cone with a `IsStarConvex` set centred
at the vertex of the cone is again an affine cone. The base is the
intersection of the cone's base with the star-convex set. -/
theorem inter_starConvex (c : Cone 𝕜 V P) (hs : IsStarConvex 𝕜 P c.vertex s) :
    IsCone 𝕜 V P c.vertex (s ∩ c.carrier) := by
  admit

end Affine.Cone

end «Convex sets»

-- ********************************************************************
--#lint
