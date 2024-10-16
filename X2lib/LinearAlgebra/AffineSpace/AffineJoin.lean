/-
Copyright (c) 2024 Stephan Maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Subset
--import Mathlib.Order.SetNotation
import Mathlib.Algebra.AddTorsor
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Topology.Algebra.Affine
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

import X2lib.Topology.PiecewiseLinear.Aux.Set
import X2lib.Topology.PiecewiseLinear.Aux.Affine
import X2lib.Topology.PiecewiseLinear.Aux.Module

/-!
# Affine joins

In this file we introduce `Join` as subset of a given affine ambient space.
The joinis a fundamental set-constructions for piecewise-linear topology.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Rourke] for ann introduction to PL-topology.
-/

universe u v w

-- ********************************************************************
section «Definition»

namespace Affine

/-!
## Affine Join

The main construction of elementary PL-objects (in affine space) is given
by `Join`. Given two sets (the sides of the join), and affine join
results from taking all points on all lines connecting points in the two sets.
To make the construction useful it is required that two lines between
the sides intersect if and only if they are the same lines.
 -/

variable (𝕜 : Type u) [LinearOrderedField 𝕜]
variable (V : Type v) [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- An affine  join between two sets in an affine space is the set of line segments
between pairs of points from the two sets.

Note that the definition differs from that of `convexJoin` in requiring that
the line segments that make up the join do not intersect unless they are
identical.

We need to include the definition of `segment_points` and `Join.carrier`
because we potentially wish to extend this structure through properties
that need to access the definition of the segment points and the carrier.

Note that affine joins determine sets in the ambient affine space. Affine joins
cannot, however, implement the `SetLike` interface as the same set can be
written as a join in many ways. Compare, however, `carrier_eq_iff_eq`
which shows that joins are uniquely determined by their sets once part
of the join is given.
-/
structure Join where
  /-- The left set of the join.-/
  side0 : Set P
  /-- The right set of the join.-/
  side1 : Set P
  /-- The sides must be disjoint. -/
  sides_disjoint : side0 ∩ side1 = ∅
  /-- If lines connecting points in the two side intersect they are identical lines. -/
  lines_do_not_intersect (ha : a ∈ side0) (hb : b ∈ side1)
                         (ha' : a' ∈ side0) (hb' : b' ∈ side1)
                         (hi : Affine.segmentOO 𝕜 a b ∩ Affine.segmentOO 𝕜 a' b' ≠ ∅ ) : a = a' ∧ b = b'
  /-- The points in the ambient space that lie on the segments connecting the sides
  (endpoints excluded). -/
  segment_points : Set P := ⋃ p : side0 × side1, Affine.segmentOO 𝕜 ↑p.fst ↑p.snd
  /-- The defintion of `segment_points`. -/
  segment_points_def : segment_points = ⋃ p : side0 × side1, Affine.segmentOO 𝕜 ↑p.fst ↑p.snd := by simp
  /-- The carrier is the set of points defined by an affine join. -/
  carrier : Set P := side0 ∪ side1 ∪ segment_points
  /-- The defintion of the carrier. -/
  carrier_def : carrier = side0 ∪ side1 ∪ segment_points := by simp

/-- This defines the conditions which two sets must satisfy in order to form an
affine join. -/
structure IsJoin
    (𝕜 : Type u) [LinearOrderedField 𝕜]
    (V : Type v) [AddCommGroup V] [Module 𝕜 V]
    (P : Type w) [AddTorsor V P]
    (side0 side1 : Set P) : Prop where
  /-- The sides must be disjoint. -/
  sides_disjoint : side0 ∩ side1 = ∅
  /-- If lines connecting points in the two side intersect they are identical lines. -/
  lines_do_not_intersect (ha : a ∈ side0) (hb : b ∈ side1)
                         (ha' : a' ∈ side0) (hb' : b' ∈ side1)
                         (hi : Affine.segmentOO 𝕜 a b ∩ Affine.segmentOO 𝕜 a' b' ≠ ∅ ) : a = a' ∧ b = b'

end Affine

end «Definition»

-- ********************************************************************
section «Affine Join structure»

/-!
## The structure of joins

This section describes the structure of affine joins. Most importantly,
this sections defines the subset of affine space, the `Join.carrier`,
given by an affine join.
 -/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

open Affine

-- -------------------------------------------------------------------
section «Basics»

/-- This allows us to transform the condition `IsJoin` to a `Join`. -/
def IsJoin.to_Join (h : IsJoin 𝕜 V P s0 s1) : Join 𝕜 V P where
  side0 := s0
  side1 := s1
  sides_disjoint := h.sides_disjoint
  lines_do_not_intersect := h.lines_do_not_intersect

end «Basics»

namespace Affine.Join

-- -------------------------------------------------------------------
section «Affine Join equality»
/-!
### Equality of joins

Two joins are equal iff their sides are equal.
 -/

/-- If the sides of joins are equal so are their segment points. -/
theorem eq_sides_eq_segment_points (j j': Join 𝕜 V P) (heq : j.side0 = j'.side0 ∧ j.side1 = j'.side1) :
    j.segment_points = j'.segment_points := by
  ext x
  simp only [segment_points_def, Set.mem_iUnion]
  constructor <;>
  · rintro ⟨⟨⟨p0, hp0⟩, ⟨p1, hp1⟩⟩, hh⟩; simp at hh
    use ⟨⟨p0, heq.left ▸ hp0⟩, ⟨p1, heq.right ▸ hp1⟩⟩

/-- If the sides of joins are equal so are their carriers. -/
theorem eq_sides_eq_carrier (j j': Join 𝕜 V P) (heq : j.side0 = j'.side0 ∧ j.side1 = j'.side1) :
    j.carrier = j'.carrier := by
  ext x
  simp only [carrier_def, heq.left, heq.right, eq_sides_eq_segment_points j j' heq]

/-- Two joins are equal iff their sides are equal. -/
theorem eq (j j': Join 𝕜 V P) : j = j' ↔ j.side0 = j'.side0 ∧ j.side1 = j'.side1 := by
  constructor
  · intro h; rw [h]; simp
  · rintro h
    calc
      j = ⟨ j.side0, j.side1, j.sides_disjoint, j.lines_do_not_intersect, j.segment_points, j.segment_points_def, j.carrier, j.carrier_def ⟩ := rfl
      _ = ⟨ j'.side0, j'.side1, j'.sides_disjoint, j'.lines_do_not_intersect, j'.segment_points, j'.segment_points_def, j'.carrier, j'.carrier_def ⟩ := by
        simp only [h.left, h.right, eq_sides_eq_segment_points j j' h, eq_sides_eq_carrier j j' h]
      _ = j' := rfl

end «Affine Join equality»

/- ---------- Sets ------------------------------------------------- -/
section «Affine Join sets»
/-!
### Sets of joins

This section discusses the various subsets of a join and their elementary
relations.
 -/

/-- This allows us to view the condition `IsJoin` as a `Join`. -/
instance inst_CoeSort_IsJoin_to_Join : CoeSort (IsJoin 𝕜 V P s0 s1) (Join 𝕜 V P) where
  coe := IsJoin.to_Join

/-- This allows us to view a `Join` as a `Set P`. The set is the carrer of the join. -/
instance CoeSort_Join_to_Set : CoeSort (Join 𝕜 V P) (Set P) where coe := carrier

/-- This provides a handy way to reason about the carrier. -/
theorem carrier_mem (j : Join 𝕜 V P) {p : P} :
    p ∈ j.carrier ↔ (p ∈ j.side0) ∨ (p ∈ j.side1) ∨ (∃ p₀ : j.side0, ∃ p₁ : j.side1, p ∈ segmentOO 𝕜 ↑p₀ ↑p₁) := by
  conv => lhs; simp only [carrier_def, segment_points_def, Set.union_def, Set.mem_setOf, Set.mem_iUnion]; simp only [or_assoc]
  conv => rhs; simp only [Set.mem_setOf]
  simp only [Prod.exists]

/-- The carrier's left interior of an `Join` is the set consisting of the left side
and the segment points. -/
def carrier_interior0 (j : Join 𝕜 V P) : Set P := j.side0 ∪ j.segment_points

/-- The defintion of the carrier's left interior. -/
def carrier_interior0_def (j : Join 𝕜 V P) : j.carrier_interior0 = j.side0 ∪ j.segment_points := rfl

/-- The carrier's right interior of an `Join` is the set consisting of the right side
and the segment points. -/
def carrier_interior1 (j : Join 𝕜 V P) : Set P := j.segment_points ∪ j.side1

/-- The defintion of the carrier's left interior. -/
def carrier_interior1_def (j : Join 𝕜 V P) : j.carrier_interior1 = j.segment_points ∪ j.side1 := rfl

/-- The carrier's  interior of an `Join` is the set consisting of the
segment points. -/
def carrier_interior (j : Join 𝕜 V P) : Set P := j.segment_points

/-- The defintion of the carrier's interior. -/
def carrier_interior_def (j : Join 𝕜 V P) : j.carrier_interior = j.segment_points := rfl

/-- The first side is in the carrier of a join. -/
theorem side0_subset_carrier (j : Join 𝕜 V P) : j.side0 ⊆ j.carrier := by
  simp only [carrier_def, Set.union_assoc, Set.subset_union_left]

/-- The second side is in the carrier of a join. -/
theorem side1_subset_carrier (j : Join 𝕜 V P) : j.side1 ⊆ j.carrier := by
  simp only [carrier_def, Set.union_assoc, Set.union_comm]
  rw [← Set.union_assoc, Set.union_comm]; simp only [Set.subset_union_left]


/-- Two affine joins with one side and the carriers equal are equal. -/
private theorem carrier_eq_imp_eq (j j': Join 𝕜 V P) (hs0 : j.side0 = j'.side0)
    (hc : j.carrier = j'.carrier) : j = j' := by
  rw [eq]
  apply And.intro hs0
  admit

/-- Two affine joins with one side equal are equal iff their carriers are equal. -/
theorem carrier_eq_iff_eq (j j': Join 𝕜 V P) (hs0 : j.side0 = j'.side0) :
      j.carrier = j'.carrier ↔ j = j' := by
  constructor
  · intro h; exact j.carrier_eq_imp_eq j' hs0 h
  · intro h; rw [h]

/-- This interchanges the two sides of a join. This is used mainly to simplify proofs. -/
def flip (j : Join 𝕜 V P) : Join 𝕜 V P where
  side0 := j.side1
  side1 := j.side0
  sides_disjoint := by rw [Set.inter_comm]; exact j.sides_disjoint
  lines_do_not_intersect := by
    intro a b a' b' ha hb ha' hb' hi
    rw [segmentOO_symm 𝕜 a b] at hi; rw [segmentOO_symm 𝕜 a' b'] at hi
    exact (j.lines_do_not_intersect hb ha hb' ha' $ hi).symm

/-- States that the sides are exchanged after a flip of a join. -/
theorem flipped_side0_side1 (j : Join 𝕜 V P) : j.side0 = j.flip.side1 := by rfl

/-- States that the sides are exchanged after a flip of a join. -/
theorem flipped_side1_side0 (j : Join 𝕜 V P) : j.side1 = j.flip.side0 := by rfl

/-- Flipping does not change the segment elements of a join. -/
theorem flipped_segment_elements_same (j : Join 𝕜 V P) : j.segment_points = j.flip.segment_points := by
  simp only [segment_points_def]
  ext x
  simp only [Set.mem_iUnion]
  constructor <;>
  · rintro ⟨⟨p0, p1⟩, h⟩; use ⟨p1, p0⟩; rw [segmentOO_symm]; exact h

/-- Flipping does not change the carrier of a join. -/
theorem flipped_carrier_same (j : Join 𝕜 V P) : j.carrier = j.flip.carrier := by
  simp only [carrier_def]
  rw [←flipped_segment_elements_same]
  simp only [flip, side0, side1]
  rw [Set.union_comm j.side1 j.side0]

/-- Flipping does not change the carrier of a join. -/
theorem flipped_carrier_interior0_carrier_interior1 (j : Join 𝕜 V P) : j.carrier_interior0 = j.flip.carrier_interior1 := by
  simp only [carrier_interior0_def, carrier_interior1_def]
  rw [←flipped_segment_elements_same]
  simp only [flip, side0, side1]
  rw [Set.union_comm]

/-- Flipping does not change the carrier of a join. -/
theorem flipped_carrier_interior1_carrier_interior0 (j : Join 𝕜 V P) : j.carrier_interior1 = j.flip.carrier_interior0 := by
  simp only [carrier_interior0_def, carrier_interior1_def]
  rw [←flipped_segment_elements_same]
  simp only [flip, side0, side1]
  rw [Set.union_comm]

/-- Flipping does not change the carrier interior of a join. -/
theorem flipped_carrier_interior_same (j : Join 𝕜 V P) : j.carrier_interior = j.flip.carrier_interior := by
  simp only [carrier_interior_def]
  rw [←flipped_segment_elements_same]

/-- If either side of a join is empty, the set of segment elements is empty. -/
theorem side_empty_imp_segements_empty (j : Join 𝕜 V P) (he : j.side0 = ∅ ∨ j.side1 = ∅) : j.segment_points = ∅ := by
  simp only [segment_points_def]
  ext p
  simp only [Set.mem_empty_iff_false]
  cases he with
  | inl he0 => rw [he0]; simp [Set.mem_empty_iff_false]
  | inr he1 => rw [he1]; simp [Set.mem_empty_iff_false]

/-- If `side0` is empty then the join reduces to `side1`. -/
theorem side0_empty_imp_side1 (j : Join 𝕜 V P) (he : j.side0 = ∅) : j.carrier = j.side1 := by
  simp only [carrier_def]; rw [he, j.side_empty_imp_segements_empty (Or.inl he)]
  simp only [Set.empty_union, Set.union_empty]

/-- If `side1` is empty then the join reduces to `side0`. -/
theorem side1_empty_imp_side0 (j : Join 𝕜 V P) (he : j.side1 = ∅) : j.carrier = j.side0 := by
  rw [j.flipped_carrier_same, j.flipped_side0_side1]
  exact (j.flip).side0_empty_imp_side1 he

/-- If both sides of a join are empty then the carrier of the join is empty. -/
theorem sides_empty_imp_empty (j : Join 𝕜 V P) (he : j.side0 = ∅ ∧ j.side1 = ∅) : j.carrier = ∅ := by
  rcases he with ⟨he0, he1⟩; simp [j.side0_empty_imp_side1 he0]; rw [he1]

end «Affine Join sets»

end Affine.Join

end «Affine Join structure»

-- ********************************************************************
section «Join under affine maps»

/-!
## Joins under affine maps

This section shows how affine joins behave under affine maps. The conditon
that the lines that define both affine joins and cones do not intersect
unless they are identical requires that we restrict to injective maps.
-/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {W : Type v} [AddCommGroup W] [Module 𝕜 W]
variable {Q : Type w} [AddTorsor W Q]

namespace Affine.Join

/-- This defines how a join is mapped under affine maps. We first define
the join that results from the map. Later, we show that this is the same
as applying the affine map to the join as a set. -/
def map_affine_injective (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) : Join 𝕜 W Q where
  side0 := m '' j.side0
  side1 := m '' j.side1
  sides_disjoint := by
    rw [←Set.image_inter, Set.image_eq_empty]
    exact j.sides_disjoint
    exact hmi
  lines_do_not_intersect := by
    intro ai bi ai' bi' hai hbi hai' hbi'
    simp only [Set.mem_image] at hai; rcases hai with ⟨a, ⟨ha, hma⟩⟩
    simp only [Set.mem_image] at hbi; rcases hbi with ⟨b, ⟨hb, hmb⟩⟩
    simp only [Set.mem_image] at hai'; rcases hai' with ⟨a', ⟨ha', hma'⟩⟩
    simp only [Set.mem_image] at hbi'; rcases hbi' with ⟨b', ⟨hb', hmb'⟩⟩
    rw [←hma, ←hmb, ←hma', ←hmb', hmi.eq_iff, hmi.eq_iff]
    intro h
    rw [Affine.segmentOO, Affine.segmentOO, ←AffineMap.image_map_lineMap,
      ←AffineMap.image_map_lineMap, ←Set.image_inter] at h
    exact j.lines_do_not_intersect ha hb ha' hb' $ Set.image_eq_not_empty.mp h
    exact hmi

/-- `map_affine_injective` takes `Join.side0` to `Join.side0`. -/
@[simp] theorem map_affine_injective_side0 (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (j.map_affine_injective m hmi).side0 = m '' j.side0 := rfl

/-- `map_affine_injective` takes `Join.side1` to `Join.side1`. -/
@[simp] theorem map_affine_injective_side1 (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (j.map_affine_injective m hmi).side1 = m '' j.side1 := rfl

/-- The `segment_points` of the affine join given by `Join.map_affine_injective`
is the image of the `segment_points` of the original affine join under the
affine map. -/
theorem map_affine_injective_segment_points
    (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (j.map_affine_injective m hmi).segment_points = m '' j.segment_points := by
  simp only [segment_points_def, Set.image_iUnion, Affine.segmentOO_maps_to_segmentOO]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨q0, q1⟩, hp0p1⟩; simp only at hp0p1
    rcases (Set.mem_image m j.side0 q0.val).mp q0.property with ⟨p0, ⟨hp0, hmp0q0⟩⟩
    rcases (Set.mem_image m j.side1 q1.val).mp q1.property with ⟨p1, ⟨hp1, hmp1q1⟩⟩
    use ⟨⟨p0, hp0⟩, ⟨p1, hp1⟩⟩
    rw [hmp0q0, hmp1q1]
    exact hp0p1
  · rintro ⟨p0p1, hp0p1⟩; use ⟨Set.apply_subtype m p0p1.1, Set.apply_subtype m p0p1.2⟩; exact hp0p1

/-- The carrier of the affine join given by `Join.map_affine_injective`
is the image of the carrier of the original affine join under the
affine map . -/
theorem map_affine_injective_carrier
    (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    j.map_affine_injective m hmi = m '' j := by
  simp only [carrier_def, Set.image_union]
  rw [map_affine_injective_side0, map_affine_injective_side1, map_affine_injective_segment_points]

/-- The carrier's interior of the affine join given by `Join.map_affine_injective`
is the image of the carrier's interior of the original affine join under the
affine map . -/
theorem map_affine_injective_carrier_interior0
    (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (j.map_affine_injective m hmi).carrier_interior0 = m '' j.carrier_interior0 := by
  simp only [carrier_interior0_def, Set.image_union]
  rw [map_affine_injective_side0, map_affine_injective_segment_points]

/-- The carrier's interior of the affine join given by `Join.map_affine_injective`
is the image of the carrier's interior of the original affine join under the
affine map . -/
theorem map_affine_injective_carrier_interior1
    (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (j.map_affine_injective m hmi).carrier_interior1 = m '' j.carrier_interior1 := by
  simp only [carrier_interior1_def, Set.image_union]
  rw [map_affine_injective_side1, map_affine_injective_segment_points]

/-- The carrier's interior of the affine join given by `Join.map_affine_injective`
is the image of the carrier's interior of the original affine join under the
affine map . -/
theorem map_affine_injective_carrier_interior
    (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) :
    (j.map_affine_injective m hmi).carrier_interior = m '' j.carrier_interior := by
  simp only [carrier_interior_def]
  rw [map_affine_injective_segment_points]

end Affine.Join

end «Join under affine maps»

-- ********************************************************************
--#lint
