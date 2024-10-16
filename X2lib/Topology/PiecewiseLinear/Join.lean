/-
Copyright (c) 2024 Stephan maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Subset
import Mathlib.Order.SetNotation
import Mathlib.Algebra.AddTorsor
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Ray
--import Mathlib.Algebra.Field.Basic
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

import X2lib.Topology.PiecewiseLinear.Module

/-!
# Joins and cones

In this file we introduce `Join` and `Cone` objects as constructs in affine ambient space.
`Cone` will serve as building block for PL-topology.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Rourke] for ann introduction to PL-topology.
-/

universe u v w

-- ********************************************************************
section «Join types»

/-!
## Join and Cone

 -/

/-- A join between two sets in an affine space is the set of line segments between pairs
of points from the two sets. This structure captures the pairs of sets but not the line
segments joining them. For this see the separate method `Join.carrier`. -/
@[ext]
structure Join
  (𝕜 : Type u) [OrderedCommRing 𝕜]
  (V : Type v) [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
  (P : Type w) [AddTorsor V P] where
  /-- The left set of the join.-/
  side0 : Set P
  /-- The right set of the join.-/
  side1 : Set P

/-- A cone is a join, where one set consists of only one point, the vertex, and where
each point of the join between vertex and base lies on a unique line between vertex
and base. This structure captures the pairs of sets but not the line segments joining them.
For this see the separate method `Join.carrier`.-/
@[ext]
structure Cone
  (𝕜 : Type u) [StrictOrderedCommRing 𝕜]
  (V : Type v) [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
  (P : Type w) [AddTorsor V P] where
  /-- This is the tip of the cone.-/
  vertex : P
  /-- The base.-/
  base : Set P
  /-- The cone must not be in the cone's base. -/
  vertex_not_in_base' : vertex ∉ base
  /-- Different base points represent different rays. This is a stronger statement than
  only demanding that segments from the vertex to base-points meet only at the vertex. -/
  unique_rays' {b₁ b₂ : P} (hb₁ : b₁ ∈ base) (hb₂ : b₂ ∈ base) : b₁ = b₂ ↔ SameRay 𝕜 (↑b₁ -ᵥ vertex) (↑b₂ -ᵥ vertex)

end «Join types»

section «Cone API»

/-! This section exposes the API of a cone. -/

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Cone

/-- The vertex of a cone is not in the base. -/
def vertex_not_in_base (c : Cone 𝕜 V P) : c.vertex ∉ c.base := c.vertex_not_in_base'

/-- Different base points represent different rays. This is a stronger statement than
  only demanding that segments from the vertex to base-points meet only at the vertex. -/
def unique_rays (c : Cone 𝕜 V P) {b₁ b₂ : P} (hb₁ : b₁ ∈ c.base) (hb₂ : b₂ ∈ c.base) : b₁ = b₂ ↔ SameRay 𝕜 (↑b₁ -ᵥ c.vertex) (↑b₂ -ᵥ c.vertex) := c.unique_rays' hb₁ hb₂

end Cone

end «Cone API»

-- ********************************************************************
section «Join structure»

/-!
## The structure of joins
 -/

variable {𝕜 : Type u} [OrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Join

/-- The points strictly between two points in either side of the join.
TODO Use this to rewrite everything using segmentOO instead of affineSegment -/
def segmenOO (j : Join 𝕜 V P) (_ : p₀ ∈ j.side0) (_ : p₁ ∈ j.side1) : Set P :=
  AffineMap.lineMap p₀ p₁ '' Set.Ioo (0:𝕜) 1

/-- The join is made up of all line segments between pairs of points from
the left and right sets. This defines the segment that make up the join. -/
def segment_set (j : Join 𝕜 V P) : Set (Set P) := { s | ∃ p₀ ∈ j.side0, ∃ p₁ ∈ j.side1, s = affineSegment 𝕜 p₀ p₁ }

/-- The join is made up of all line segments between pairs of points from
the left and right sets. This defines the segment that make up the join. -/
def segment_elements (j : Join 𝕜 V P) : Set P := { p | ∃ p₀ ∈ j.side0, ∃ p₁ ∈ j.side1, p ∈ affineSegment 𝕜 p₀ p₁ }

/-- The join is made up of all line segments between pairs of points from
the left and right sets. This defines the segment that make up the join. -/
def segment_elements' (j : Join 𝕜 V P) : Set P := ⋃₀ j.segment_set

/-- The two definitions of the total space of segments coincide. -/
theorem segment_elements'' (j : Join 𝕜 V P) : j.segment_elements' = j.segment_elements := by
  simp only [segment_elements, segment_elements', segment_set]
  ext x; apply Iff.intro
  . rintro ⟨t, ⟨ht, hpt⟩⟩; simp only [Set.mem_setOf] at ht; simp only [Set.mem_setOf]
    rcases ht with ⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, htseg⟩⟩⟩⟩
    rw [htseg, Set.mem_def] at hpt
    exact ⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, hpt⟩⟩⟩⟩
  . rintro ⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, htseg⟩⟩⟩⟩
    rw [Set.mem_sUnion]; simp only [Set.mem_setOf]
    exists (affineSegment 𝕜 p0 p1)
    exact ⟨⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, rfl⟩⟩⟩⟩, htseg⟩

/-- The join is made up of all line segments between pairs of points from
the left and right sets. Note that the definition adds the sides of the join
by taking unions. This is done to ensure that the join is defined when one
side is empty. -/
def carrier (j : Join 𝕜 V P) : Set P := j.side0 ∪ j.side1 ∪ j.segment_elements

/-- This provides a handy way to reason about the carrier. -/
theorem carrier_def (j : Join 𝕜 V P) {p : P} :
    p ∈ j.carrier ↔ (p ∈ j.side0) ∨ (p ∈ j.side1) ∨ (∃ p₀ ∈ j.side0, ∃ p₁ ∈ j.side1, p ∈ affineSegment 𝕜 p₀ p₁) := by
  conv => lhs; simp only [carrier, segment_elements, Set.union_def, Set.mem_setOf]
  conv => rhs; simp only [Set.mem_setOf]
  conv => lhs; simp only [or_assoc]
  done

/-- This allows us to view a `Join` as a `Set P`. The set is the carrer of the join. -/
instance CoeSort_to_Set : CoeSort (Join 𝕜 V P) (Set P) where coe j := j.carrier

/-- The segments between the sides of a join are contained in the join. -/
theorem carrier_contains_segment (j : Join 𝕜 V P) {p₀ p₁ : P} (hp0s0 : p₀ ∈ j.side0) (hp1s1: p₁ ∈ j.side1) :
  affineSegment 𝕜 p₀ p₁ ⊆ j := by
  intro p hpseg
  have h : ∃ p₀ ∈ j.side0, ∃ p₁ ∈ j.side1, p ∈ affineSegment 𝕜 p₀ p₁ := by exact ⟨p₀, ⟨hp0s0, ⟨p₁, ⟨hp1s1, hpseg⟩⟩⟩⟩
  exact (carrier_def j).mpr (Or.inr (Or.inr h))
  done

/-- The first side is in the carrier of a join. -/
theorem side0_subset_carrier (j : Join 𝕜 V P) : j.side0 ⊆ j.carrier := by
  simp only [carrier, Set.union_assoc, Set.subset_union_left]

/-- The first side is in the carrier of a join. -/
theorem side0_element_in_carrier (j : Join 𝕜 V P) {p :P } (hp : p ∈ j.side0): p ∈ j.carrier := by
  exact (Set.subset_def.mp (side0_subset_carrier j)) p hp

/-- The second side is in the carrier of a join. -/
theorem side1_subset_carrier (j : Join 𝕜 V P) : j.side1 ⊆ j.carrier := by
  simp only [carrier, Set.union_assoc, Set.union_comm]
  rw [← Set.union_assoc, Set.union_comm]; simp only [Set.subset_union_left]

/-- The second side is in the carrier of a join. -/
theorem side1_element_in_carrier (j : Join 𝕜 V P) {p : P} (hp: p ∈ j.side1) : p ∈ j.carrier := by
  exact (Set.subset_def.mp (side1_subset_carrier j)) p hp

/-- This interchanges the two sides of a join. This is used mainly to simplify proofs. -/
def flip (j : Join 𝕜 V P) : Join 𝕜 V P where
  side0 := j.side1
  side1 := j.side0

/-- States that the sides are exchanged after a flip of a join. -/
theorem flipped_side0_side1 (j : Join 𝕜 V P) : j.side0 = j.flip.side1 := by rfl

/-- States that the sides are exchanged after a flip of a join. -/
theorem flipped_side1_side0 (j : Join 𝕜 V P) : j.side1 = j.flip.side0 := by rfl

/-- Flipping does not change the segment elements of a join. -/
theorem flipped_segment_elements_same (j : Join 𝕜 V P) : j.segment_elements = j.flip.segment_elements := by
  simp only [segment_elements, flip, side0, side1]
  ext p; simp only [Set.mem_setOf]
  apply Iff.intro
  . rintro ⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, hp⟩⟩⟩⟩; rw [affineSegment_comm 𝕜 p0 p1] at hp; exact ⟨p1, ⟨hp1s1, ⟨p0, ⟨hp0s0, hp⟩⟩⟩⟩
  . rintro ⟨p1, ⟨hp1s1, ⟨p0, ⟨hp0s0, hp⟩⟩⟩⟩; rw [affineSegment_comm 𝕜 p1 p0] at hp; exact ⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, hp⟩⟩⟩⟩
  done

/-- Flipping does not change the carrier of a join. -/
theorem flipped_carrier_same (j : Join 𝕜 V P) : j.carrier = j.flip.carrier := by
  simp only [carrier]
  rw [←flipped_segment_elements_same]
  simp only [flip, side0, side1]
  rw [Set.union_comm j.side1 j.side0]
  done

/-- If either side of a join is empty, the set of segment elements is empty. -/
theorem side_empty_imp_segements_empty (j : Join 𝕜 V P) (he : j.side0 = ∅ ∨ j.side1 = ∅) : j.segment_elements = ∅ := by
  unfold segment_elements; ext p; simp only [Set.mem_empty_iff_false]
  cases he with
  | inl he0 => rw [he0]; simp [Set.mem_empty_iff_false]
  | inr he1 => rw [he1]; simp [Set.mem_empty_iff_false]
  done

/-- If `side0` is empty then the join reduces to `side1`. -/
theorem side0_empty_imp_side1 (j : Join 𝕜 V P) (he : j.side0 = ∅) : j.carrier = j.side1 := by
  unfold carrier; rw [he, j.side_empty_imp_segements_empty (Or.inl he)]
  simp only [Set.empty_union, Set.union_empty]
  done

/-- If `side1` is empty then the join reduces to `side0`. -/
theorem side1_empty_imp_side0 (j : Join 𝕜 V P) (he : j.side1 = ∅) : j.carrier = j.side0 := by
  rw [j.flipped_carrier_same, j.flipped_side0_side1]
  exact (j.flip).side0_empty_imp_side1 he
  done

/-- If both sides of a join are empty then the carrier of the join is empty. -/
theorem sides_empty_imp_empty (j : Join 𝕜 V P) (he : j.side0 = ∅ ∧ j.side1 = ∅) : j.carrier = ∅ := by
  rcases he with ⟨he0, he1⟩; simp [j.side0_empty_imp_side1 he0]; rw [he1]
  done

end Join

end «Join structure»

-- ********************************************************************
section «Cone basics»

/-!
## Basic definitions for cones

 -/

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Cone

/-- This allows us to view a `Cone` as a `Join`. -/
def to_join (c : Cone 𝕜 V P) : Join 𝕜 V P where
    side0 := { c.vertex }
    side1 := c.base

/-- This will force a cast of `Cone` to `Join`.-/
instance CoeSort_to_Join: CoeSort (Cone 𝕜 V P) (Join 𝕜 V P) where
  coe c := c.to_join

/-- The vertex is the only element of `side0`. -/
theorem vertex_is_side0 (c : Cone 𝕜 V P) : c.to_join.side0 = { c.vertex } := by
  simp only [Cone.to_join]

/-- The vertex is the only element of `side0`. -/
theorem vertex_in_side0 (c : Cone 𝕜 V P) : c.vertex ∈ c.to_join.side0 :=
  Set.mem_singleton c.vertex

/-- The base is `side1` of the join. -/
theorem base_is_side1 (c : Cone 𝕜 V P) : c.base = c.to_join.side1 := rfl

/-- The complement of the vertex. -/
def vertex_complement (c : Cone 𝕜 V P) : Set P := { x | x ≠ c.vertex }

/-- The vector pointing from the vertex to a point n the vertex-complement is not zero. -/
def direction_to_complement_neq_zero (c : Cone 𝕜 V P) (hp : p ∈ c.vertex_complement) : ↑p -ᵥ c.vertex ≠ 0 := by
  simp only [ne_eq, vsub_eq_zero_iff_eq, not_false_eq_true]
  simp only [vertex_complement, Set.mem_setOf] at hp
  exact hp

/-- The vector pointing from the vertex to a point n the vertex-complement is not zero. -/
def direction_to_complement_neq_zero' (c : Cone 𝕜 V P) (p : c.vertex_complement) : ↑p -ᵥ c.vertex ≠ 0 := by
  exact c.direction_to_complement_neq_zero p.property

/-- Base elements are never equal to the vertex. -/
theorem base_point_neq_vertex (c : Cone 𝕜 V P) (hb : b ∈ c.base) : b ≠ c.vertex := by
  intro hyp; rw [hyp] at hb; have _ := c.vertex_not_in_base'; contradiction

/-- Base elements are never equal to the vertex. -/
theorem base_point_neq_vertex' (c : Cone 𝕜 V P) (b : c.base) : ↑b ≠ c.vertex :=
  c.base_point_neq_vertex b.property

/-- The vector pointing from the vertex to a base-element is not zero. -/
def base_direction_neq_zero (c : Cone 𝕜 V P) (hb : b ∈ c.base) : ↑b -ᵥ c.vertex ≠ 0 := by
  simp only [ne_eq, vsub_eq_zero_iff_eq, not_false_eq_true]; exact c.base_point_neq_vertex hb

/-- The vector pointing from the vertex to a base-element is not zero. -/
def base_direction_neq_zero' (c : Cone 𝕜 V P) (b : c.base) : ↑b -ᵥ c.vertex ≠ 0 :=
  c.base_direction_neq_zero b.property

/-- View the base of cone as a subset of the vertex-complement. -/
def base_as_subset_vertex_complement (c : Cone 𝕜 V P) : Set c.vertex_complement :=
  { p : c.vertex_complement | p.val ∈ c.base }

/-- This allows us to view a base-point as being in the complement of the vertex. -/
def base_to_vertex_complement (c : Cone 𝕜 V P) (hb : b ∈ c.base) : c.vertex_complement where
  val := b
  property := c.base_point_neq_vertex hb

/-- This allows us to view a base-point as being in the complement of the vertex. -/
def base_to_vertex_complement' (c : Cone 𝕜 V P) (b : c.base) : c.vertex_complement where
  val := b.val
  property := c.base_point_neq_vertex b.property

/-- This allows us to view a base-point as being in the complement of the vertex. -/
theorem base_point_as_vertex_complement (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.base_to_vertex_complement hb ∈ c.base_as_subset_vertex_complement := by
  simp [base_to_vertex_complement, base_as_subset_vertex_complement]; exact hb

/-- View a point in the base as a point in the vertex-complement. -/
theorem vertex_complement_as_base_point (c : Cone 𝕜 V P)
    (p : c.vertex_complement) (hp : p.val ∈ c.base) : p ∈ c.base_as_subset_vertex_complement := by
  simp only [base_as_subset_vertex_complement, Set.mem_setOf]; assumption

end Cone

end «Cone basics»

-- ********************************************************************
section «Cone vector and lineMap»

/-!
## Lines in cones

 -/

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Cone

/-- The vector pointing from the vertex to the given point, i.e. `p -ᵥ c.vertex`.-/
def vector_to (c : Cone 𝕜 V P) (p : P) : V := p -ᵥ c.vertex

/-- The set of vectors pointing from the vertex to a base-point.-/
def base_vectors (c : Cone 𝕜 V P) : Set V := c.base -ᵥ { c.vertex }

/-- The closed segment between the vertex and a base-point. -/
def lineMap (c : Cone 𝕜 V P) (_ : b ∈ c.base) : 𝕜 →ᵃ[𝕜] P := AffineMap.lineMap c.vertex b

theorem vector_to_lineMap_k (c : Cone 𝕜 V P) (hb : b ∈ c.base) (k : 𝕜) :
    c.vector_to (c.lineMap hb k) = k • (c.vector_to b) := by
  --unfold segmentLineMap; unfold AffineMap.lineMap; unfold vector_to
  dsimp [lineMap, AffineMap.lineMap, vector_to]; simp; done

/-- The segment line map is injective. -/
theorem lineMap_injective (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    Function.Injective (c.lineMap hb) := by
  intro k1 k2 hk1k2
  simp [lineMap, AffineMap.lineMap ] at hk1k2
  exact smul_left_injective 𝕜 (c.base_direction_neq_zero hb) hk1k2
  done

/-- The segment line map maps 0 to the vertex. -/
theorem lineMap_0_to_vertex (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.lineMap hb 0 = c.vertex := by dsimp [lineMap, AffineMap.lineMap]; simp

/-- The segment line map maps 1 to the base-point. -/
theorem lineMap_1_to_base_point (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.lineMap hb 1 = b := by dsimp [lineMap, AffineMap.lineMap]; simp

/-- The segment line map maps `k ≠ 0` to points different from the vertex. -/
theorem lineMap_k_neq_vertex (c : Cone 𝕜 V P) (hb : b ∈ c.base) (hk : (0:𝕜) < k) :
    c.lineMap hb k ≠ c.vertex := by
  have hh0 := (c.lineMap_injective hb).ne (ne_of_gt hk)
  rw [c.lineMap_0_to_vertex hb] at hh0
  exact hh0

/-- The segment line map maps `k ≠ 1` to points different from the base-point. -/
theorem lineMap_k_neq_base_point (c : Cone 𝕜 V P) (hb : b ∈ c.base) (hk : k ≠ (1:𝕜)) :
    c.lineMap hb k ≠ b := by
  have hh1 := (c.lineMap_injective hb).ne hk
  rw [c.lineMap_1_to_base_point hb] at hh1
  exact hh1

/-- The closed segment between the vertex and a base-point. -/
def segmentCC (c : Cone 𝕜 V P) (hb : b ∈ c.base) : Set P := (c.lineMap hb) '' Set.Icc (0 : 𝕜) 1

/-- The `segmentCC` is exactly the `affineSegment` defined in `Mathlib.Analysis.Convex.Between`. -/
theorem segmentCC_eq_affineSegment (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.segmentCC hb = affineSegment 𝕜 c.vertex b := by rfl

/-- The half-open segment between the vertex and a base-point. -/
def segmentOC (c : Cone 𝕜 V P) (hb : b ∈ c.base) : Set P := (c.lineMap hb) '' Set.Ioc (0 : 𝕜) 1

/-- The open segment between the vertex and a base-point. -/
def segmentOO (c : Cone 𝕜 V P) (hb : b ∈ c.base) : Set P := (c.lineMap hb) '' Set.Ioo (0 : 𝕜) 1

private theorem zero_union_Ioc_Icc : { (0 : 𝕜) } ∪ Set.Ioc (0 : 𝕜) 1 = Set.Icc (0 : 𝕜) 1 := by
  admit

/-- The `segmentCC` is the union of the vertex ans `segmentOC`. -/
theorem segmentCC_eq_vertex_union_segmentOC (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.segmentCC hb = Set.insert c.vertex (c.segmentOC hb) := by
  have h := Set.image_union (c.lineMap hb) { (0 : 𝕜) } (Set.Ioc (0 : 𝕜) 1)
  rw [zero_union_Ioc_Icc, ←segmentCC, ←segmentOC, Set.image_singleton, c.lineMap_0_to_vertex] at h
  exact h

/- Two segments with nonempty intersection apart from the vertex are the same segment. -/
-- theorem segments_with_common_point_same_segment (c : Cone 𝕜 V P) (hb₁ : b₁ ∈ c.base) (hb₂ : b₂ ∈ c.base)
--     (hpnv : p ≠ c.vertex) (hpi : p ∈ c.segmentCC hb₁ ∩ c.segmentCC hb₂) : b₁ = b₂ := by
--   simp only [c.unique_rays hb₁ hb₂, SameRay, vsub_eq_zero_iff_eq, exists_and_left, c.base_point_neq_vertex hb₁, c.base_point_neq_vertex hb₂, false_or]
--   simp only [Set.image, Set.mem_inter_iff, segmentCC_eq_affineSegment] at hpi
--   rcases hpi with ⟨h1, h2⟩
--   simp only [Set.mem_def] at h1; rcases h1 with ⟨c1, ⟨hc1, hc1s⟩⟩; rw [AffineMap.lineMap_apply c.vertex ↑b₁ c1] at hc1s
--   simp only [Set.mem_def] at h2; rcases h2 with ⟨c2, ⟨hc2, hc2s⟩⟩; rw [AffineMap.lineMap_apply c.vertex ↑b₂ c2] at hc2s
--   have hc1ne0 : c1 ≠ 0 := by by_contra h0; rw [h0] at hc1s; simp at hc1s; absurd hpnv; exact hc1s.symm
--   have hc2ne0 : c2 ≠ 0 := by by_contra h0; rw [h0] at hc2s; simp at hc2s; absurd hpnv; exact hc2s.symm
--   have hc1 : 0 < c1 := lt_of_le_of_ne (Set.mem_Icc.mp hc1).left hc1ne0.symm
--   have hc2 : 0 < c2 := lt_of_le_of_ne (Set.mem_Icc.mp hc2).left hc2ne0.symm
--   use c1; apply And.intro hc1; use c2; apply And.intro hc2
--   exact (vadd_right_cancel_iff c.vertex).mp (Eq.trans hc1s hc2s.symm)

end Cone

end «Cone vector and lineMap»

-- ********************************************************************
section «Cone carrier»

/-!
## The carrier of a cone

 -/

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Cone

/-- The carrier of a `Cone` is the carier of the `Join`. -/
def carrier (c : Cone 𝕜 V P) : Set P := c.to_join.carrier

/-- This restates the defintion of the carrier. -/
theorem carrier_def (c : Cone 𝕜 V P) :
    c.carrier = { c.vertex } ∪ c.base ∪ c.to_join.segment_elements := by
  unfold carrier; unfold Join.carrier
  rw [c.vertex_is_side0, c.base_is_side1]; done

/-- The carrier of a cone contains the vertex. -/
theorem vertex_in_carrier (c : Cone 𝕜 V P) : c.vertex ∈ c.carrier := by
  exact Set.mem_of_subset_of_mem c.to_join.side0_subset_carrier c.vertex_in_side0

/-- The base is in the carrier of a cone. -/
theorem base_subset_of_carrier (c : Cone 𝕜 V P) : c.base ⊆ c.carrier := by
  simp only [carrier, c.base_is_side1, c.to_join.side1_subset_carrier]

/-- A point in the carrier is on a segment-line. -/
theorem point_in_carrier_on_lineMap (c : Cone 𝕜 V P) (hpc : p ∈ c.carrier) (hpv : p ≠ c.vertex) :
    ∃ b : c.base, ∃ k : 𝕜, 0 < k ∧ k ≤ 1 ∧ p = c.lineMap b.property k := by
  match hpc with
  | Or.inl (Or.inl h) =>
    simp only [c.vertex_is_side0, Set.mem_singleton_iff] at h
    contradiction
  | Or.inl (Or.inr h) =>
    rw [←c.base_is_side1] at h
    use ⟨p, h⟩, 1
    simp only [c.lineMap_1_to_base_point, Set.right_mem_Ioc, zero_lt_one]
    simp
  | Or.inr h =>
    simp only [Join.segment_elements, Set.mem_setOf, c.vertex_is_side0, Set.mem_singleton_iff] at h
    rw [←c.base_is_side1] at h
    rcases h with ⟨p0, ⟨hp0v, ⟨b, ⟨hb, hpb⟩⟩⟩⟩
    rw [hp0v] at hpb; simp only [affineSegment, Set.mem_image] at hpb
    rcases hpb with ⟨k, ⟨hk, hlkp⟩⟩
    use ⟨b, hb⟩, k
    have hkneq0 : k ≠ 0 := by
      apply (c.lineMap_injective hb).ne_iff.mp
      rw [c.lineMap_0_to_vertex, lineMap, hlkp]
      exact hpv
    apply And.intro (lt_of_le_of_ne (Set.mem_Icc.mp hk).left hkneq0.symm)
    apply And.intro (Set.mem_Icc.mp hk).right
    simp only [lineMap]
    exact hlkp.symm

/-- The segment between the vertex and the base point is contained in the carrier. -/
theorem segmentCC_subset_carrier (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
  c.segmentCC hb ⊆ c := by exact c.to_join.carrier_contains_segment c.vertex_in_side0 hb

/- `segmentLineMap` maps into the carrier of the cone. -/
-- theorem _maps_to (c : Cone 𝕜 V P) (hb : b ∈ c.base) (hk: k ∈ Set.Icc (0:𝕜) 1) :
--     c.lineMap hb k ∈ c.carrier := by
--   have h : c.lineMap hb k ∈ c.segmentCC hb := by simp only [segmentCC]; use k
--   exact c.segmentCC_subset_carrier hb $ h

end Cone

end «Cone carrier»

-- ********************************************************************
section «Cone rays»

/-!
## Rays of cones

 -/

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Cone

/-- This maps each point different from the cone's vertex to its ray in ray-space. -/
def ray_to (c : Cone 𝕜 V P) (hp : p ≠ c.vertex) : Module.Ray 𝕜 V :=
  rayOfNeZero 𝕜 (c.vector_to p) (vsub_ne_zero.mpr hp)

/-- This maps a base-point to its ray in ray-space. -/
def ray_to' (c : Cone 𝕜 V P) (hb : b ∈ c.base) : Module.Ray 𝕜 V :=
  c.ray_to (c.base_point_neq_vertex hb)

/-- This maps each point different from the cone's vertex to its ray in ray-space. -/
def ray_to'' (c : Cone 𝕜 V P) (p : c.vertex_complement) : Module.Ray 𝕜 V :=
  c.ray_to p.property

/-- The defintion of `to_ray` is independent of the cone used to define it. -/
theorem ray_to_independent_of_cone (c : Cone 𝕜 V P) (c' : Cone 𝕜 V P) (hv : c.vertex = c'.vertex) (hp : p ≠ c.vertex) :
    c.ray_to hp = c'.ray_to (hp ∘ (fun x => Eq.trans x hv.symm)) := by
  unfold ray_to; unfold vector_to
  have hp' := hp ∘ (fun x => Eq.trans x hv.symm)
  rw [ray_eq_iff (vsub_ne_zero.mpr hp) (vsub_ne_zero.mpr hp')]
  rw [hv]
  done

/-- This is a restatement of `SameRay.ray_eq_iff`. -/
theorem ray_to_eq_iff_same_ray (c : Cone 𝕜 V P) (hp₁ : p₁ ≠ c.vertex) (hp₂ : p₂ ≠ c.vertex) :
    c.ray_to hp₁ = c.ray_to hp₂ ↔ SameRay 𝕜 (c.vector_to p₁) (c.vector_to p₂) :=
  ray_eq_iff (vsub_ne_zero.mpr hp₁) (vsub_ne_zero.mpr hp₂)

/-- This is a restatement of `SameRay.exists_pos`. -/
theorem ray_to_eq_iff_exists_pos (c : Cone 𝕜 V P) (hp₁ : p₁ ≠ c.vertex) (hp₂ : p₂ ≠ c.vertex) :
    c.ray_to hp₁ = c.ray_to hp₂ ↔ ∃ (r₁ : 𝕜) (r₂ : 𝕜), 0 < r₁ ∧ 0 < r₂ ∧ r₁ • (c.vector_to p₁) = r₂ • (c.vector_to p₂) := by
  apply Iff.intro
  . intro hreq; rw [ray_to_eq_iff_same_ray] at hreq
    exact SameRay.exists_pos hreq (c.direction_to_complement_neq_zero hp₁) (c.direction_to_complement_neq_zero hp₂)
  . intro hk1k2
    exact (c.ray_to_eq_iff_same_ray hp₁ hp₂).mpr $ Or.inr $ Or.inr hk1k2

/-- This is a restatement of `SameRay.ray_eq_iff`. -/
theorem ray_to_eq_iff_same_ray' (c : Cone 𝕜 V P) (p₁ : c.vertex_complement) (p₂ : c.vertex_complement) :
    c.ray_to'' p₁ = c.ray_to'' p₂ ↔ SameRay 𝕜 (c.vector_to p₁.val) (c.vector_to p₂.val) :=
  ray_eq_iff (vsub_ne_zero.mpr p₁.property) (vsub_ne_zero.mpr p₂.property)

/-- This is a restatement of the property `unique_rays` that defines cones. -/
theorem ray_to_injective_on_base (c : Cone 𝕜 V P) (hb₁ : b₁ ∈ c.base) (hb₂ : b₂ ∈ c.base) :
    c.ray_to (c.base_point_neq_vertex hb₁) = c.ray_to (c.base_point_neq_vertex hb₂) ↔ b₁ = b₂ := by
  unfold ray_to; rw [ray_eq_iff]; exact (c.unique_rays hb₁ hb₂).symm

/-- This is the formal statement that mapping to rays is injective on the base. -/
theorem ray_to_injective_on_base' (c : Cone 𝕜 V P) : Set.InjOn c.ray_to'' c.base_as_subset_vertex_complement := by
  unfold Set.InjOn; unfold base_as_subset_vertex_complement; unfold ray_to''
  intro b1 hb1 b2 hb2 heqr
  simp only [Set.mem_setOf] at hb1; simp only [Set.mem_setOf] at hb2
  simp only [vertex_complement] at b1; simp only [vertex_complement] at b2
  rw [Subtype.mk_eq_mk]
  exact (c.ray_to_injective_on_base hb1 hb2).mp heqr

/-- The image of the base under the map `to_ray`. This is the set of rays running
from the vertex to the base points. -/
def rays' (c : Cone 𝕜 V P) : Set (Module.Ray 𝕜 V) := c.ray_to'' '' c.base_as_subset_vertex_complement

/-- The image of the base under the map `to_ray`. This is the set of rays running
from the vertex to the base points. -/
def rays (c : Cone 𝕜 V P) : Set (Module.Ray 𝕜 V) := { r : Module.Ray 𝕜 V | ∃ b : c.base, c.ray_to' b.property = r }

/-- Both definitions of the ray set agree. -/
theorem rays_eq_rays' (c : Cone 𝕜 V P) : c.rays' = c.rays := by

  admit

/-- Rays through base points are in `rays`. -/
theorem base_point_ray_in_rays (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.ray_to (c.base_point_neq_vertex hb) ∈ c.rays := by
  unfold rays; simp only [Set.mem_setOf]; use ⟨b, hb⟩; rfl; done

/-- Rays through base points are in `rays`. -/
theorem base_point_ray_in_rays' (c : Cone 𝕜 V P) (hb : b ∈ c.base) :
    c.ray_to' hb ∈ c.rays := by
  unfold rays; simp only [Set.mem_setOf]; use ⟨b, hb⟩; done

/-- Points in a segment from the vertex to a base point lie on the same ray
as the base point. -/
theorem point_on_lineMap_same_ray_as_base_point (c : Cone 𝕜 V P)
    (hb : b ∈ c.base) (hk : (0:𝕜) < k) :
    c.ray_to (c.lineMap_k_neq_vertex hb hk) = c.ray_to' hb := by
  unfold ray_to'
  rw [c.ray_to_eq_iff_exists_pos (c.lineMap_k_neq_vertex hb hk) (c.base_point_neq_vertex hb)]
  simp only [vector_to_lineMap_k]
  use 1, k
  apply And.intro zero_lt_one; apply And.intro hk; conv => lhs; simp only [smul_assoc, one_smul]
  done

/-- Points in the carrier of a cone define rays. -/
theorem point_in_carrier_defines_ray (c : Cone 𝕜 V P) (hpc : p ∈ c.carrier) (hpv : p ≠ c.vertex) :
    c.ray_to hpv ∈ c.rays := by
  rcases c.point_in_carrier_on_lineMap hpc hpv with ⟨b, ⟨k, ⟨h0k, ⟨_, hlkp⟩⟩⟩⟩
  have hrr : c.ray_to hpv = c.ray_to (c.lineMap_k_neq_vertex b.property h0k) := by
    unfold ray_to; unfold vector_to; dsimp [lineMap, AffineMap.lineMap]; simp
    dsimp [lineMap, AffineMap.lineMap] at hlkp
    have x := congr_arg (fun q => q -ᵥ c.vertex) hlkp; simp at x
    rw [ray_eq_iff, x]
  rw [hrr, c.point_on_lineMap_same_ray_as_base_point b.property h0k]
  exact c.base_point_ray_in_rays' b.property

end Cone

end «Cone rays»

-- ********************************************************************
section «Cone tangent space»

/-!
## The tangent space and the affine subspaces defined by cones

 -/

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Cone

/-- This is the module subspace generated by a cone. -/
def tangent_space (c : Cone 𝕜 V P) : Submodule 𝕜 V := Submodule.span 𝕜 c.base_vectors

/-- This is the affine subspace generated by a cone. -/
def affine_subspace (c : Cone 𝕜 V P) : AffineSubspace 𝕜 P := AffineSubspace.mk' c.vertex c.tangent_space

/-- This shows that for a given base-point the vector from the vertex to the
base-point is in the spanned module subspace. -/
def base_direcion_in_spanned_module_subspace (c : Cone 𝕜 V P) (b : c.base) : c.vector_to b ∈ c.tangent_space := by
  simp only [tangent_space]
  have h : ↑b -ᵥ c.vertex ∈ c.base -ᵥ { c.vertex } := by
    simp only [Set.mem_vsub, Set.mem_def.mp]; use ↑b; apply And.intro b.property; use c.vertex; exact ⟨Set.mem_singleton c.vertex, rfl⟩
  exact Submodule.subset_span h
  done

/-- The carrier is in the spanned affine subspace. -/
def carrier_subset_of_affine_subspace (c : Cone 𝕜 V P) : c.carrier ⊆ c.affine_subspace := by
  admit

/-- The spanned module subspace is the least subspace in the module that contains all base-vectors. -/
def tangent_space_least_subspace (c : Cone 𝕜 V P) (sm : Submodule 𝕜 V) :
    c.tangent_space ≤ sm ↔ c.base_vectors ⊆ sm := by
  --Submodule.span_le
  admit

/-- The spanned affine subspace is the least subspace in the affine space that contains all base-points. -/
def affine_subspace_least_subspace (c : Cone 𝕜 V P) (as : AffineSubspace 𝕜 P) :
    c.affine_subspace ≤ as ↔ c.carrier ⊆ as := by
  -- affineSpan_le
  admit

end Cone

end «Cone tangent space»

-- ********************************************************************
section «Join under affine maps»

/-!
## Joins and cones under affine maps

This section shows how joins behave under affine maps. Joins have benign
behaviour when mapped affinely: The image is again a join. -/

variable {𝕜 : Type u} [OrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {W : Type v} [AddCommGroup W] [Module 𝕜 W] [NoZeroSMulDivisors 𝕜 W]
variable {Q : Type w} [AddTorsor W Q]

/-- This defines how a join is mapped under affine maps. We first define the join that results
from the map. Later, we show that this is the same as applying the affine map to the join as a set. -/
def Join.map_affine (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) : Join 𝕜 W Q where
  side0 := m '' j.side0
  side1 := m '' j.side1

/-- This proves that the carrier of the result of `Join.map_affine` is indeed
the image of the join under the affine map . -/
theorem Join.map_affine_image_eq_image_under_affine_map
  (j : Join 𝕜 V P) (m : P →ᵃ[𝕜] Q) : m '' j = j.map_affine m := by
  funext q
  --have hcarrierR := (carrier_def (j.map_affine m) q)
  simp only [carrier]
  conv => lhs; simp only [Set.image_union]
  conv => rhs; pattern ((map_affine j m).side0); simp only [map_affine]
  conv => rhs; pattern ((map_affine j m).side1); simp only [map_affine]
  suffices hmseg : ⇑m '' segment_elements j = segment_elements (map_affine j m) by
    conv => rhs; rw [← hmseg]
  simp only [map_affine, segment_elements]
  conv => rhs; simp only [Set.exists_mem_image]
  conv => lhs; simp only [Set.image, Set.mem_def]
  ext q; simp only [Set.mem_setOf]
  apply Iff.intro
  . intro h
    rcases h with ⟨p, ⟨⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, ⟨k, ⟨hk, haff'⟩⟩⟩⟩⟩⟩, hpmq⟩⟩
    have haff := congrArg m haff'; rw [AffineMap.apply_lineMap, hpmq] at haff
    exact ⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, ⟨k, ⟨hk, haff⟩⟩⟩⟩⟩⟩
  . intro h
    rcases h with ⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, ⟨k, ⟨hk, haff⟩⟩⟩⟩⟩⟩
    let p := AffineMap.lineMap p0 p1 k; have hp : AffineMap.lineMap p0 p1 k = p := by rfl
    rw [← AffineMap.apply_lineMap, hp] at haff
    exact ⟨p, ⟨⟨p0, ⟨hp0s0, ⟨p1, ⟨hp1s1, ⟨k, ⟨hk, hp⟩⟩⟩⟩⟩⟩, haff⟩⟩
  done

end «Join under affine maps»

/-! This section shows how cones behave under affine maps. Cones map to cones
when the affine map is injective on the linear subspace generated by the cone. -/

section «Cone under affine maps»

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {W : Type v} [AddCommGroup W] [Module 𝕜 W] [NoZeroSMulDivisors 𝕜 W]
variable {Q : Type w} [AddTorsor W Q]

namespace Cone

/-- Cones map to cones under injective affine transformations. -/
def map_affine_injective (c : Cone 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) : Cone 𝕜 W Q where
  vertex := m c.vertex
  base := m '' (c.base)
  vertex_not_in_base' := by
    rintro ⟨b, ⟨hbb, hbmv⟩⟩
    absurd (c.base_point_neq_vertex hbb).symm
    rw [←vsub_eq_zero_iff_eq, (AffineMap.linearMap_vsub m b c.vertex).symm, LinearMap.map_eq_zero_iff, vsub_eq_zero_iff_eq] at hbmv
    exact hbmv.symm
    exact (AffineMap.linear_injective_iff m).mpr hmi
  unique_rays' := by
    rintro q1 q2 hq1 hq2
    simp only [Set.image] at hq1; rcases hq1 with ⟨b1, ⟨hb1, hb1mq1⟩⟩
    simp only [Set.image] at hq2; rcases hq2 with ⟨b2, ⟨hb2, hb2mq2⟩⟩
    simp only [Subtype.mk_eq_mk, ←hb1mq1, ←hb2mq2]
    rw [(AffineMap.linearMap_vsub m b1 c.vertex).symm]
    rw [(AffineMap.linearMap_vsub m b2 c.vertex).symm]
    rw [hmi.eq_iff, ((AffineMap.linear_injective_iff m).mpr hmi).sameRay_map_iff]
    exact c.unique_rays hb1 hb2
    done

/-- This proves that an affine map on a cone yields the same join as the action of
an affine map of the join represented by the cone. -/
theorem map_affine_injective_eq_to_join_affine_map
  (c : Cone 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) : (c.map_affine_injective m hmi).to_join = c.to_join.map_affine m := by
  simp only [map_affine_injective, Join.map_affine, to_join, Set.image_singleton]

/-- This proves that the carrier of the result of `Cone.map_affine_injective` is indeed
the image of the cone under the affine map . -/
theorem map_affine_injective_image_eq_image_under_affine_map
  (c : Cone 𝕜 V P) (m : P →ᵃ[𝕜] Q) (hmi : Function.Injective m) : c.map_affine_injective m hmi = m '' c := by
  simp only [map_affine_injective_eq_to_join_affine_map, Join.map_affine_image_eq_image_under_affine_map]

end Cone

end «Cone under affine maps»

-- ********************************************************************
section «Cone scaling»

/-!
## Scaling of cones

Cones can be rescaled from the vertex.
-/

variable {𝕜 : Type u} [StrictOrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- Hhomotheties are injective. -/
theorem AffineMap.homothety_injective (p : P) (k : 𝕜) (hk : k ≠ (0:𝕜)) :
  Function.Injective (AffineMap.homothety p k) := by
  unfold AffineMap.homothety
  intro p1 p2 h; dsimp at h
  exact vsub_left_cancel <| smul_right_injective V hk <| vadd_right_cancel p h
  done

namespace Cone

/-- This applies a homothety (dilation) at the vertex to the given cone. For the definition
of homothety, see `AffineMap.homothety`. This function defines the resulting cone. -/
def dilate_at_vertex (c : Cone 𝕜 V P) (k : 𝕜) (hk : 0 < k) : Cone 𝕜 V P :=
  c.map_affine_injective (AffineMap.homothety c.vertex k) (AffineMap.homothety_injective c.vertex k (ne_of_gt hk))

/-- This proves that image of thge carrier of a cone under rescaling is the carrier of the
rescaled cone. -/
theorem dilate_at_vertex_carrier_eq_image_carrier_under_dilation (c : Cone 𝕜 V P) (k : 𝕜) (hk : 0 < k) :
    c.dilate_at_vertex k hk = (AffineMap.homothety c.vertex k) '' c.carrier := by
  unfold dilate_at_vertex
  exact c.map_affine_injective_image_eq_image_under_affine_map (AffineMap.homothety c.vertex k) (AffineMap.homothety_injective c.vertex k (ne_of_gt hk))

end Cone

end «Cone scaling»

-- ********************************************************************
--#lint
