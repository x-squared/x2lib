/-
Copyright (c) 2024 Stephan maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/

import Mathlib.Init.Function
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.AddTorsor
import Mathlib.Algebra.Module.Basic
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
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import X2lib.Topology.PiecewiseLinear.Join
import X2lib.Topology.PiecewiseLinear.Affine
import X2lib.Topology.PiecewiseLinear.Module

/-!
# Foos and bars

In this file we introduce `foo` and `bar`,
two main concepts in the theory of xyzzyology.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.
- `bar_of_foo`: a construction of a `bar`, given a `foo`.
- `bar_eq`    : the main classification theorem of `bar`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Thales600BC] for the original account on Xyzzyology.
-/

universe u v w
open Set
open Filter
open Topology

-- For later ********************************************************************

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html#IsDomain

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/Basic.html#OrderTopology

-- ********************************************************************
/-!
This is a section of miscellaneous results that could not be located
elsewhere but which should, ideally, come straight from the main library.
This is not an official section and does not appear in the piublished API.
All theorems are declared private to make them invisible outside this file.
-/

/-- A point that is not open has arbitrarily close neighbours. -/
private theorem non_open_point_has_close_neighbours [TopologicalSpace X] (x : X) (hnox: ¬ IsOpen {x}) (hn : n ∈ 𝓝 x) :
    ∃ y, y ∈ n ∧ y ≠ x := by
  rcases mem_nhds_iff.mp hn with ⟨s, ⟨hssubn, ⟨hsopen, hxins⟩⟩⟩
  rw [←dense_compl_singleton_iff_not_open] at hnox
  rcases (Dense.exists_mem_open hnox hsopen $ nonempty_of_mem hxins) with ⟨y, ⟨hyincx, hyins⟩⟩
  use y; exact ⟨mem_of_mem_of_subset hyins hssubn, mem_compl_singleton_iff.mp hyincx⟩
  done

/-- Topological add-groups whose topology is not discrete have non-zero points arbitrarily close to `0`. -/
private theorem AddGroup.exists_elements_close_to_zero {G : Type u}
    [TopologicalSpace G] [AddGroup G] [ContinuousAdd G] (ndtR : ¬ DiscreteTopology G)
    {n : Set G} (hn : n ∈ 𝓝 (0 : G)) : ∃ y ∈ n, y ≠ 0 := by
  have hno0 : ¬ IsOpen { (0:G) } := (not_iff_not.mpr discreteTopology_iff_isOpen_singleton_zero).mp ndtR
  exact non_open_point_has_close_neighbours (0:G) hno0 hn

/-- We need this auxiliary result to handle the problem of type-class resolution in the application
below. -/
private def add_group_of_ring (hr : Ring R) : AddGroup R := by
  have h1 := hr.toAddCommGroup; exact h1.toAddGroup

/-- Topological rîngs whose topology is not discrete have non-zero points
arbitrarily close to `0`. -/
private theorem Ring.exists_elements_close_to_zero' {R : Type u}
    [ringR : Ring R] [topR : TopologicalSpace R] [topRingR : TopologicalRing R]
    (ndtR : ¬ DiscreteTopology R)
    (n : Set R) (hn : n ∈ 𝓝 (0 : R)) : ∃ y ∈ n, y ≠ 0 := by
  exact @AddGroup.exists_elements_close_to_zero _ _ (add_group_of_ring ringR) topRingR.toContinuousAdd ndtR n hn

/-- Linearly ordered topological rîngs whose topology is not discrete have
non-zero points arbitrarily close to `0`. -/
private theorem Ring.exists_elements_close_to_zero'' {R : Type u}
    [LinearOrderedCommRing R] [TopologicalSpace R] [TopologicalRing R] [OrderClosedTopology R]
    (ndtR : ¬ DiscreteTopology R)
    {ε : R} (he : 0 < ε) : ∃ r : R, 0 < r ∧ r < ε := by
  let o := Set.Ioo (-ε : R) ε
  have hon : o ∈ 𝓝 (0 : R) := Ioo_mem_nhds (neg_neg_iff_pos.mpr he) he
  rcases Ring.exists_elements_close_to_zero' ndtR o hon with ⟨r', ⟨hr', r'neq0⟩⟩
  let r := abs r'; use r
  exact ⟨abs_pos.mpr r'neq0, abs_lt.mpr (Set.mem_Ioo.mp hr')⟩
  done

/-- Linearly ordered topological rîngs whose topology is not discrete have
non-zero points arbitrarily close to `0`. -/
private theorem Ring.exists_elements_close_to_zero {R : Type u}
    [LinearOrderedCommRing R] [TopologicalSpace R] [TopologicalRing R] [OrderTopology R]
    (ndtR : ¬ DiscreteTopology R) (n : Set R) (hn : n ∈ 𝓝 (0 : R)) :
    ∃ r ∈ n, 0 < r := by
  rcases mem_nhds_iff_exists_Ioo_subset.mp hn with ⟨a, ⟨b, ⟨ha0b, hon⟩⟩⟩
  let ε := min (-a) b
  have h0ε : 0 < ε := lt_min (neg_pos_of_neg (Set.mem_Ioo.mp ha0b).1) (Set.mem_Ioo.mp ha0b).2
  let o := Set.Ioo (-ε : R) ε
  have hoab : o ⊆ Ioo a b := by
    have ha : a ≤ -ε := by
      simp only [ε]; conv => lhs; rw [← neg_neg a]
      exact neg_le_neg_iff.mpr (min_le_left (-a) b)
    have hb : ε ≤ b := min_le_right (-a) b
    exact Set.Ioo_subset_Ioo ha hb
  have hon : o ⊆ n := subset_trans hoab hon
  have honhd : o ∈ 𝓝 (0 : R) := Ioo_mem_nhds (neg_neg_iff_pos.mpr h0ε) h0ε
  rcases Ring.exists_elements_close_to_zero' ndtR o honhd with ⟨r', ⟨hr', r'neq0⟩⟩
  let r := abs r'; use r
  have h0r : 0 < r := abs_pos.mpr r'neq0
  have hrn : r ∈ n := by
    have h1 : -ε < r := lt_of_lt_of_le (neg_neg_of_pos h0ε) (abs_nonneg r')
    have h2 : r < ε := abs_lt.mpr $ Set.mem_Ioo.mp hr'
    have hro : r ∈ o := Set.mem_Ioo.mpr ⟨h1, h2⟩
    exact Set.mem_of_mem_of_subset hro hon
  exact ⟨hrn, h0r⟩
  done

/-- Linearly ordered topological rîngs whose topology is not discrete have
non-zero points arbitrarily close to `0`. -/
private theorem Ring.exists_elements_close_to_zero_for_map
    {X : Type v} [TopologicalSpace X]
    {R : Type u} [LinearOrderedCommRing R] [TopologicalSpace R] [TopologicalRing R] [OrderTopology R] (ndtR : ¬ DiscreteTopology R)
    (f : R → X) (hc0f : ContinuousAt f (0:R)) (ε : R) (hε : 0 < ε) (nx : Set X) (hnx : nx ∈ 𝓝 (f 0)) :
    ∃ r : R, 0 < r ∧ r < ε ∧ f r ∈ nx := by

  admit

/- The theorem `ContinuousAt.preimage_mem_nhds` does not apply to relative topologies.
We provide a version that does and suits our needs. It is not the most general theorem. -/
-- private theorem ContinuousAt.preimage_mem_nhds_within {X : Type u} {Y : Type v}
--     [TopologicalSpace X] [TopologicalSpace Y]
--     {f : X → Y} {x : X} {sx : Set X} {hx : x ∈ sx} {sy : Set Y} {n : Set Y} (hi : f '' sx ⊆ sy) (hcfx : ContinuousAt f x)
--     (hn : n ∈ 𝓝[sy] (f x)) : f ⁻¹' n ∈ 𝓝 x := by
--   rcases mem_nhdsWithin.mp hn with ⟨o, ⟨ho, ⟨hfxin0, hoisn⟩⟩⟩; rw [inter_comm] at hoisn
--   have h1 := ContinuousAt.preimage_mem_nhds hcfx (IsOpen.mem_nhds ho hfxin0)
--   have h2 : f ⁻¹' (sy ∩ o) ⊆ f ⁻¹' n := preimage_mono hoisn
--   have h3 : f ⁻¹' (sy ∩ o) = f ⁻¹' o := by
--     rw [preimage_inter, preimage_eq_univ_iff.mpr, univ_inter]
--     exact hi
--   rw [h3] at h2
--   exact Filter.mem_of_superset h1 h2
--   done

-- ********************************************************************
section «Cone neighbourhood»

/-!
### Cone neighbourhoods

The topology of polytopes is given by neighbourhood-filters that
are generated by cones. This section defines these cone-neighbourhoods
via the structure `ConeNhd`.

`ConeNhd`s are sometimes called 'star' (sugesting that the cone fills the
available space), and `Cone.base` is then called 'link'. We do not use this
terminology in order not to introduce yet another term. -/

variable (𝕜 : Type u) [LinearOrderedCommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] [OrderClosedTopology 𝕜]
variable (V : Type v) [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V]
variable (P : Type w) [AddTorsor V P] [TopologicalSpace P] [TopologicalAddTorsor V P]

/-- A cone-neighbourhood is a cone which is contained in a given set `s`
where the base is a closed set and the cone is a neighbourhood in the
relative topology.-/
structure ConeNhd (s : Set P) extends Cone 𝕜 V P where
/-- The carrier is in the set `s`. -/
  subset_set : carrier ⊆ s
  /-- The cone's carrier is a neighbourhood in the induced toplogy on `s`. -/
  is_nhd : carrier ∈ 𝓝[s] vertex
  /-- The base must be a closed set in the ambient affine space. -/
  base_closed : IsClosed base

/-- This allows us to view a `ConeNhd` as a `Cone`.-/
instance : CoeSort (ConeNhd 𝕜 V P s) (Cone 𝕜 V P) where
  coe c := c.toCone

end «Cone neighbourhood»

-- ********************************************************************
section «Cone neighbourhood basics»

/-!
### Cone neighbourhoods basics

TODO.  -/

variable {𝕜 : Type u} [LinearOrderedCommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] [OrderTopology 𝕜] (ndtR : ¬ DiscreteTopology 𝕜)
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P] [topologyP : TopologicalSpace P] [TopologicalAddTorsor V P]

namespace ConeNhd

/-- The vertex of the cone is in `s`. -/
theorem vertex_in_set (cn : ConeNhd 𝕜 V P s) : cn.vertex ∈ s :=
  cn.subset_set cn.vertex_in_carrier

/-- For convenience we provide this defintion which is an alternative
way of stating that a cone-neighbourood is a neighbourhood in the
relative topology. -/
theorem is_rel_nhd (cn : ConeNhd 𝕜 V P s) : ∃ u ∈ 𝓝 cn.vertex, u ∩ s ⊆ cn.carrier :=
  mem_nhdsWithin_iff_exists_mem_nhds_inter.mp cn.is_nhd

/- For convenience, we note that the segment-line-map is continuous. -/
@[continuity] theorem lineMap_continuous (cn : ConeNhd 𝕜 V P s) (hb : b ∈ cn.base) :
    Continuous $ cn.lineMap hb := Affine.lineMap_continuous

/-- Auxiliary result to prove the theorem `cone_nhds_have_same_rays`. -/
private theorem cone_nhds_have_subset_rays (nhd1 : ConeNhd 𝕜 V P s) (nhd2 : ConeNhd 𝕜 V P s) (heqv : nhd1.vertex = nhd2.vertex) :
    nhd1.rays ⊆ nhd2.rays := by
  -- Start with a ray of the first cone-neighbourghood
  intro r1 hr1
  simp only [Cone.rays, Set.mem_setOf] at hr1
  rcases hr1 with ⟨b1, h_rb1_eq_r1⟩
  -- Get a line segment for the ray
  let f : 𝕜 →ᵃ[𝕜] P := nhd1.lineMap b1.property
  have hfc0 : ContinuousAt f (0:𝕜) := Continuous.continuousAt Affine.lineMap_continuous
  have hf0v : f (0:𝕜) = nhd2.vertex := by simp only [←heqv, f, Cone.lineMap, AffineMap.lineMap_apply_zero]
  -- Find a point along the line that lies in the second cone neighbourhood
  rcases nhd2.is_rel_nhd with ⟨u, ⟨hunhd, hunhd2⟩⟩
  rw [←hf0v] at hunhd
  rcases Ring.exists_elements_close_to_zero_for_map ndtR f hfc0 1 zero_lt_one u hunhd with ⟨k, ⟨h0k, ⟨hk1, hfku⟩⟩⟩
  have hkIoo : k ∈ Ioo (0:𝕜) 1 := Set.mem_Ioo.mpr ⟨h0k, hk1⟩
  have hkIcc : k ∈ Icc (0:𝕜) 1 := Set.Ioo_subset_Icc_self hkIoo
  -- The point is found, now show it lies in the right sets
  have hfknhd1 : f k ∈ nhd1.carrier := nhd1.lineMap_maps_to_carrier b1.property hkIcc
  have h_fk_neq_v1 : f k ≠ nhd1.vertex := nhd1.lineMap_k_neq_vertex b1.property h0k
  have hfks : f k ∈ s := nhd1.subset_set hfknhd1
  have hfknhd2 : f k ∈ nhd2.carrier := mem_of_mem_of_subset (mem_inter hfku hfks) hunhd2
  have h_fk_neq_v2 : f k ≠ nhd2.vertex := by rw [←heqv]; exact h_fk_neq_v1
  -- Now argue with rays
  have h_rfk_eq_rb1 := nhd1.point_on_lineMap_same_ray_as_base_point b1.property h0k
  have h_r1_eq_rfk := Eq.trans h_rb1_eq_r1.symm h_rfk_eq_rb1.symm
  have h_rfk_nhd1_nhd2 := nhd1.ray_to_independent_of_cone nhd2 heqv h_fk_neq_v1
  let r2 := nhd2.ray_to h_fk_neq_v2
  have hr2inr2 := nhd2.point_in_carrier_defines_ray hfknhd2 h_fk_neq_v2
  admit

/-- Two cone-neighbourhoods centred on the same vertex have identical rays. -/
theorem cone_nhds_have_same_rays (nhd1 : ConeNhd 𝕜 V P s) (nhd2 : ConeNhd 𝕜 V P s) (heqv : nhd1.vertex = nhd2.vertex) :
    nhd1.rays = nhd2.rays :=
  Set.eq_of_subset_of_subset (cone_nhds_have_subset_rays ndtR nhd1 nhd2 heqv) (cone_nhds_have_subset_rays ndtR nhd2 nhd1 heqv.symm)

/--
TODO Define the interior of ConeNhd. -/
example : 1=1 := rfl

/--
TODO The interior of ConeNhd is an open set in the relative topology. -/
example : 1=1 := rfl

/--
TODO Define the tangent-rays of a ConeNhd and show that this is a closed set. -/
example : 1=1 := rfl

/--
TODO Define the tangent-space of a ConeNhd and show that this is a closed set. -/
example : 1=1 := rfl

/--
TODO Can we show some upper semicontiuity for the tangent space? -/
example : 1=1 := rfl

end ConeNhd

end «Cone neighbourhood basics»

-- ********************************************************************
section «Geometric polyhedron»

/-!
### Geometric polyhedra

A polyhedral set is a subset of an affine space where each point has a cone-neighbourhood.
A geometric polyhdron is such a set where the closure also is a geometric polyhdron.
Distinguishing polyhedral sets and geometric polyhdra helps to avoid pathological
sets when handling geometric polyhdra.

We choose the prefix `Geom` to indicate that geometric polyhedra always are subsets
of an ambient affine space. This leaves room for a notion of polyhedron as a set
which locally looks like a geometric polyhedron. This point of view is developed
later. -/

variable (𝕜 : Type u) [LinearOrderedCommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] {ndtR : ¬ DiscreteTopology 𝕜}
variable (V : Type v) [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V]
variable (P : Type w) [AddTorsor V P] [TopologicalSpace P] [TopologicalAddTorsor V P]


/-- This defines what it means for a set to carry a polyhedral topology. This means that
the topology generated by the con-neighbourhoods is iqual to the induced topology of the
set. -/
class PolyhedralSet (s : Set P) : Prop where
  /-- Each point has a cone-neighbourhood. -/
  points_have_cone_nhds (_ : p ∈ s) : ∃ cn : ConeNhd 𝕜 V P s, cn.vertex = p
  /-- Every neighbourhood of a point in the polytope contains a cone-neighbourhood. -/
  nhd_contains_cone_nhd (_ : p ∈ s) (_ : n ∈ 𝓝[carrier] p) : ∃ cn : ConeNhd 𝕜 V P s, ↑cn ⊆ n

/-- A geometric polyhedron is a set in an ambient affine space such that.... -/
class GeomPolyhedron (s : Set P) extends PolyhedralSet 𝕜 V P s : Prop where
  /-- The carrier is closed in the ambient space. -/
  is_closed : IsClosed s
/- The ray-set must be a closed set. -/  --ray_set_closed (_ : p ∈ s) : IsClosed (???)
/- Check if we need upper semicontinuityfor the tangent affine space -/

/-- In order to be able to define interesting geometric polyhedra we must work in
ambient affine spaces that already carry the structure of geometric ployhedra.
A polyhedral space is an affine space that in it entirety is a geometric polyhedron. -/
class PolyhedralSpace : Prop where
  /-- The entire set of the type is a geometric polyhedron. -/
  univ_is_polyhedron : GeomPolyhedron 𝕜 V P (Set.univ : Set P)

end «Geometric polyhedron»

-- ********************************************************************
section «Geometric polyhedra basics»

/-!
### Basics of geometric polyhedra

TODO.  -/

variable {𝕜 : Type u} [LinearOrderedCommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] {ndtR : ¬ DiscreteTopology 𝕜}
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V]
variable {P : Type w} [AddTorsor V P] [topologyP : TopologicalSpace P] [TopologicalAddTorsor V P]

namespace PolyhedralSet

/-- The carrier of a polyhedral space is the set for which it is defined. -/
def carrier (_ : PolyhedralSet 𝕜 V P s) : Set P := s

/-- This allows us to view a `PolyhedralSet` as a `Set P`.-/
instance CoeSort_to_Set : CoeSort (PolyhedralSet 𝕜 V P s) (Set P) where
  coe := carrier

/-- Polyhedral sets will always carry the induced topology. -/
instance topologicalSpace (gp : PolyhedralSet 𝕜 V P s) : TopologicalSpace gp.carrier :=
  TopologicalSpace.induced (Subtype.val : gp.carrier → P) topologyP

end PolyhedralSet

namespace GeomPolyhedron

/-- The carrier of a geometric polyhedron is the set for which it is defined. -/
def carrier (_ : GeomPolyhedron 𝕜 V P s) : Set P := s

/-- This allows us to view a `GeomPolyhedron` as a `Set P`.-/
instance CoeSort_to_Set : CoeSort (GeomPolyhedron 𝕜 V P s) (Set P) where
  coe := carrier

/-- Every polyhedron is a polyhedral set. -/
instance CoeSort_to_PolyhedralSet : CoeSort (GeomPolyhedron 𝕜 V P s) (PolyhedralSet 𝕜 V P s) where
  coe gp := gp.toPolyhedralSet

/-- Every `PolyhedralSet` that is closed is a `GeomPolyhedron`.-/
def closed_polyhedralset_to_GeomPolyhedron (ps : PolyhedralSet 𝕜 V P s) (hic : IsClosed s) :
    GeomPolyhedron 𝕜 V P s where
  points_have_cone_nhds := ps.points_have_cone_nhds
  nhd_contains_cone_nhd := ps.nhd_contains_cone_nhd
  is_closed := hic

/-- This allows us to view a polyhedral set as a `GeomPolyhedron`.
TODO still true  if we require more of a polyhedron? -/
instance CoeSort_ClosedPolyhedralSet_to_GeomPolyhedron {s : Set P} (hic : IsClosed s) :
    CoeSort (PolyhedralSet 𝕜 V P s) (GeomPolyhedron 𝕜 V P s) where
  coe ps := closed_polyhedralset_to_GeomPolyhedron ps hic

/-- This allows us to view the universal set of an affine space that is itself a `PolyhedralSpace`
as a `GeomPolyhedron`.-/
instance CoeSort_univ_to_GeomPolyhedron : CoeSort (PolyhedralSpace 𝕜 V P) (GeomPolyhedron 𝕜 V P (Set.univ : Set P)) where
  coe ps := ps.univ_is_polyhedral_set

/-- Geometric polyhedra will always carry the induced topology. -/
instance topologicalSpace (gp : GeomPolyhedron 𝕜 V P s) : TopologicalSpace gp.carrier :=
  TopologicalSpace.induced (Subtype.val : gp.carrier → P) topologyP

/--
TODO Define tangent-rays and show closed -/
example : 1=1 := rfl

/--
TODO Define tangent space  amnd show closed -/
example : 1=1 := rfl

end GeomPolyhedron

end «Geometric polyhedra basics»

-- ********************************************************************
section «Basic examples: Affine spaces that are polyhedra»

/-!
### Affine spaces that are pohyedra

In this section we provide the elementary examples of affine spaces that
are naturally polyhedral sets and thus polyhedra.
TODO Make bullet list for navigation.  -/

variable {𝕜 : Type u} [LinearOrderedCommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] {ndtR : ¬ DiscreteTopology 𝕜}
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V]
variable {P : Type w} [AddTorsor V P] [topologyP : TopologicalSpace P] [TopologicalAddTorsor V P]
variable [instPolyhedralSpace: PolyhedralSpace 𝕜 V P]

namespace GeomPolyhedron

/--
TODO Normed spaces -/
example : 1=1 := rfl

/--
TODO real space -/
example : 1=1 := rfl

end GeomPolyhedron

end «Basic examples: Affine spaces that are polyhedra»

-- ********************************************************************
section «Basic examples: Polyhedral sets from other polyhedral sets»

/-!
### Basic examples: Getting polyhedral sets from given polyhedral sets

TODO.  -/

variable {𝕜 : Type u} [LinearOrderedCommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] {ndtR : ¬ DiscreteTopology 𝕜}
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V]
variable {P : Type w} [AddTorsor V P] [topologyP : TopologicalSpace P] [TopologicalAddTorsor V P]
variable [instPolyhedralSpace: PolyhedralSpace 𝕜 V P]

namespace GeomPolyhedron

/-- If the ambient affine space is polyhedral the the entire ambient space is a geometric polyhedron.
This is a triviality, but it needs being stated. -/
theorem polyhedral_space_is_geometric_polyhedron : GeomPolyhedron 𝕜 V P (Set.univ : Set P) :=
  instPolyhedralSpace

/-- Open subsets of geometric polyhedra are geometric polyhedra. -/
theorem open_subsets_of_of_polyhedral_sets_are_polyhedral_sets (gp : GeomPolyhedron 𝕜 V P s)
    (hs : s ⊆ gp.carrier) (hso : IsOpen s) : GeomPolyhedron 𝕜 V P s := by
  admit

end GeomPolyhedron

end «Basic examples: Polyhedral sets from other polyhedral sets»

-- ********************************************************************
section «Basic examples: Geometric polyhedra from polyhedral sets»

/-!
### Basic examples: Getting geometric polyhedra from given polyhedral sets

TODO.  -/

variable {𝕜 : Type u} [LinearOrderedCommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] {ndtR : ¬ DiscreteTopology 𝕜}
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [TopologicalAddGroup V] [ContinuousSMul 𝕜 V]
variable {P : Type w} [AddTorsor V P] [topologyP : TopologicalSpace P] [TopologicalAddTorsor V P]
variable [instPolyhedralSpace: PolyhedralSpace 𝕜 V P]

namespace GeomPolyhedron



end GeomPolyhedron

end «Basic examples: Geometric polyhedra from polyhedral sets»

/--
The obvious triangle induced by `QuotientMap.lift` commutes:
```
     g
  X --→ Z
  |   ↗
f |  / hf.lift g h
  v /
  Y
```
-/
example : 1 = 1
