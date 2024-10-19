/-
Copyright (c) 2024 Stephan maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib

/-!
# Auxiliary results for affine spaces

This file extends contains auxiliary results for affine spaces.

-/

universe u v w u' v' w'

-- ********************************************************************
section «Auxiliary Set results»

variable {𝕜 : Type u} [OrderedCommRing 𝕜]

@[simp] theorem Set.Ioo_gt_left (hk : k ∈ Set.Ioo (0:𝕜) 1) : 0 < k := by
  exact (Set.mem_Ioo.mp hk).left

@[simp] theorem Set.Ioo_neq_0 (hk : k ∈ Set.Ioo (0:𝕜) 1) : k ≠ 0 := by
  exact ne_of_gt (Set.mem_Ioo.mp hk).left

end «Auxiliary Set results»

-- ********************************************************************
section «Affine line map»

/-! TODO -/

section «Ring»

variable {𝕜 : Type u} [CommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace AffineMap

variable {V' : Type v} [AddCommGroup V'] [Module 𝕜 V']
variable {P' : Type w} [AddTorsor V' P']

/-- The image of a set in the ground ring under both an affine map and
a line map is the image of the line map defined on the image of the
defining points of the line map. -/
theorem image_map_lineMap {p₀ p₁ : P} {s : Set 𝕜} (f : P →ᵃ[𝕜] P'):
    f '' (AffineMap.lineMap p₀ p₁ '' s) = (AffineMap.lineMap (f p₀) (f p₁) '' s) := by
  ext p; constructor
  · rintro ⟨q, ⟨⟨k, ⟨hks, hlmkq⟩⟩, hfqp⟩⟩
    have hlmkq := congr_arg f hlmkq; rw [AffineMap.apply_lineMap, hfqp] at hlmkq
    exact ⟨k, ⟨hks, hlmkq⟩⟩
  · rintro ⟨k, ⟨hks, hlmkp⟩⟩
    rw [←AffineMap.apply_lineMap] at hlmkp
    use (lineMap p₀ p₁) k
    exact ⟨Set.mem_image_of_mem (lineMap p₀ p₁) hks, hlmkp⟩

/-- Homotheties fix their base point. -/
def homothety_fixes_vertex  (p : P) (k : 𝕜) :
    (AffineMap.homothety p k) p = p := by simp

end AffineMap

end «Ring»

section «Field»

variable {𝕜 : Type u} [Field 𝕜] [TopologicalSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace AffineMap

/-- . -/
private theorem lineMap_proportionate_end_points (a b b' : P) {k k' : 𝕜} (h : (AffineMap.lineMap a b) k = (AffineMap.lineMap a b') k') :
    lineMap a b (k'⁻¹ * k) = b' ∧ lineMap a b' (k⁻¹ * k') = b := by

  admit

end AffineMap

end «Field»

end «Affine line map»

-- ********************************************************************
section «Affine segments»

variable (𝕜 : Type u) [OrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-!
## Affine segments

This section defines segments between points in affine space as the the
most basic building block for PL-topology. Given two points in an affine
space, the sets `segmentCC`, `segmentOC` and `segmentOO` are the line
segments between these points, including or excluding the points themselves.
The definition mirrors the definition of `Set.Icc`, `Set.Ioc` and `Set.Ioo`.
These definitions are provided for better readability of the theorems
on joins and cones.

Note: Mathlib provides `affineSegment`. This notion seems to be mainly
geared for use in comparing position of points (in-between-ness). For PL-topology
we are interested in the sets themselves, not the relation of in-between-ness.
For this reason, we define an adapted notion of `affineSegment` bypassing
the definitions in `Mathlib.Analysis.Convex.Between`. Also, the Mathlib section
on convex sets contains a defintion of (open and) closed segements, none
of which serves the purpose of PL-topology.
 -/

namespace Affine

/-- The segment between two points including both end-points. This is
the image of `Set.Icc` under the linemap given by the two points -/
def segmentCC (a b : P) : Set P := AffineMap.lineMap a b '' Set.Icc (0:𝕜) 1

/-- The segment between two points excluding the start-point but
including the end-point. This is the image of `Set.Ioc` under the linemap
given by the two points -/
def segmentOC (a b : P) : Set P := AffineMap.lineMap a b '' Set.Ioc (0:𝕜) 1

/-- The segment between two points excluding both end-points. This is
the image of `Set.Ioo` under the linemap given by the two points -/
def segmentOO (a b : P) : Set P := AffineMap.lineMap a b '' Set.Ioo (0:𝕜) 1

/-- The segment starting at a pointand extending through a second point
to (right) infinity. This is the image of `Set.Ioi` under the line map
given by the two points -/
def segmentOI (a b : P) : Set P := AffineMap.lineMap a b '' Set.Ioi (0:𝕜)

/-- `segmentCC` is `segmentOC` with start-point added. -/
theorem segmentCC_eq_segmentOC_union_startpoint (a b : P) :
    segmentCC 𝕜 a b = {a} ∪ segmentOC 𝕜 a b := by
  dsimp only [segmentCC]
  have : Set.Icc (0:𝕜) 1 = {(0:𝕜)} ∪ Set.Ioc (0:𝕜) 1 := by simp
  rw [this, Set.image_union, Set.image_singleton]
  have : AffineMap.lineMap a b (0:𝕜) = a := AffineMap.lineMap_apply_zero a b
  rw [this, segmentOC]

/-- `segmentOC` is `segmentOO` with end-point added. -/
theorem segmentOC_is_segmentOO_union_endpoint (a b : P) :
    segmentOC 𝕜 a b = segmentOO 𝕜 a b ∪ { b } := by
  dsimp only [segmentOC]
  have : Set.Ioc (0:𝕜) 1 = Set.Ioo (0:𝕜) 1 ∪ {(1:𝕜)} := by admit
  rw [this, Set.image_union, Set.image_singleton]
  have : AffineMap.lineMap a b (1:𝕜) = b := AffineMap.lineMap_apply_one a b
  rw [this, segmentOO]

/-- `segmentCC` is `segmentOO` with end-points added. -/
theorem segmentCC_eq_segmentOO_union_endpoints (a b : P) :
    segmentCC 𝕜 a b = {a} ∪ segmentOO 𝕜 a b ∪ { b } := by
  rw [segmentCC_eq_segmentOC_union_startpoint, segmentOC_is_segmentOO_union_endpoint, Set.union_assoc]

/-- `segmentOO` is a subset of `segmentOC`.-/
theorem segmentOO_subset_segmentOC (a b : P) :
    segmentOO 𝕜 a b ⊆ segmentOC 𝕜 a b := by
  rw [segmentOC_is_segmentOO_union_endpoint 𝕜 a b]; simp

/-- The segment is independent of the order of the end-points. -/
theorem segmentOO_symm (a b : P) :
    segmentOO 𝕜 a b = segmentOO 𝕜 b a := by
  ext x
  constructor <;>
  · rintro ⟨t, ⟨⟨h0t, ht1⟩, habtx⟩⟩
    use 1 - t
    apply And.intro $ Set.mem_Ioo.mpr ⟨sub_pos.mpr ht1, sub_lt_self _ h0t⟩
    rw [AffineMap.lineMap_symm, AffineMap.comp_apply]
    nth_rewrite 2 [AffineMap.lineMap_apply]
    simp
    exact habtx

/-- The segment is independent of the order of the end-points. -/
theorem segmentCC_symm (a b : P) :
    segmentCC 𝕜 a b = segmentCC 𝕜 b a := by
  repeat rw [segmentCC_eq_segmentOO_union_endpoints]
  conv => lhs; rw [segmentOO_symm, Set.union_comm, ←Set.union_assoc]
  conv => rhs; rw [Set.union_assoc, Set.union_comm, Set.union_assoc, Set.union_comm]
  nth_rewrite 2 [Set.union_comm]
  dsimp

/-- The half-closed segment between two points is contained in the open segment between
the first point and a point beyond the second. -/
theorem segmentOC_subset_segmentOO (a x b : P) (hx : x ∈ segmentOO 𝕜 a b) :
    segmentOC 𝕜 a x ⊆ segmentOO 𝕜 a b := by
  simp only [segmentOO, Set.mem_image] at hx
  rcases hx with ⟨kx, ⟨hkx, hkxx⟩⟩
  simp only [Set.subset_def]
  intro p hp
  simp only [segmentOC, Set.mem_image] at hp
  rcases hp with ⟨kp, ⟨hkp, hkpp⟩⟩
  use (kp * kx)
  admit
  -- have haux := mul_lt_mul_of_pos_left (Set.mem_Ioo.mp hkx).right (Set.mem_Ioc.mp hkp).left
  -- rw [mul_one] at haux
  -- apply And.intro ⟨
  --   mul_pos (Set.mem_Ioc.mp hkp).left (Set.mem_Ioo.mp hkx).left,
  --   lt_of_lt_of_le haux (Set.mem_Ioc.mp hkp).right
  -- ⟩
  -- clear haux
  -- unfold AffineMap.lineMap at hkxx; simp at hkxx
  -- have haux := (eq_vadd_iff_vsub_eq x (kx • (b -ᵥ a)) a).mp hkxx.symm
  -- unfold AffineMap.lineMap at hkpp; simp at hkpp
  -- unfold AffineMap.lineMap; simp
  -- rw [haux, smul_smul] at hkpp
  -- exact hkpp

/-- The open segment between two points is contained in the open segment between
the first point and a point beyond the second. -/
theorem segmentOO_subset_segmentOO (a x b : P) (hx : x ∈ segmentOO 𝕜 a b) :
    segmentOO 𝕜 a x ⊆ segmentOO 𝕜 a b := by
  exact subset_trans (segmentOO_subset_segmentOC 𝕜 a x) (segmentOC_subset_segmentOO 𝕜 a x b hx)

/- If two `segmentOO`s based at the same initial point intersect then their
end points are collinear with respect to the initial point. -/
-- theorem segmentOO_inter_segmentOO_nonempty_collinear (a b b' : P)
--     (hi : Affine.segmentOO 𝕜 a b ∩ Affine.segmentOO 𝕜 a b' ≠ ∅ ) :
--     b ∈ Affine.segmentOO 𝕜 a b' ∨ b' ∈ Affine.segmentOO 𝕜 a b := by
--   rcases Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hi with ⟨x, hx⟩
--   rcases (Set.mem_image (AffineMap.lineMap a b) (Set.Ioo (0:𝕜) 1) x).mp hx.left with ⟨k, ⟨hk01, hlk⟩⟩
--   rcases (Set.mem_image (AffineMap.lineMap a b') (Set.Ioo (0:𝕜) 1) x).mp hx.right with ⟨k', ⟨hk01', hlk'⟩⟩
--   have heqx := Eq.trans hlk hlk'.symm
--   simp [AffineMap.lineMap] at heqx
--   have hl : AffineMap.lineMap a b (k'⁻¹ * k) = b' := by
--     calc
--       (k'⁻¹ * k) • (b -ᵥ a) +ᵥ a = k'⁻¹ • (k • (b -ᵥ a)) +ᵥ a := by rw [mul_smul]
--                                _ = k'⁻¹ • (k' • (b' -ᵥ a)) +ᵥ a := by rw [heqx]
--                                _ = (k'⁻¹ * k') • (b' -ᵥ a) +ᵥ a := by rw [←mul_smul]
--                                _ = (b' -ᵥ a) +ᵥ a := by rw [mul_comm, Field.mul_inv_cancel, one_smul]; exact Set.Ioo_neq_0 hk01'
--                                _ = b' := by simp

--   admit

variable {W : Type v} [AddCommGroup W] [Module 𝕜 W]
variable {Q : Type w} [AddTorsor W Q]

/-- Affine maps map `segmentCC`s to `segmentCC`s. -/
theorem segmentCC_maps_to_segmentCC (m : P →ᵃ[𝕜] Q) (a b : P) :
    m '' (segmentCC 𝕜 a b) = segmentCC 𝕜 (m a) (m b) := by
  unfold segmentCC; rw [AffineMap.image_map_lineMap m]

/-- Affine maps map `segmentOC`s to `segmentOC`s. -/
theorem segmentOC_maps_to_segmentOC (m : P →ᵃ[𝕜] Q) (a b : P) :
    m '' (segmentOC 𝕜 a b) = segmentOC 𝕜 (m a) (m b) := by
  unfold segmentOC; simp only [AffineMap.image_map_lineMap]

/-- Affine maps map `segmentOO`s to `segmentOO`s. -/
theorem segmentOO_maps_to_segmentOO (m : P →ᵃ[𝕜] Q) (a b : P) :
    m '' (segmentOO 𝕜 a b) = segmentOO 𝕜 (m a) (m b) := by
  unfold segmentOO; simp only [AffineMap.image_map_lineMap]

/-- Contracting homotheties map `segmentOC`s to `segmentOO`s. -/
theorem segmentOC_contracts_into_segmentOO (hk : k ∈ Set.Ioo (0:𝕜) 1) (a b : P) :
    (AffineMap.homothety a k) '' (segmentOC 𝕜 a b) ⊆ segmentOO 𝕜 a b := by
  simp only [segmentOC_maps_to_segmentOC, AffineMap.homothety_fixes_vertex]
  suffices ((AffineMap.homothety a k) b) ∈ segmentOO 𝕜 a b by
    exact segmentOC_subset_segmentOO 𝕜 a ((AffineMap.homothety a k) b) b this
  unfold segmentOO
  simp only [Set.mem_image, AffineMap.lineMap, AffineMap.homothety]; simp
  use k
  exact ⟨hk, rfl⟩

end Affine

end «Affine segments»

-- ********************************************************************
section «TopologicalAddTorsor»

/-!
## Affine Topological add torsors

Mathlib seems not to define topological add-torsors (affine spaces
with a topology that respects the operatons `vadd` and `vsub`).

The library `Mathlib.Analysis.Normed.Group.AddTorsor` contains a
theorem `continuous_vsub` which makes assumptions on the spaces involved,
but there is no a priori definition. This is compensated for in
this file.
-/

variable (𝕜 : Type u) [Ring 𝕜]
variable (V : Type v) [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
variable (P : Type w) [AddTorsor V P] [TopologicalSpace P]

/-- Class `ContinuousVSub M X` says that the subtraction action `(-ᵥ) : M → X → X`
is continuous in both arguments. -/
class ContinuousVSub : Prop where
  /-- The difference-action `(-ᵥ)` is continuous. -/
  continuous_vsub : Continuous fun p : P × P => p.1 -ᵥ p.2

/-- The following puts the right topology on affine spaces. -/
class TopologicalAddTorsor extends ContinuousVAdd V P, ContinuousVSub V P : Prop

end «TopologicalAddTorsor»

-- ********************************************************************
section «AffineSubspace»

/-!
## Topology of affine subspaces

Affine subspaces are furnished with the relative topology. This is
not contained in Mathlib yet.
-/

variable (𝕜 : Type u) [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P] [TopologicalSpace P]

/-- Affine subspaces are furnished with the relative topology. This is
not contained in Mathlib yet. -/
instance AffineSubspace.instTopologicalSpace (a : AffineSubspace 𝕜 P) [Nonempty ↥a] : TopologicalSpace a :=
  TopologicalSpace.induced a.subtype inferInstance

end «AffineSubspace»

-- ********************************************************************
section «Affine topology»

/-!
## Affine topology

This section defines the topology on affine spaces and shows that an
affine space with a topology which makes all actions of the (topological)
module and the (topological) base ring continuous is already homeomorphic
to the module through `vsub` and `vadd`.
-/

section «Algebra»

variable {𝕜 : Type u} [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- This is the map that comes from mappping as point `q` of the
affine space to the module given a point `p` by taking their difference `q -ᵥ p`.-/
def vector_to (fromP toP: P) : V := toP -ᵥ fromP

/--The affine translation map is the map that translates a point `p` in an affine space
by a vector `v` by adding `v +ᵥ p`.-/
def translate_by (fromP : P) (byV : V) : P := byV +ᵥ fromP

/-- Affine translation is a left inverse to the vector map. -/
@[simp] theorem translate_by_inv_vector_to (p q: P) :
    (translate_by p) (vector_to p q) = q := by
  simp only [translate_by, vector_to, vsub_vadd q p]

/-- Affine transtlation is a right inverse to the vector map. -/
@[simp] theorem vector_to_inv_translate_by (p : P) (v : V):
    (vector_to p) (translate_by p v) = v := by
  simp only [translate_by, vector_to, vadd_vsub]

end «Algebra»

section «Topology»

variable {𝕜 : Type u} [Ring 𝕜] [TopologicalSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P] [htopAddTorsor : TopologicalAddTorsor V P]

namespace Affine

/-- The vector map is continuous.-/
@[continuity] theorem vector_to_continuous (p : P) : Continuous (vector_to p) := by
  let f (q : P) := (q, p)
  have h_comp : (fun pp : P × P => pp.1 -ᵥ pp.2) ∘ f = vector_to p := by
    funext; simp [vector_to]
  rw [← h_comp]
  apply Continuous.comp
  · exact htopAddTorsor.continuous_vsub
  · have h_cont_f : Continuous f := by
      simp [f]; constructor
      exact (ContinuousMap.id P).continuous_toFun
      exact (ContinuousMap.const P p).continuous_toFun
    exact h_cont_f

/-- The affine translation map is continuous.-/
@[continuity] theorem translate_by_continuous (p : P) : Continuous (translate_by p) := by
  let f (v : V) := (v, p)
  have h_comp : (fun pp : V × P => pp.1 +ᵥ pp.2) ∘ f = translate_by p := by
    funext; simp [translate_by]
  rw [← h_comp]
  apply Continuous.comp
  · exact htopAddTorsor.continuous_vadd
  · have h_cont_f : Continuous f := by
      simp [f]; constructor
      exact (ContinuousMap.id V).continuous_toFun
      exact (ContinuousMap.const V p).continuous_toFun
    exact h_cont_f

/-- The affine space is homeomorphic to the module that acts on it. To get a witness
for this equivalence we need to fix an arbitrary point in P and then use translation and
vectorial map.-/
def homeomorphism_affine_space_equiv_module (p : P) : V ≃ₜ P where
  toFun := translate_by p
  invFun := vector_to p
  left_inv := by intro _; simp [translate_by, vector_to]
  right_inv := by intro _; simp [translate_by, vector_to]

/-- The line map is continuous. We need to prove this here, as the version
in Mathlib works only in modules. -/
@[continuity] theorem lineMap_continuous [TopologicalAddGroup V] {p₁ p₂ : P} :
    Continuous (AffineMap.lineMap p₁ p₂ : 𝕜 →ᵃ[𝕜] P) := by
  let lm : 𝕜 →ᵃ[𝕜] V := AffineMap.lineMap (0:V) (p₂ -ᵥ p₁)
  have hclm : Continuous lm := by apply AffineMap.lineMap_continuous
  let f (v : V) := (v, p₁)
  have hcf : Continuous f := by
    simp [f]; constructor
    exact (ContinuousMap.id V).continuous_toFun
    exact (ContinuousMap.const V p₁).continuous_toFun
  have h_comp : (fun pp : V × P => pp.1 +ᵥ pp.2) ∘ f ∘ lm = AffineMap.lineMap p₁ p₂ := by
    funext; simp [lm]; unfold AffineMap.lineMap; simp
  rw [← h_comp]
  apply Continuous.comp
  · exact continuous_vadd
  · apply Continuous.comp
    · exact hcf
    · exact hclm

end Affine

end «Topology»
end «Affine topology»

-- ********************************************************************
section «Homothety»

/-!
## Homotheties

The results in Mathlib on homotheties seem to be scattered, and
especially the results on continuity are proved only for a limited
range of topological spaces. This section introduces the main results.
-/

namespace AffineMap

section «Algebra»

variable {𝕜 : Type u} [CommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [NoZeroSMulDivisors 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- This shows that homotheties are injective. -/
theorem homothety_injective (p : P) (hk : k ≠ (0:𝕜)) :
    Function.Injective (AffineMap.homothety p k) := by
  unfold AffineMap.homothety
  intro p1 p2 h; dsimp at h
  exact vsub_left_cancel <| smul_right_injective V hk <| vadd_right_cancel p h

end «Algebra»

section «Topology/Ring»

variable {𝕜 : Type u} [CommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousConstSMul 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P] [hTopAddTorsor : TopologicalAddTorsor V P]

/-- Note: This is missing from Mathlib, or more precisely it is only proved
for normed spaces, see `Mathlib.Analysis.Normed.Group.AddTorsor`. -/
theorem Continuous.vsub [TopologicalSpace X] {f g : X → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f -ᵥ g) :=
  hTopAddTorsor.continuous_vsub.comp (hf.prod_mk hg : _)

open Continuous
open Topology

/-- This shows that homotheties are continuous. -/
theorem homothety_continuous'
    (p : P) (k : 𝕜) :
    Continuous (AffineMap.homothety p k) := by
  suffices ⇑(AffineMap.homothety p k) = fun x => k • (x -ᵥ p) +ᵥ p by
    rw [this]
    exact ((vsub continuous_id continuous_const).const_smul _).vadd continuous_const
  ext y
  simp [homothety_apply]

/-- Homotheties are continous affine maps. -/
def homothety_continuous_affine_map (p : P) (k : 𝕜) : P →ᴬ[𝕜] P where
  toFun := (AffineMap.homothety p k).toFun
  linear := (AffineMap.homothety p k).linear
  map_vadd' := (AffineMap.homothety p k).map_vadd'
  cont := homothety_continuous' p k

/-- Homotheties are homeomorphisms when the scaling factor is invertible. -/
def homothety_homeomorph_of_invertible (p : P) (k : 𝕜) (hInvk : Invertible k) : Homeomorph P P where
  toFun := (AffineMap.homothety p k).toFun
  invFun := (AffineMap.homothety p hInvk.invOf).toFun
  left_inv := by simp only [homothety]; intro x; simp
  right_inv := by simp only [homothety]; intro x; simp
  continuous_toFun := homothety_continuous' p k
  continuous_invFun := homothety_continuous' p hInvk.invOf

/-- Shows the function of `homothety_homeomorph_of_invertible`. -/
theorem homothety_homeomorph_of_invertible_toFun (p : P) (k : 𝕜) (hInvk : Invertible k) :
    (homothety_homeomorph_of_invertible p k hInvk).toFun = (AffineMap.homothety p k).toFun := rfl

/-- Invertible homotheties fix the neighbourhood filter of the vertex. -/
theorem homothety_fixes_nhd_of_invertible (p : P) (k : 𝕜) (hInvk : Invertible k) :
    Filter.map (AffineMap.homothety p k) (𝓝 p) = 𝓝 p := by
  have hh :=  (Homeomorph.map_nhds_eq $ homothety_homeomorph_of_invertible p k hInvk) p
  simp [homothety_homeomorph_of_invertible] at hh
  exact hh

end «Topology/Ring»

section «Topology/Field»

variable {𝕜 : Type u} [Field 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousConstSMul 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P] [hTopAddTorsor : TopologicalAddTorsor V P]

open Topology

/-- This defines an `Invertible` in case we are working with fields. -/
instance Invertible_from_Field [instField : Field α] (ha : a ≠ (0:α)) : Invertible a where
  invOf := instField.inv a
  invOf_mul_self := by simp only [instField.mul_comm]; exact instField.mul_inv_cancel a ha
  mul_invOf_self := instField.mul_inv_cancel a ha

/-- Homotheties are homeomorphisms when the ring is a field. -/
def homothety_homeomorph_of_field (p : P) (hk : k ≠ (0:𝕜)) : Homeomorph P P :=
  homothety_homeomorph_of_invertible p k (Invertible_from_Field hk)

/-- Shows the function of `homothety_homeomorph_of_invertible`. -/
theorem homothety_homeomorph_of_field_toFun (p : P) (hk : k ≠ (0:𝕜)) :
    ⇑(homothety_homeomorph_of_field p hk) = (AffineMap.homothety p k).toFun := rfl

/-- Invertible homotheties fix the neighbourhood filter of the vertex. -/
theorem homothety_fixes_nhd_of_field (p : P) (hk : k ≠ (0:𝕜)) :
    Filter.map (AffineMap.homothety p k) (𝓝 p) = 𝓝 p :=
  homothety_fixes_nhd_of_invertible p k (Invertible_from_Field hk)

/-- Invertible homotheties map neighbourhoods of the vertex to neighbourhoods o the vertex. -/
theorem homothety_maps_nhds_of_vertex_to_nhds (p : P) (hk : k ≠ (0:𝕜)) (hn : n ∈ (𝓝 p)) :
    (AffineMap.homothety p k) '' n ∈ 𝓝 p := by
  rw [←homothety_fixes_nhd_of_field p hk]
  exact Filter.image_mem_map hn

end «Topology/Field»

end AffineMap

end «Homothety»

-- ********************************************************************
section «AffineSubspace»

-- --------------------------------------------------------------------
section «Definitions»

variable (𝕜 : Type u) [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- The condition for a set to be an affine subspace. -/
structure IsAffineSubspace (carrier : Set P): Prop where
  smul_vsub_vadd_mem :
    ∀ (c : 𝕜) {p1 p2 p3 : P},
      p1 ∈ carrier → p2 ∈ carrier → p3 ∈ carrier → c • (p1 -ᵥ p2 : V) +ᵥ p3 ∈ carrier

/-- This allows us to view the fact that a set `IsAffineSubspace`
as `AffineSubspace`.-/
instance AffineSubspace.instCoeSort_IsAffineSubspace_to_AffineSubspace :
    CoeSort (IsAffineSubspace 𝕜 P s) (AffineSubspace 𝕜 P) where
  coe h := {
    carrier := s
    smul_vsub_vadd_mem := h.smul_vsub_vadd_mem
  }

/-- Mathlib does not seem to contain a defintion for the trivial
subspace consisting of a single point only. Could also be
defined via `AffineSubspace.affineSpan` -/
@[simp] def AffineSubspace.singleton (p : P):  AffineSubspace 𝕜 P where
  carrier := { p }
  smul_vsub_vadd_mem := by
    intro k p0 p1 p2
    intro h0; rw [Set.mem_singleton_iff] at h0
    intro h1; rw [Set.mem_singleton_iff] at h1
    intro h2; rw [Set.mem_singleton_iff] at h2
    rw [h0, h1, h2]; simp

end «Definitions»

-- --------------------------------------------------------------------
section «Properties»

namespace AffineSubspace

variable {𝕜 : Type u} [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- The set represented by the singleton-affine-subspace is the singleton set. -/
@[simp] theorem singleton_coe (p : P) : (AffineSubspace.singleton 𝕜 P p : Set P) = { p } := rfl

/-- A point is in an affien subspace iff it is in the carrier. -/
@[simp] theorem mem_carrier (a : AffineSubspace 𝕜 P) : p ∈ a ↔ p ∈ a.carrier := Iff.rfl

/-- A point is in the singleton-subspace iff it is identical to the
point defining the singleton. -/
@[simp] theorem mem_singleton_iff_eq : q ∈ AffineSubspace.singleton 𝕜 P p ↔ q = p := by
  simp only [AffineSubspace.singleton, AffineSubspace.mem_carrier, Set.mem_singleton_iff]

end AffineSubspace

end «Properties»

-- --------------------------------------------------------------------
section «Topology»

namespace AffineSubspace

variable {𝕜 : Type u} [Field 𝕜] [TopologicalSpace 𝕜] [LocallyCompactSpace 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P] [TopologicalSpace P]

/-- Finite dimensional afffine subspaces are closed sets within the
ambient affine space provided the field over which the structures are
defined is locally compact.
TODO Comparable results in Mathlib use normed spaces. This is not
necessary. It is enough if the topology of finite dimensional spaces over
the field are locally compact. See the proofs in the first chapter of
Rudin, Functional Analysis. -/
theorem closed_of_finiteDimensional' (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] :
    IsClosed (s : Set P) := by
  admit

end AffineSubspace

end «Topology»

end «AffineSubspace»


-- ********************************************************************
section «Convexity»

namespace Affine

-- --------------------------------------------------------------------
section «Definitions»

variable (𝕜 : Type u) [OrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]

/-- A star-convex set is a set where all linbes connecting a vertex to points
in the set lies in the set. -/
def IsStarConvex (v : P) (s : Set P) : Prop := ∀ ⦃x : P⦄, x ∈ s → segmentCC 𝕜 v x ⊆ s

/-- A convex set `IsStarConvex` star-vonvex at all of its points. -/
def IsConvex (s : Set P) : Prop := ∀ ⦃p : P⦄, p ∈ s → IsStarConvex 𝕜 P p s

end «Definitions»

-- --------------------------------------------------------------------
section «Properties»

variable {𝕜 : Type u} [OrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace IsStarConvex

/-- The base of a star-convex set is the set of points that lie at
the end of a line that emenates from the vertex. -/
def base (hs : IsStarConvex 𝕜 P v s) : Set P := by admit

/-- Star-Conxity is stable under finite intersectiion. -/
theorem inter (v : P) (s0 s1 : Set P)
    (hs0 : IsStarConvex 𝕜 P p s0) (hs1 : IsStarConvex 𝕜 P p s1) : IsStarConvex 𝕜 P p (s0 ∩ s1) := by
  admit

/-- Star-Conxity is stable under any intersectiion. -/
theorem iInter (v : P) (s : ι → Set P)
    (hs : ∀ i : ι, IsStarConvex 𝕜 P p (s i)) : IsStarConvex 𝕜 P p (⋂ i : ι, s i) := by
  admit

end IsStarConvex

namespace IsConvex

/-- Conxity is stable under finite intersectiion. -/
theorem inter (s0 s1 : Set P)
    (hs0 : IsConvex 𝕜 P s0) (hs1 : IsConvex 𝕜 P s1) : IsConvex 𝕜 P (s0 ∩ s1) := by
  admit

/-- Conxity is stable under any intersectiion. -/
theorem iInter (v : P) (s : ι → Set P)
    (hs : ∀ i : ι, IsConvex 𝕜 P (s i)) : IsConvex 𝕜 P (⋂ i : ι, s i) := by
  admit

end IsConvex

end «Properties»

end Affine

end «Convexity»

-- ********************************************************************
section «Weighted points»

section «Defintions»

variable {𝕜 : Type u} [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights. -/
def Finset.weightedPointsWithBase (hfin : Finset ι) (ps : ι → P) (b : P) : (ι → 𝕜) →ᵃ[𝕜] P where
  toFun := fun (w : ι → 𝕜) => ∑ i ∈ hfin, (w i) • (ps i -ᵥ b) +ᵥ b
  linear := by exact Finset.weightedVSubOfPoint hfin ps b
  map_vadd' := by
    intro w2 w1
    simp [add_smul, Finset.sum_add_distrib, ←vadd_assoc, vadd_eq_add]

/-- This shows how the funtion `weightedPointsWithBase` applies to given weights. -/
theorem Finset.weightedPointsWithBase_apply (hfin : Finset ι) (ps : ι → P) (b : P) (w : ι → 𝕜) :
  (hfin.weightedPointsWithBase ps b).toFun w = ∑ i ∈ hfin, (w i) • (ps i -ᵥ b) +ᵥ b := rfl

/-- The function that for a given weight-set assigns a base-point to the
weightes sum is constant in the following sense. Note that getting a
witness for the point whose existence is proved you need some form of
the axiom of choice. -/
theorem Finset.weightedPointsWithBase_const (hfin : Finset ι) (ps : ι → P) (w : ι → 𝕜):
    ∃! p : P, ∀ b : P, (hfin.weightedPointsWithBase ps b).toFun w = p  := by
  let f := fun (b : P) => (hfin.weightedPointsWithBase ps b).toFun w
  have hf : ∀ p p' : P, f p = f p' := by
    intro p p'
    have : p' = (p' -ᵥ p) +ᵥ p := (vsub_vadd p' p).symm
    dsimp only [f, weightedPointsWithBase]
    rw [this]
    admit
  let imf := f '' (Set.univ)
  have simf : imf.Subsingleton := by
    rintro x ⟨x', _, hxx'⟩
    rintro y ⟨y', _, hyy'⟩
    exact Eq.trans (Eq.trans hxx'.symm (hf x' y')) hyy'
  have imfne : imf ≠ ∅ := by exact Set.nonempty_iff_ne_empty.mp $ Set.image_nonempty.mpr Set.univ_nonempty
  have : ∃ p, imf = {p} := Or.resolve_left (Set.Subsingleton.eq_empty_or_singleton simf) imfne
  rcases this with ⟨p, himfp⟩
  use p
  simp
  admit

end «Defintions»

namespace Affine

section «Definitions for sets»

variable (𝕜 : Type u) [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable (P : Type w) [AddTorsor V P]
variable (ι : Type*) [DecidableEq ι]

/-- A set is a a join of points if it results from taking weighted sums
of a given vertex-set. -/
def JoinedPoints (v : ι → P) : Set P :=
  { p : P | ∃ s : Finset ι, ∃ w : ι → 𝕜, ∑ i ∈ s, w i = 1 ∧
    p = (s.weightedPointsWithBase v p).toFun w }

/-- A set is a a join of points if it results from taking weighted sums
of a given vertex-set. -/
def IsJoinedPoints (v : ι → P) (s : Set P) : Prop := s = JoinedPoints 𝕜 P ι v

/-- A set given by joining points is minimal iff removing any vertex
results in a strictly smaller join-set. -/
def IsMinimalJoinedPoints (v : ι → P) : Prop :=
  ∀ x : ι, JoinedPoints 𝕜 P { i : ι // i ≠ x } (fun i : { j // j ≠ x } => v i) ⊂ JoinedPoints 𝕜 P ι v

end «Definitions for sets»

section «Ring»

variable {𝕜 : Type u} [Ring 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {ι : Type*} [DecidableEq ι]

/-- If a set of vertices is a minimal set in the sense of `Affine.IsMinimalJoinedPoints`
then so is any subset. -/
theorem IsMinimalJoinedPoints.subset {p : ι  → Prop} (v : ι → P) (h : IsMinimalJoinedPoints 𝕜 P ι v) :
    IsMinimalJoinedPoints 𝕜 P (Subtype p) (fun i : Subtype p => v i) := by
  admit

end «Ring»

section «OrderedCommRing»

variable {𝕜 : Type u} [OrderedCommRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]
variable {ι : Type*} [DecidableEq ι]

/-- Joined points form a convex set. -/
theorem IsJoinedPoints.convex (v : ι → P) : IsConvex 𝕜 P (JoinedPoints 𝕜 P ι v) := by
  rintro p ⟨sp, wp, hwp1, hwpp⟩
  rintro q ⟨sq, wq, hwq1, hwqq⟩
  rw [Set.subset_def]
  rintro x ⟨k, hk, hkx⟩
  simp  [AffineMap.lineMap] at hkx
  let sp' := sp \ sq; let sq' := sq \ sp; let spq := sp ∩ sq
  let w : ι → 𝕜 := fun i =>
    if i ∈ sp' then k * (wp i)
    else if i ∈ sq' then (1 - k) * (wq i)
    else if i ∈ spq then k * (wp i) + (1 - k) * (wq i)
    else 0
  let s : Finset ι := sp ∪ sq
  have hs : s = sp' ∪ sq' ∪ spq := by admit
  have hsp : sp = sp' ∪ spq := by admit
  have hsq : sq = sq' ∪ spq := by admit
  have hd1 : Disjoint (sp' ∪ sq') spq := by admit
  have hd2 : Disjoint sp' sq' := by admit
  have hw1 : ∑ i ∈ s, w i = 1 := by
    admit
  rw [JoinedPoints, Set.mem_setOf]
  use s; use w
  apply And.intro hw1
  simp only [Finset.weightedPointsWithBase_apply, hs]
  rw [Finset.sum_union hd1, Finset.sum_union hd2]
  admit

/-- Joined points form a convex set. -/
theorem IsJoinedPoints.is_convex (v : ι → P) (h : IsJoinedPoints 𝕜 P ι v s) : IsConvex 𝕜 P s :=
  h ▸ IsJoinedPoints.convex v

/-- Joined points form a locally closed set only under suitable conditions.
TODO This cannot be true but in finite dimensions, and not even there. Needs completeness! -/
theorem IsJoinedPoints.is_locally_closed [TopologicalSpace P] (v : ι → P) (h : IsJoinedPoints 𝕜 P ι v s) : IsLocallyClosed s := by
  admit

end «OrderedCommRing»

end Affine

end «Weighted points»
