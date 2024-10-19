/-
Copyright (c) 2024 Stephan Maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/
import Mathlib.Data.Set.Image
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Interval.Set.Basic

/-!
# Set theory

This file collects theorems on sets that seem to be missing in Mathlib,
or that extend Mathlib's Set-capabilities.
-/

open Set

-- ********************************************************************
section «Missing theorems»

/-!
### Theorems missing from mathlib. -/

namespace Set

/-- In Mathlib, `Set.inter_subset` and `Set.union_subset` do not behave
in the same way even though they have names that suggest they should be
theorems with a similar structure. We need the shape of `Set.union_subset`
so we provide it here. -/
theorem inter_subset' {s s' t : Set α} (hs : s ⊆ t) (hs' : s' ⊆ t) : s ∩ s' ⊆ t := by
  rw [←inter_self t]
  apply inter_subset_inter
  exact hs
  exact hs'

/-- Mathlib does not provide set-operations relative to a set.-/
theorem rel_compl_inj_iff {s s' t : Set α} : s ∩ t = s' ∩ t ↔ sᶜ ∩ t = s'ᶜ ∩ t := by
  have h1 (u : Set α) : (u ∩ t) ∪ (uᶜ ∩ t) = t := by
    rw [←union_inter_distrib_right, union_compl_self, univ_inter]
  suffices h : s ∩ t = s' ∩ t → sᶜ ∩ t = s'ᶜ ∩ t by
    admit
  intro h; ext x; simp only [inter_def, mem_setOf]
  constructor
  . rintro ⟨hxsc, hxt⟩
    admit
    --rw [not_mem_of_mem_compl] at hxsc
  admit

/-- This coerces a witness for a singleton to the element defining the
singleton. -/
@[simp] theorem singleton_coe {y : α} (x : ({ y } : Set α)) : ↑x = y :=
  Set.eq_of_mem_singleton $ Subtype.mem x

/--
TODO Check if necessary. -/
@[simp] theorem not_empty_of_mem {s : Set α} (hx : x ∈ s) : s ≠ ∅ := by
  rw [←Set.nonempty_iff_ne_empty]; exact Set.nonempty_of_mem hx

/--
TODO Check if necessary. -/
@[simp] theorem image_eq_not_empty {α β} {f : α → β} {s : Set α} :
    f '' s ≠ ∅ ↔ s ≠ ∅ := by
  apply Iff.ne
  exact Set.image_eq_empty

/- ---------- Mathlib.Data.Subtype ------------------------------- -/

/-- Compare `Subtype.map`.-/
@[simp] def apply_subtype {α β} {s : Set α} (f : α → β) (x : s) :
    f '' s := ⟨f x, Set.mem_image_of_mem f x.property⟩

/-- Remove this. -/
@[simp] def to_eq_subtype {α} {s s' : Set α} (hs : s = s') (x : s) : s' :=
  ⟨x.val, hs ▸ x.property⟩

/- ---------- Mathlib.Order.Interval.Set.Basic -------------------- -/

@[simp] theorem Ioo_01_neq_0 [OrderedCommRing 𝕜] (hk : k ∈ Set.Ioo (0:𝕜) 1) : k ≠ 0 := by
  exact ne_of_gt (Set.mem_Ioo.mp hk).left

end Set

end «Missing theorems»

-- ********************************************************************
section «Function»

/- ---------- Init.Prelude -------------------- -/

namespace Function

/-- This defines that a function is not constant. -/
def Nonconstant (f : α → β) : Prop := ∀ b : β, f ≠ Function.const α b

/-- A function on a nonempty type is not constant iff it assumes two
different values. -/
theorem neq_const_iff_exists [hne : Nonempty α] (f : α → β) :
    Nonconstant f ↔ ∃ a0 a1 : α, f a0 ≠ f a1 := by
  constructor
  · intro h
    rcases Nonempty.map f hne with ⟨b⟩
    rcases Function.ne_iff.mp (h b) with ⟨a0, ha0⟩
    simp only [Function.const_apply] at ha0
    rcases Function.ne_iff.mp (h $ f a0) with ⟨a1, ha1⟩
    simp only [Function.const_apply] at ha1
    exact ⟨a0, a1, ha1.symm⟩
  · rintro ⟨a0, a1, h⟩
    intro b
    rw [Function.ne_iff]
    simp only [Function.const_apply]
    if h0 : f a0 = b then use a1; exact (h0 ▸ h.symm)
    else if f a1 = b then use a0
    else use a0

end Function

end «Function»

-- ********************************************************************
section «Subset relations»

/-!
### Subset relations

To do topology, we need to be able to move  between different points of
view. For example, we must, depending on the question we look at, view
a subset `s ` of a set `t` as a subset of the entire space or as a subset
of the type `t`. And we must be able to change our point of view nimbly.
This file provides the machinery for doing so. -/

namespace Set

/- ---------- Rel -------------------------------------- -/

/-- Turns a subset of a containing set into a set of the containing set
thought of a type. Compare `Set.inclusion`. -/
def rel_set_of {s t : Set α} (_ : s ⊆ t) : Set t := { x : t | (x : α) ∈ s }

/-- Notation for `Set.rel_set_of`. -/
scoped[Set] notation "rel[" t "] " hst:100 => @rel_set_of _ _ t hst

/-- An element of `rel[t] _` is an element of the set. -/
theorem mem_rel_set_of {s t : Set α} (hst : s ⊆ t) :
    ∀ x : t, x ∈ (rel[t] hst) ↔  (x : α) ∈ s := by
  intro x; rw [rel_set_of, mem_setOf]

/-- Subset-realtion and `rel[_]` commute. -/
theorem rel_set_of_subset_comm {s t : Set α} (hst : s ⊆ t) (hst' : s' ⊆ t) :
    (rel[t] hst) ⊆ (rel[t] hst') ↔ s ⊆ s' := by
  unfold rel_set_of; rw [subset_def, subset_def]; constructor
  . intro h x hx; specialize h ⟨x, mem_of_subset_of_mem hst hx⟩; simp at h; exact h hx
  . intro h x hx; rw [mem_setOf] at hx; rw [mem_setOf]; specialize h x; exact h hx

/-- The image of a relative set under `Subtype.val` is the set. -/
theorem rel_set_of_subtype {s t : Set α} (hst : s ⊆ t) :
    Subtype.val '' (rel[t] hst) = s := by
  ext x; rw [mem_image]; simp only [mem_rel_set_of hst]; constructor
  . rintro ⟨x', ⟨hxs', hxx'⟩⟩; rw [hxx'] at hxs'; exact hxs'
  . intro hxs; use ⟨x, mem_of_subset_of_mem hst hxs⟩

/-- This shows how a subset relation is translated by `rel[_]`. -/
theorem rel_set_of_trans {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    rel[u] (subset_trans hst htu) ⊆ rel[u] htu := by
  unfold rel_set_of
  simp only [subset_def]
  intro x
  rw [mem_setOf, mem_setOf]
  exact mem_of_subset_of_mem hst

/-- If `Set.as_set_of` is applied through a set of two inclusions, the result
equals the image of `Set.as_set_of` under `Set.inclusion`. -/
theorem rel_set_of_trans_inclusion {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    rel[u] (subset_trans hst htu) = inclusion htu '' rel[t] hst := by
  ext x; simp only [rel_set_of, rel_set_of, inclusion, mem_setOf, mem_image]; constructor
  . intro h
    use ⟨x, mem_of_subset_of_mem hst h⟩
  . rintro ⟨y, ⟨hys, hyx⟩⟩
    rw [Subtype.mk_eq_mk] at hyx
    rw [←hyx]
    assumption

/-- Given a subset, and a global property, the relative set defined
in the subset by this property is equal to the intersection of the
subset with the set defined by the property. -/
theorem setOf_eq_rel_set_of_inter_setOf {t : Set α} (p : α → Prop) :
    { x : t | p x.val } = rel[t] ( @inter_subset_left _ t (setOf p) ) := by

  admit

/-- Empty set and `rel[_]` commute. -/
theorem  rel_set_of_empty {t : Set α} :
    (rel[t] (empty_subset t) ) = ∅ := by
  unfold rel_set_of; rfl

/-- Equality-relation and `rel[_]` commute. -/
theorem  rel_set_of_eq_comm {s t : Set α} (hst : s ⊆ t) (hst' : s' ⊆ t) :
    (rel[t] hst) = (rel[t] hst') ↔ s = s' := by
  unfold rel_set_of; constructor
  . intro h; ext x; admit
  . admit

/-- `Set.as_set_of` is the same as taking the preimage of the set
under the map `Subtype.val`. -/
theorem rel_set_of_eq_preimage_subtype_val {s t : Set α} (hst : s ⊆ t) :
    rel_set_of hst = ( @Subtype.val _ t : t → α ) ⁻¹'  s := by
  ext x; rw [mem_preimage, mem_rel_set_of]

/-- Talking union and `rel[_]` commute. -/
theorem  rel_set_of_union_comm {s s' t : Set α} (hst : s ⊆ t) (hst' : s' ⊆ t) :
    (rel[t] union_subset hst hst') = rel[t] hst ∪ rel[t] hst' := by
  ext x; simp only [mem_rel_set_of, mem_union]

/-- Talking intersection and `rel[_]` commute. -/
theorem  rel_set_of_inter_comm {s s' t : Set α} (hst : s ⊆ t) (hst' : s' ⊆ t) :
    (rel[t] inter_subset' hst hst') = rel[t] hst ∩ rel[t] hst' := by
  ext x; simp only [mem_rel_set_of, inter_def, mem_setOf]

/-- Talking complements and `rel[_]` commute. -/
theorem  rel_set_of_compl_comm {s t : Set α} (hst : s ⊆ t) :
    (rel[t] hst)ᶜ = rel[t] (@inter_subset_right _ sᶜ t) := by
  admit

/-- Disjointness `rel[_]` commute. -/
theorem  rel_set_of_disjoint_comm {s s' t : Set α} (hst : s ⊆ t) (hst' : s' ⊆ t) :
    Disjoint (rel[t] hst) (rel[t] hst') ↔ Disjoint s s' := by
  rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty]
  rw [←rel_set_of_inter_comm, ←rel_set_of_empty, rel_set_of_eq_comm]

/- ---------- From -------------------------------- -/

/-- Turns a set defined in a subtype into a set in the containing
type. -/
def from_set {t : Set α} {s : Set t} : Set α := (fun x => Subtype.val '' x) s

/-- Notation for `Set.from_set_of`. -/
scoped[Set] notation "from[" t "] " s:100 => @from_set _ t s

/-- The set resulting from `from[_]` is a subset of the set. -/
theorem from_set_to_subset {t : Set α} (s : Set t) :
    from[t] s ⊆ t := by
  unfold from_set; simp only [Set.image, Set.mem_setOf, Set.subset_def]
  intro x; rintro ⟨x', ⟨_, hxx'⟩⟩
  rw [←hxx']
  exact x'.property

/-- Notation for `Set.from_set_of_subset`. -/
scoped[Set] notation "from'[" t "] " s:100 => @from_set_to_subset _ t s

/-- Talking union and `from[_]` commute. -/
theorem  from_set_union_comm {t : Set α} (s s' : Set t) :
    from[t] ( s ∪ s' ) = from[t] s ∪ from[t] s' := by
  admit

/-- Talking intersection and `from[_]` commute. -/
theorem  from_set_inter_comm {s s' t : Set α} (hst : s ⊆ t) (hst' : s' ⊆ t) :
    (rel[t] inter_subset' hst hst') = rel[t] hst ∩ rel[t] hst' := by
  ext x; simp only [mem_rel_set_of, inter_def, mem_setOf]

/-- Talking complements and `from[_]` commute. -/
theorem  from_set_compl_comm {t : Set α} (s : Set t) :
    from[t] sᶜ = (from[t] s)ᶜ ∩ t := by
  admit

/-- Talking complements and `from[_]` commute. -/
theorem  from_set_compl_comm' {t : Set α} (s : Set t) :
    (from[t] s)ᶜ = ( from[t] sᶜ ) ∪ tᶜ := by
  admit

/-- The operations `from[_]` and `rel[_]` are left and right inverse
of each other. -/
theorem from_set_of_rel_set_of_eq_id {s t : Set α} (hst : s ⊆ t) :
    from[t] ( rel[t] hst ) = s := by
  unfold from_set; unfold rel_set_of
  simp only [Set.image, Set.mem_setOf]
  ext x
  rw [mem_setOf]
  constructor
  . rintro ⟨x', ⟨hx', hxx'⟩⟩; rw [hxx'] at hx'; assumption
  . intro h; use ⟨x, mem_of_mem_of_subset h hst⟩

/-- The operations `from'[_]` and `rel[_]` are right and left inverse
of each other. -/
theorem rel_set_of_from_set_of_eq_id {t : Set α} (s : Set t) :
    rel[t] ( from'[t] s ) = s := by
  unfold rel_set_of; unfold from_set
  simp only [Set.image, Set.mem_setOf]
  ext x
  rw [mem_setOf]
  constructor
  . rintro ⟨x', ⟨hx', hxx'⟩⟩
    have : x = x' := Subtype.mk_eq_mk.mpr hxx'.symm
    rw [this]
    assumption
  . intro hxs; use x

/-- Two subset of a given enclosing set are equal relativ to the enclosing set
they are equal as sets. -/
theorem set_eq_iff_rel_set_eq {s s' t : Set α} (hst : s ⊆ t) (hst' : s' ⊆ t) :
    s = s' ↔ rel[t] hst = rel[t] hst' := by
  unfold rel_set_of; constructor
  . intro hss'; rw [hss']
  . intro hss'; ext x
    rw [setOf, setOf] at hss'
    constructor
    . intro hxs
      have := congr_fun hss' ⟨x, mem_of_subset_of_mem hst hxs⟩
      exact this.mp hxs
    . intro hxs'
      have := congr_fun hss' ⟨x, mem_of_subset_of_mem hst' hxs'⟩
      exact this.mpr hxs'

/-- Two subsets of a type that is itself a set are equal iff they are
equal as subset of the entire space. -/
theorem rel_set_eq_iff_from_set_eq {t : Set α} (s s' : Set t)  :
    s = s' ↔ from[t] s = from[t] s' := by
  admit

/-- Given a subset, and a global property, the relative set defined
in the subset by this property is equal to the intersection of the
subset with the set defined by the property. -/
theorem from_set_of_setOf_eq_inter_setOf {t : Set α} (p : α → Prop) :
    from[t] { x : t | p x.val } = t ∩ setOf p := by
  unfold from_set; simp only [Set.image, Set.mem_setOf]; rw [←Set.sep_mem_eq]
  ext x; rw [mem_setOf, mem_setOf, mem_setOf]
  constructor
  . rintro ⟨⟨z, hz⟩, hzx⟩; simp at hzx; rw [←hzx.right]; exact ⟨hz, hzx.left⟩
  . rintro ⟨hxt, hpx⟩; use ⟨x, hxt⟩

/- ---------- Relative functions ----------------------------- -/

/-- Given a function which preserves given sets, this is the function
restricted to those sets.
TODO Use Subtype.map instead
-/
def rel_set_fct {t : Set α} {t' : Set β} {f : α → β} (hfst : f '' t ⊆ t') (x : t) : t' :=
  ⟨f x, hfst ⟨x, x.2, rfl⟩⟩

/-- Notation for `Set.rel_set_fct`. -/
scoped[Set] notation "relF[" t ", " t' "] " hfst:100 => @rel_set_fct _ _ t t' _ hfst

end Set

end «Subset relations»
