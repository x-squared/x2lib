/-
Copyright (c) 2024 Stephan Maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Homeomorph

import X2lib.Topology.PiecewiseLinear.Aux.Set

/-!
# Topology for PL-topology

TODO

## Main results

- `exists_foo`: the main existence theorem of `foo`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Thales600BC] for the original account on Xyzzyology.
-/

--[FiniteDimensional 𝕜 V]

open Set
open Filter
open Topology
open BigOperators

-- ********************************************************************
section «Relative topology»

/-!
### Separation of sets by sets
.  -/

variable [topS: TopologicalSpace S]
variable [topS': TopologicalSpace S']

namespace Topology

/-- A set is relatively open with respect to an enclosing set iff it
is the intersection of the enclosing set with an open set in the ambient
space. -/
theorem rel_open_iff_inter_with_open (hst : s ⊆ t) :
    ( IsOpen $ rel[t] hst ) ↔ ∃ o : Set S, ( IsOpen o ) ∧ ( t ∩ o ) = s := by
  constructor
  · intro hsot
    rcases isOpen_induced_iff.mp hsot with ⟨o, ⟨ho, hi⟩⟩
    use o; apply And.intro ho
    simp only [Set.preimage, rel_set_of] at hi
    have h := congr_arg (fun x => from[t] x) hi
    dsimp at h
    rw [from_set_of_setOf_eq_inter_setOf] at h
    rw [from_set_of_setOf_eq_inter_setOf] at h
    simp only [setOf] at h
    rw [←Set.right_eq_inter.mpr hst] at h
    assumption
  · rintro ⟨o, ⟨ho, htos⟩⟩
    rw [isOpen_induced_iff]
    use o
    apply And.intro ho
    rw [preimage, rel_set_of]
    ext x'
    let x := x'.val; have xdef : x = x'.val := rfl
    have hxt : x ∈ t := by rw[xdef]; exact x'.property
    rw [mem_setOf, mem_setOf, ←xdef]
    constructor
    · intro hxo
      have := (mem_inter_iff x t o).mpr ⟨hxt, hxo⟩
      rw [htos] at this
      assumption
    · intro hxs
      rw [←htos, mem_inter_iff] at hxs
      exact hxs.right

/-- A set is relatively closed with respect to an enclosing set iff it
is the intersection of the enclosing set with an closed set in the ambient
space. -/
theorem rel_closed_iff_inter_with_closed (hst : s ⊆ t) :
    ( IsClosed $ rel[t] hst ) ↔ ∃ c : Set S, ( IsClosed c ) ∧ ( t ∩ c ) = s := by
  constructor
  · intro hc; rw [←isOpen_compl_iff, rel_set_of_compl_comm, rel_open_iff_inter_with_open] at hc
    rcases hc with ⟨o, ⟨hoo, htost⟩⟩
    use oᶜ
    apply And.intro $ isClosed_compl_iff.mpr hoo
    rw [inter_comm, rel_compl_inj_iff, compl_compl] at htost
    rw [inter_comm, htost, inter_eq_left]
    assumption
  · rintro ⟨c, ⟨hcc, htcs⟩⟩
    rw [←isOpen_compl_iff, rel_set_of_compl_comm, rel_open_iff_inter_with_open]
    use cᶜ
    apply And.intro $ isOpen_compl_iff.mpr hcc
    rw [inter_comm] at htcs
    rw [inter_comm, rel_compl_inj_iff, compl_compl, compl_compl, htcs, eq_comm, inter_eq_left]
    assumption

/-- If a set is open, it will be open relative to a set. -/
theorem rel_open_if_open {s t : Set S} (hst : s ⊆ t) (ho : IsOpen s) : IsOpen $ rel[t] hst := by
  rw [rel_open_iff_inter_with_open]
  use s
  apply And.intro ho
  exact Set.inter_eq_self_of_subset_right hst

/-- If a set is closed, it will be closed relative to a set. -/
theorem rel_closed_if_closed {s t : Set S} (hst : s ⊆ t) (hc : IsClosed s) : IsClosed $ rel[t] hst := by
  rw [←isOpen_compl_iff, rel_set_of_compl_comm, rel_open_iff_inter_with_open]
  use sᶜ
  apply And.intro $ isOpen_compl_iff.mpr hc
  rw [inter_comm]

/-- If a set is open, it will be open relative to a set. -/
theorem open_as_subset_if_rel_open {t : Set S} {s : Set t} :
    IsOpen s ↔ (IsOpen $ rel[t] (from'[t] s)) := by
  rw [rel_set_of_from_set_of_eq_id]

/-- A continuous function that preserves a set is a continuous function on that set.
This restates the theorems `ContinuousOn.restrict_mapsTo` and `Continuous.continuousOn`.-/
theorem rel_map_continuous {s : Set S} {s' : Set S'} {f : S → S'} (hfc : Continuous f) (hf : Set.MapsTo f s s') :
    Continuous $ Set.MapsTo.restrict f s s' hf := by
  exact ContinuousOn.restrict_mapsTo (Continuous.continuousOn hfc) hf

end Topology

end «Relative topology»

-- ********************************************************************
section «Separation of sets by sets»

/-!
### Separation of sets by sets
.  -/

variable [TopologicalSpace S]
variable [TopologicalSpace S']

namespace Topology

/-- Two sets in a topological space are seperated iff the closure of
any one of them does not meet the other set. The intersection of the
two closures is not necessarily empty (if it is, the space is disconnected),
and it is said to separate the space. Note that both sets may be empty. -/
def AreSeperated (u v : Set S) : Prop :=
  ( (closure u) ∩ v ) = ∅ ∧ ( u ∩ (closure v) ) = ∅

/-- Separation by a set is a symmetric property. -/
theorem are_separated_symm (u v : Set S) :
    AreSeperated u v ↔ Topology.AreSeperated v u := by
  unfold AreSeperated
  nth_rewrite 1 [and_comm]; nth_rewrite 3 [inter_comm]; nth_rewrite 4 [inter_comm]
  simp

/-- A set separates a two sets in a topological space if its complement
is the union of two sets and the sets are separated. We call the set `s`
the separating set, and the other two sets the separated sets`-/
def Separates (u s v : Set S) : Prop :=
  ( u ∪ v = sᶜ ) ∧ ( Topology.AreSeperated u v )

/-- Separation by a set is a symmetric property. -/
theorem separates_symm {u s v : Set S} :
    Separates u s v ↔ Separates v s u := by
  unfold Separates; simp only [union_comm, are_separated_symm]

/- All sets involved in a separation are disjoint. -/
-- theorem separates_disjoint {u s v : Set S} (Separates u s v) :
--     @Disjoint (Set S) _ _ u v := by
--   admit

/-- Separation by a set is a symmetric property. -/
theorem separates_imp_complements (u s v : Set S)
    (hsep : Separates u s v) : ( uᶜ = s ∪ v ) ∧ ( vᶜ = s ∪ u ) := by
  suffices haux : (u' v' : Set S) → (Separates u' s v') → ( u'ᶜ = s ∪ v' ) by
    exact ⟨haux u v hsep, haux v u $ separates_symm.mp hsep⟩
  intro a b hab
  have := Eq.trans (congr_arg compl hab.left) $ compl_compl s
  simp only [Set.compl_union] at this
  have := congr_arg (fun w => w ∪ b) this; simp at this
  simp [Set.inter_union_distrib_right, Set.compl_union_self] at this
  rw [←this]
  have := Set.union_subset_union_right aᶜ $ subset_trans (subset_closure) (Set.subset_compl_iff_disjoint_left.mpr $ Set.disjoint_iff_inter_eq_empty.mpr hab.right.right)
  rw [Set.union_self] at this
  exact subset_antisymm (Set.subset_union_left) this

/-- When a closed set separates two other sets then each of the separated sets is open. -/
theorem separated_by_closed_set_imp_separated_sets_open {u s v : Set S}
    (hs : Separates u s v) (hc : IsClosed s) : IsOpen u ∧ IsOpen v := by
  suffices haux : (u' v' : Set S) → (Topology.Separates u' s v') → IsOpen u' by
    exact ⟨haux u v hs, haux v u $ separates_symm.mp hs⟩
  intro a b hab
  have hacsb : aᶜ = s ∪ b := by exact (Topology.separates_imp_complements a s b hab).left
  rw [←isClosed_compl_iff, hacsb]
  have : IsClosed $ s ∪ b := by
    have := Set.subset_compl_iff_disjoint_left.mpr $ Set.disjoint_iff_inter_eq_empty.mpr hab.right.right
    rw [hacsb] at this
    have := Set.union_subset_union_right s this
    rw [←union_assoc, Set.union_self] at this
    have := subset_antisymm this (Set.union_subset_union_right s (subset_closure))
    rw [←this]
    apply IsClosed.union
    exact hc
    apply isClosed_closure
  exact this

/-- Given three disjoint sets two o which are open and one is closed then the
closed set separates the open sets. -/
theorem separated_if_triplet_open_open_closed [TopologicalSpace S] {u s v : Set S}
    (husd : Disjoint u s) (hvsd : Disjoint v s) (huvd : Disjoint u v)
    (huo : IsOpen u) (hvo : IsOpen v) (hsc : IsClosed s) :
    Separates u s v := by

  admit

/-- Two open sets are separated by the intersection of their complements. -/
theorem open_sets_are_separated {u v : Set S} (huo : IsOpen u) (hvo : IsOpen v) :
    ( Separates u (uᶜ ∩ vᶜ) v ) ∧ (IsClosed  (uᶜ ∩ vᶜ) ) := by

  admit

/-- Given two disjoint sets whose union is closed, if one of them is open then
the triplet consisting of these two sets and the complement of their union form
a separating triplet. -/
theorem separated_if_open_closed [TopologicalSpace S] {u s : Set S}
    (hd : Disjoint u s) (ho : IsOpen u) (hc : IsClosed (u ∪ s)) :
    Separates u s (u ∪ s)ᶜ ∧ ( ( IsClosed s ) ∧ ( IsOpen (u ∪ s)ᶜ ) ):= by
  unfold Separates; unfold AreSeperated
  have : s = (u ∪ s) ∩ uᶜ := by
    rw [Set.union_inter_distrib_right]; simp; apply Disjoint.le_compl_right; exact Disjoint.symm hd
  let v := (u ∪ s)ᶜ
  have vdef : v = (u ∪ s)ᶜ := rfl
  rw [←vdef]
  have : u ∪ v = sᶜ := by admit
  rw [and_assoc]; apply And.intro this
  have : closure (u ∪ s) = u ∪ s := closure_eq_iff_isClosed.mpr hc

  --have cs : IsClosed s := by rw [this]; exact IsClosed.inter hc (isClosed_compl_iff.mpr ho)
  have hoc : IsOpen v := isOpen_compl_iff.mpr hc

  have : v ⊆ uᶜ := compl_le_compl $ Set.subset_union_left
  have : closure v ⊆ uᶜ := (IsClosed.closure_subset_iff (isClosed_compl_iff.mpr ho)).mpr this

  rw [and_assoc];
  admit

/-- When a closed set separates two other sets then the frontier of these sets is contained
in the separating set. -/
theorem separated_by_closed_set_imp_frontier_in_separating_set [TopologicalSpace S] {u s v : Set S}
    (hs : Topology.Separates u s v) (hcs : IsClosed s) : ( frontier u ⊆  s ) ∧ ( frontier v ⊆  s ) := by
  suffices haux : (u' v' : Set S) → (Separates u' s v') → ( frontier u' ⊆  s ) by
    exact ⟨haux u v hs, haux v u $ separates_symm.mp hs⟩
  admit

/-- When a closed set separates two other sets, the the separating set has empty interior
iff it is equal to the frontier of the seperated. -/
theorem separated_by_closed_set_imp_separating_set_has_empty_interior_iff_eq_frontier [TopologicalSpace S] {u s v : Set S}
    (hs : Topology.Separates u s v) (hcs : IsClosed s) : ( interior s = ∅ ) ↔ ( frontier u = s ) ∧ ( frontier v =  s ) := by
  suffices haux : (u' v' : Set S) → (Separates u' s v') → ( ( interior s = ∅ ) ↔ ( frontier u' = s ) ) by
    have h1 := haux u v hs
    have h2 := haux v u $ separates_symm.mp hs
    constructor
    · intro hempty; exact ⟨h1.mp hempty , h2.mp hempty⟩
    · intro heq;  exact h1.mpr heq.left
  admit

/-- When there is a sepatared triplet and a continuous map into the entire set that
meets both the seperated parts, then the domain of the continous map is also seperated.
TODO Do the same for Path.
-/
theorem separates_preimage_under_continuous_separates
    {u s v : Set S} (husv : Separates u s v)
    {f : S' → S} (hf : Continuous f)
    (hfu : f ⁻¹' u ≠ ∅) (hfv : f ⁻¹' v ≠ ∅)  :
    Separates (f ⁻¹' u) (f ⁻¹' s) (f ⁻¹' v) ∧ ( ∃ s' : S', s' ∈ f ⁻¹' s ) := by

  admit

-- theorem separated_by_closed_set_stable_under_intersection [TopologicalSpace S]
--     {u s v : Set S} {u' s' v' : Set S} {t t' : Set S}
--     (hu : u ⊆ t) (hs : s ⊆ t) (hv : v ⊆ t) (hu' : u' ⊆ t') (hs' : s' ⊆ t') (hv' : v' ⊆ t')
--     (hss : Topology.Separates (in[t] hu) (in[t] hs) (in[t] hv))
--     (hss' : Topology.Separates (in[t'] hu') (in[t'] hs') (in[t'] hv')) (hcs : IsClosed $ in[t] hs) (hcs : IsClosed $ in[t'] hs')
--     : Topology.Separates (in[t ∩ t'] inter_subset_inter hu hu') (in[t ∩ t'] s ∪ s') (in[t ∩ t'] v ∪ v') := by

--   admit


end Topology

end «Separation of sets by sets»
