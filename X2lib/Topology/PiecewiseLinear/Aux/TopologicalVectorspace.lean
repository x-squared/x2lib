/-
Copyright (c) 2024 Stephan maier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephan Maier
-/

import Mathlib

/-!
# Topological Vector Spaces


## References

See [Thales600BC] for the original account on Xyzzyology.
-/

-- ********************************************************************
section «General norms»

/-- A type-class version of `a ≥ 0`.  -/
class GeZero (α : Type*) [LE α] [Zero α] : Prop where
  out : ∀ a : α, a ≥ 0

variable (𝕜 : Type*)
variable (ν : Type*)

/--

We tried to use `Mathlib.Algebra.Order.Ring.Unbundled.Nonneg` but failed
to make the theorems below work reasonably.
TODO. -/
class GNormed [LinearOrderedCommSemiring ν] [GeZero ν] [NeZero (1:ν)] where
  /-- The norm defined in this structure. -/
  gnorm : 𝕜 → ν

export GNormed (gnorm)
variable [LinearOrderedCommSemiring ν] [LinearOrder ν] [GeZero ν] [NeZero (1:ν)]

-- @[inherit_doc]
-- notation "γ‖" e "‖" => gnorm e

section «Field»

class GNormedField [Field 𝕜] extends GNormed 𝕜 ν where
  /-- the `gnorm`-function is a norm. -/
  norm_add (a b : 𝕜) : gnorm (a + b) ≤ gnorm a + gnorm b
  /-- The norm respects the multiplicativ structure. -/
  norm_mul (a b : 𝕜) : gnorm (a * b) = gnorm a * gnorm b
  /-- The norm of `0` is `0`. -/
  norm_zero : gnorm 0 = 0
  /-- The norm of `1` is `1`. -/
  norm_one : gnorm 1 = 1
  /-- The norm is nontrivial. -/
  norm_nontrivial : ∃ k : 𝕜, gnorm k > 1

end «Field»

section «Topology»

open Topology

/-- This defines a topology that is induced by a generalized norm. -/
class GNormedTopology (α : Type*) [top : TopologicalSpace α]
    [topν : TopologicalSpace ν] [OrderTopology ν] [GNormed α ν] : Prop where
  /-- The topology is generated the generalized norm. -/
  topology_eq_generate_gnorm : top = TopologicalSpace.induced gnorm topν

end «Topology»

end «General norms»

-- ********************************************************************
section «Balanced sets»

variable (ν : Type*) [LinearOrderedCommSemiring ν] [GeZero ν] [NeZero (1:ν)]
variable (𝕜 : Type*) [Field 𝕜]

open Pointwise

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a` has norm at most `1`. -/
def GBalanced {E : Type*} [GNormed 𝕜 ν] [SMul 𝕜 E] (A : Set E) :=
  ∀ k : 𝕜, gnorm k ≤ (1:ν) → k • A ⊆ A

variable [TopologicalSpace ν] [htopν : OrderTopology ν]
variable [gnormed : GNormedField 𝕜 ν] [TopologicalSpace 𝕜] [TopologicalRing 𝕜] [htopg : GNormedTopology ν 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [csmul : ContinuousSMul 𝕜 E]

open Topology

/-- Every neighbourhood of the origin contains a balanced neighbourhood. -/
theorem balanced_nhd {V : Set E} (hv : V ∈ 𝓝 0) : ∃ Vb : Set E, (Vb ∈ 𝓝 0) ∧ GBalanced ν 𝕜 Vb := by
  let f : 𝕜 × E → E  := fun (k, e) => k • e
  have h0 : f (0, 0) = 0 := by rw [smul_eq_zero]; simp
  have h1 : ContinuousAt f ((0:𝕜), (0:E)) := Continuous.continuousAt csmul.continuous_smul
  have : ∀ A ∈ 𝓝 (f (0, 0)), f ⁻¹' A ∈ 𝓝 (0, 0) := by exact continuousAt_def.mp h1
  rw [h0] at this
  have : f ⁻¹' V ∈ 𝓝 (0, 0) := by exact this V hv
  rcases mem_nhds_prod_iff.mp this with ⟨u, hu, w, hw, huw⟩
  have h4 : f '' u ×ˢ w ⊆ V := subset_trans (Set.image_subset f huw) (Set.image_preimage_subset f V)
  have := TopologicalSpace.ext_iff_nhds.mp htopg.topology_eq_generate_gnorm 0
  rcases (mem_nhds_induced gnormed.gnorm (0:𝕜) u).mp (this ▸ hu) with ⟨v, hv, huv⟩
  simp only [gnormed.norm_zero] at hv
  rcases mem_nhds_iff.mp hv with ⟨w, hwv, hwo, hw0⟩
  rcases IsOpen.exists_Ioo_subset hwo (Set.nonempty_of_mem hw0) with ⟨a, b, hab, habw⟩
  admit

end «Balanced sets»

-- ********************************************************************
section «Separation properties»

variable (ν : Type*) [StrictOrderedSemiring ν]
variable (𝕜 : Type*) [Field 𝕜] [GNormed 𝕜 ν]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

theorem separate_compact_closed (K C : Set V) : True := by admit



end «Separation properties»
-- ********************************************************************
