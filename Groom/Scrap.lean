import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced


import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced

open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) :=
begin
  -- Assume x1 and x2 are elements of X such that g (f x1) = g (f x2)
  intros x1 x2 h,
  -- Since g is injective, we have f x1 = f x2
  apply hf,
  apply hg,
  exact h,
end
