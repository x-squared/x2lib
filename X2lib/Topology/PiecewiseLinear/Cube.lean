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
import Mathlib.Topology.Algebra.Affine
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.LinearAlgebra.Ray

import X2lib.Topology.PiecewiseLinear.Affine
import X2lib.Topology.PiecewiseLinear.Module

/-!
# Cubes



## Main results

- `exists_foo`: the main existence theorem of `foo`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Rourke] for ann introduction to PL-topology.
-/

universe u v w
open Set
open BigOperators

-- ********************************************************************
section «Affine Cube definition»

/-!
## Affine Cube

TODO. -/

variable (𝕜 : Type u) [LinearOrderedField 𝕜]

namespace Affine

namespace Cube

def xxx : ℕ := 0
def ui := unitInterval

end Cube

structure Cube
    {V : Type v} [AddCommGroup V] [Module 𝕜 V]
    (P : Type w) [AddTorsor V P]
    (n : ℕ) where
  base : Fin (n + 1) → P
  independent : AffineIndependent 𝕜 base
  base_point : P := base 0
  base_point_def : base_point = base 0 := by rfl
  carrier : Set P := { base_point }
  carrier_def : carrier = { base_point } := by rfl

end Affine

end «Affine Cube definition»

-- ********************************************************************
section «Affine Cube basics»

/-!
## Affine Cube

TODO. -/

variable {𝕜 : Type u} [LinearOrderedField 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type w} [AddTorsor V P]

namespace Affine.Cube

def vertices (c : Cube 𝕜 P n) : Set P := { p | ∃ w : Fin n → 𝕜, ∀ i, (w i) ∈ ({0, 1} : Set 𝕜) ∧ p = (∑ i, (w i) • (c.base (Fin.addNat i 1) -ᵥ c.base_point)) +ᵥ c.base_point}

def vec (c : Cube 𝕜 P n) : V := c.base_point -ᵥ c.base_point

end Affine.Cube

end «Affine Cube basics»

-- ********************************************************************
section «Affine Cube neighbourhood»

/-!
## Affine Cube

TODO. -/

namespace Affine.Cube

structure CubeNhd
    (𝕜 : Type u) [LinearOrderedField 𝕜]
    {V : Type v} [AddCommGroup V] [Module 𝕜 V]
    (P : Type w) [AddTorsor V P]
    (n : ℕ) extends Cube 𝕜 P n where
  test : carrier = { base_point }

end Affine.Cube

end «Affine Cube neighbourhood»
