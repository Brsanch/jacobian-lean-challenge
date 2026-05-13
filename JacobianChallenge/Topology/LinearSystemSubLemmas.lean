/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDeltaP
import JacobianChallenge.Topology.LinearSystemAPI

set_option diagnostics.threshold 100

/-! # Derived closure lemmas for `L(δp)`

This file ships the standard derived closure laws on
`IsBoundedByDeltaP`:

* `IsBoundedByDeltaP.neg` — `f ∈ L(δp) ⇒ -f ∈ L(δp)`. Direct from
  the scalar-mul closure (zz353) with `c = -1`.

* `IsBoundedByDeltaP.sub` — `f, g ∈ L(δp) ⇒ f - g ∈ L(δp)`. From add
  and neg closure.

These are mechanical consequences of zz352's `add`, `smul`, but
exposing them under conventional names lets downstream proofs avoid
re-deriving them inline.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace IsBoundedByDeltaP

/-- **Negation closure: `f ∈ L(δp) ⇒ -f ∈ L(δp)`.** -/
lemma neg {p : X} {f : X → ℂ}
    (hf : IsBoundedByDeltaP p f) :
    IsBoundedByDeltaP p (-f) := by
  -- `-f = (-1 : ℂ) • f`.
  have h_eq : (-f) = ((-1 : ℂ) • f) := by
    ext x; simp [Pi.smul_apply]
  rw [h_eq]
  exact IsBoundedByDeltaP.smul (-1 : ℂ) hf

/-- **Subtraction closure: `f, g ∈ L(δp) ⇒ f - g ∈ L(δp)`.** -/
lemma sub {p : X} {f g : X → ℂ}
    (hf : IsBoundedByDeltaP p f) (hg : IsBoundedByDeltaP p g) :
    IsBoundedByDeltaP p (f - g) := by
  have h_eq : (f - g) = f + (-g) := by
    ext x; simp [sub_eq_add_neg]
  rw [h_eq]
  exact IsBoundedByDeltaP.add hf (IsBoundedByDeltaP.neg hg)

end IsBoundedByDeltaP

namespace linearSystemDeltaP

/-- `-f ∈ linearSystemDeltaP p` when `f ∈ linearSystemDeltaP p`. -/
lemma neg_mem {p : X} {f : X → ℂ}
    (hf : f ∈ linearSystemDeltaP p) :
    -f ∈ linearSystemDeltaP p := IsBoundedByDeltaP.neg hf

/-- `f - g ∈ linearSystemDeltaP p` when both are. -/
lemma sub_mem {p : X} {f g : X → ℂ}
    (hf : f ∈ linearSystemDeltaP p) (hg : g ∈ linearSystemDeltaP p) :
    f - g ∈ linearSystemDeltaP p := IsBoundedByDeltaP.sub hf hg

end linearSystemDeltaP

end JacobianChallenge

end
