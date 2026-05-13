/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDeltaP

set_option diagnostics.threshold 100

/-! # API extraction lemmas for `IsBoundedByDeltaP` / `linearSystemDeltaP`

`IsBoundedByDeltaP p f` is structurally `⟨MMeromorphicOn ..., ord ≥ 0
off p, ord ≥ -1 at p⟩`. This file exposes each component as a named
lemma so downstream consumers don't need to repeatedly unpack the
conjunction.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace IsBoundedByDeltaP

/-- Component 1: `f` is meromorphic on all of `X`. -/
lemma mmeromorphicOn {p : X} {f : X → ℂ}
    (h : IsBoundedByDeltaP p f) :
    MMeromorphicOn (𝓘(ℂ, ℂ)) f Set.univ := h.1

/-- Component 2: at every `x ≠ p`, `f` has non-negative order. -/
lemma order_nonneg_off {p : X} {f : X → ℂ}
    (h : IsBoundedByDeltaP p f) :
    ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f x := h.2.1

/-- Component 3: at `p`, `f` has order at least `-1`. -/
lemma order_ge_neg_one_at_p {p : X} {f : X → ℂ}
    (h : IsBoundedByDeltaP p f) :
    ((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f p := h.2.2

/-- `MMeromorphicAt` at every point (specialisation of
`mmeromorphicOn`). -/
lemma mmeromorphicAt {p : X} {f : X → ℂ}
    (h : IsBoundedByDeltaP p f) (x : X) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) f x :=
  h.mmeromorphicOn x (Set.mem_univ x)

end IsBoundedByDeltaP

namespace linearSystemDeltaP

/-- Membership API: extract `IsBoundedByDeltaP`. -/
lemma mem_iff {p : X} {f : X → ℂ} :
    f ∈ linearSystemDeltaP p ↔ IsBoundedByDeltaP p f := Iff.rfl

end linearSystemDeltaP

end JacobianChallenge

end
