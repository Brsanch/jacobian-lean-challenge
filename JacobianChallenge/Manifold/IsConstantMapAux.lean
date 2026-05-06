/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalMultiplicity

/-! # Auxiliary helpers for `JacobianChallenge.IsConstantMap`

The base predicate

```
def IsConstantMap (f : X → Y) : Prop := ∃ y, ∀ x, f x = y
```

lives in `JacobianChallenge.Manifold.LocalMultiplicity`, together with two
basic facts:

* `isConstantMap_const : IsConstantMap (fun _ => c)`
* `not_isConstantMap_iff : ¬ IsConstantMap f ↔ ∀ y, ∃ x, f x ≠ y`

This file collects further bookkeeping lemmas that downstream consumers
(`AnalyticContinuationGlobalization`, `AnalyticFiberDiscrete`,
`Degree`) end up re-deriving inline. The lemmas here are pure logic /
equality manipulation; no manifold or analytic content.
-/

noncomputable section

namespace JacobianChallenge

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- A non-constant map admits a *witness pair* `x₁, x₂` with `f x₁ ≠ f x₂`.
This is the form most useful when one already has a candidate point and
needs to find a *second* point that disagrees with it.

The forward direction needs `[Nonempty X]` to pick an anchor; without it,
any function on an empty domain is constant (with witness any `y : Y`,
provided one exists), so the existence of a witness pair fails. -/
lemma not_isConstantMap_iff_exists_pair [Nonempty X] {f : X → Y} :
    ¬ IsConstantMap f ↔ ∃ x₁ x₂ : X, f x₁ ≠ f x₂ := by
  constructor
  · intro h
    rw [not_isConstantMap_iff] at h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    obtain ⟨x₁, hx₁⟩ := h (f x₀)
    exact ⟨x₁, x₀, hx₁⟩
  · rintro ⟨x₁, x₂, hx⟩ ⟨y, hy⟩
    exact hx ((hy x₁).trans (hy x₂).symm)

/-- Constant-map predicate is preserved by composition on the right with any
function: if `f` is constant, so is `f ∘ g`. -/
lemma IsConstantMap.comp_right {f : X → Y} (hf : IsConstantMap f) (g : Z → X) :
    IsConstantMap (f ∘ g) := by
  obtain ⟨y, hy⟩ := hf
  exact ⟨y, fun z => hy (g z)⟩

/-- Constant-map predicate is preserved by composition on the left with any
function: if `f` is constant, so is `g ∘ f`. -/
lemma IsConstantMap.comp_left {f : X → Y} (hf : IsConstantMap f) (g : Y → Z) :
    IsConstantMap (g ∘ f) := by
  obtain ⟨y, hy⟩ := hf
  refine ⟨g y, fun x => ?_⟩
  simp [Function.comp, hy x]

/-- Restated form of `not_isConstantMap_iff`: a non-constant map misses,
for every prospective value `y`, at least one input. -/
lemma exists_ne_of_not_isConstantMap {f : X → Y} (hf : ¬ IsConstantMap f)
    (y : Y) : ∃ x, f x ≠ y :=
  (not_isConstantMap_iff f).1 hf y

/-- Symmetric form: a non-constant map admits, for every input `x`, some
*other* input whose value disagrees. The existence of such a `y` follows by
applying `not_isConstantMap_iff` at the value `f x`. -/
lemma exists_value_ne_of_not_isConstantMap {f : X → Y} (hf : ¬ IsConstantMap f)
    (x : X) : ∃ y, f y ≠ f x :=
  (not_isConstantMap_iff f).1 hf (f x)

/-- If two functions agree pointwise, then one is constant iff the other is.
Useful when handling chart pullbacks where `f` and a "rewritten" `f'` agree
extensionally but not definitionally. -/
lemma isConstantMap_congr {f g : X → Y} (h : ∀ x, f x = g x) :
    IsConstantMap f ↔ IsConstantMap g := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, fun x => (h x).symm.trans (hy x)⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, fun x => (h x).trans (hy x)⟩

/-- The constant function with value `c` has range `{c}` when the domain
is nonempty. -/
lemma range_const_of_nonempty [Nonempty X] (c : Y) :
    Set.range (fun _ : X => c) = {c} := by
  ext y
  simp [Set.mem_range, eq_comm]

/-- A map on a nonempty domain is constant iff its range is a singleton.
This is a sharper version of "subsingleton range" for the inhabited case
that the challenge always lives in. -/
lemma isConstantMap_iff_range_singleton [Nonempty X] {f : X → Y} :
    IsConstantMap f ↔ ∃ y, Set.range f = {y} := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      simp [hy x]
    · rintro rfl
      obtain ⟨x₀⟩ := ‹Nonempty X›
      exact ⟨x₀, hy x₀⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, fun x => ?_⟩
    have hx : f x ∈ Set.range f := ⟨x, rfl⟩
    rw [hy] at hx
    exact hx

/-- A map is constant iff any two outputs agree. The forward direction uses
`isConstantMap_const`-style chasing; the backward direction needs `[Nonempty
X]` to anchor the existential. -/
lemma isConstantMap_iff_forall_eq [Nonempty X] {f : X → Y} :
    IsConstantMap f ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  constructor
  · rintro ⟨y, hy⟩ x₁ x₂
    rw [hy x₁, hy x₂]
  · intro h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact ⟨f x₀, fun x => h x x₀⟩

end JacobianChallenge

end
