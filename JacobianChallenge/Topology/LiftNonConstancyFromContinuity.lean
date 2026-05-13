/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiftMeroOrderFromContinuity

set_option diagnostics.threshold 100

/-! # Pointwise `germLimitLift g = g` under at-pole germ-compatibility,
and the resulting non-constancy preservation

zz362's `LiftDecomposition` lists input (v) `LiftNotConstant` as a
**non-constancy** preservation: if `g` is non-constant, so is
`germLimitLift g`. Under `IsBoundedByDeltaPContinuous` alone, the
"blip at `p`" counterexample remains: `g` may equal a constant `c` on
`X \ {p}` while `g(p) ≠ c`, in which case `g` is non-constant but
`germLimitLift g` is the constant function `c`.

The natural fix is one further strengthening: at-pole germ-compatibility,
asserting that whenever `g` has a punctured-nhd limit at `p`, then
`g(p)` equals that limit. Under the combined strengthening
`IsBoundedByDeltaPContinuousAtPole`, `germLimitLift g = g` as a
function, so non-constancy preservation is immediate.

## What this file delivers

* `IsBoundedByDeltaPContinuousAtPole p g` — the conjunction of
  `IsBoundedByDeltaPContinuous X p g` with the at-pole compatibility
  `∀ c, Tendsto g (𝓝[≠] p) (𝓝 c) → g p = c`.
* `germLimitLift_eq_self_at_pole_of_continuousAtPole` — pointwise
  identity at `p` from the at-pole compatibility.
* `germLimitLift_eq_self_everywhere_of_continuousAtPole` — pointwise
  identity at every `x`.
* `germLimitLift_eq_self_of_continuousAtPole` — functional identity
  `germLimitLift g = g`.
* `not_isConstantMap_germLimitLift_of_continuousAtPole_of_non_const` —
  the substantive non-constancy transport: under the strengthened
  predicate, non-constancy of `g` carries to `germLimitLift g`.

(The literal `LiftNotConstant X` of `LiftDecomposition` quantifies over
all `g`, not just those in L(δp); composing this chip's substantive
lemma into the literal signature is a small follow-up packaging chip
that pairs with the eventual germ-field refactor of `LiftDecomposition`.)

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **At-pole-germ-compatible `L(δp)` membership.** Adds to
`IsBoundedByDeltaPContinuous` the condition that if `g` has a
punctured-nhd limit at the marked pole `p`, then `g(p)` equals that
limit. Operationally eliminates the "blip at `p`" counterexample. -/
def IsBoundedByDeltaPContinuousAtPole (p : X) (g : X → ℂ) : Prop :=
  IsBoundedByDeltaPContinuous X p g ∧
    ∀ c : ℂ, Filter.Tendsto g (𝓝[≠] p) (𝓝 c) → g p = c

variable {X}

/-- **Forgetful map** back to `IsBoundedByDeltaPContinuous`. -/
lemma IsBoundedByDeltaPContinuousAtPole.toContinuous
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuousAtPole X p g) :
    IsBoundedByDeltaPContinuous X p g := h.1

/-- **Forgetful map** all the way back to `IsBoundedByDeltaP`. -/
lemma IsBoundedByDeltaPContinuousAtPole.toIsBoundedByDeltaP
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuousAtPole X p g) :
    IsBoundedByDeltaP p g := h.1.1

/-- **At-pole compatibility** extracted. -/
lemma IsBoundedByDeltaPContinuousAtPole.value_eq_limit
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuousAtPole X p g)
    {c : ℂ} (htend : Filter.Tendsto g (𝓝[≠] p) (𝓝 c)) :
    g p = c := h.2 c htend

/-! ## `germLimitLift g = g` pointwise under the strengthened predicate -/

/-- **Pointwise identity at `p` under the at-pole compatibility.** If
`g` has a punctured-nhd limit at `p`, then `germLimitLift g p = g p`
because both equal that common limit. If `g` has no limit at `p`,
`germLimitLift g p = g p` directly by
`MeromorphicNonzero.germLimit_eq_self_of_not_tendsto`. -/
lemma germLimitLift_eq_self_at_pole_of_continuousAtPole
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuousAtPole X p g) :
    germLimitLift g p = g p := by
  show MeromorphicNonzero.germLimit g p = g p
  by_cases hex : ∃ c : ℂ, Filter.Tendsto g (𝓝[≠] p) (𝓝 c)
  · obtain ⟨c, htend⟩ := hex
    rw [MeromorphicNonzero.germLimit_eq_of_tendsto htend]
    exact (h.value_eq_limit htend).symm
  · exact MeromorphicNonzero.germLimit_eq_self_of_not_tendsto hex

/-- **Pointwise identity at every `x` under the at-pole strengthening.**
For `x ≠ p`, off-pole continuity gives the identity via
`germLimitLift_eq_self_off_pole`. For `x = p`, the at-pole compatibility
gives it via the previous lemma. -/
lemma germLimitLift_eq_self_everywhere_of_continuousAtPole
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuousAtPole X p g)
    (x : X) :
    germLimitLift g x = g x := by
  by_cases hxp : x = p
  · subst hxp
    exact germLimitLift_eq_self_at_pole_of_continuousAtPole h
  · exact germLimitLift_eq_self_off_pole h.1.continuousAt_off_forall hxp

/-- **Functional identity `germLimitLift g = g`** under the
strengthened predicate. -/
theorem germLimitLift_eq_self_of_continuousAtPole
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuousAtPole X p g) :
    germLimitLift g = g := by
  funext x
  exact germLimitLift_eq_self_everywhere_of_continuousAtPole h x

/-! ## Non-constancy transport -/

/-- **Substantive non-constancy transport.** Under the strengthened
predicate, `germLimitLift g = g` as functions, so non-constancy of `g`
carries to non-constancy of `germLimitLift g`. The result is stated
relative to `IsConstantMap`, the predicate from
`Manifold/IsConstantMap.lean`. -/
theorem not_isConstantMap_germLimitLift_of_continuousAtPole_of_non_const
    {p : X} {g : X → ℂ} (h : IsBoundedByDeltaPContinuousAtPole X p g)
    (h_nc : g ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ))) :
    ¬ JacobianChallenge.IsConstantMap (germLimitLift g) := by
  -- Under the strengthened predicate, `germLimitLift g = g`.
  rw [germLimitLift_eq_self_of_continuousAtPole h]
  -- Reduce ¬ IsConstantMap g to "g is not in span ℂ {1}" — direct
  -- equivalence: `IsConstantMap` is "exists c, g = const c", which
  -- is equivalent to membership in the constants submodule.
  intro hconst
  apply h_nc
  obtain ⟨c, hc⟩ := hconst
  -- `hc : g = fun _ => c`. Express as `c • 1`.
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  funext x
  show c • (1 : X → ℂ) x = g x
  simp [hc]

/-! ## Bundled discharge for downstream consumers

A consumer file that supplies a witness of
`IsBoundedByDeltaPContinuousAtPole p g` for the specific `g ∈ L(δp)`
of interest immediately obtains both `germLimitLift g = g` (functional
identity, useful for further preservation arguments) and the
non-constancy transport. The composition with the previous chips
(continuity off `p` discharges (i)/(iii)/(iv) of the five-fold
LiftDecomposition; at-pole compatibility discharges (v)) reduces the
five-input split to two named hypotheses:

* the universal continuity-off-`p` strengthening
  (`IsBoundedByDeltaPContinuousAtPole`-style witness for every g ∈
  L(δp)), and
* the identity theorem for meromorphic functions on connected complex
  1-manifolds (for input (ii) `LiftNonvanishingGerm`).

The first is the germ-field refactor in operational form; the second
is classical content not at the mathlib pin. Both are precise textbook
citables.
-/

end JacobianChallenge

end
