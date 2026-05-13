/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.ExistsMeroSimplePoleSplit
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.MeromorphicAt
import Mathlib.Topology.LocallyConstant.Basic

set_option diagnostics.threshold 100

/-! # `LiouvilleOnCompactConnected X` from local constancy of holomorphics

This chip reduces zz346's `LiouvilleOnCompactConnected X` to a more
elementary statement: any holomorphic (`order ≥ 0` everywhere)
`MeromorphicNonzero X` function on a compact connected complex
1-manifold is **locally constant**.

The reduction is mechanical: `ConnectedSpace X` extends
`PreconnectedSpace X`, so mathlib's
`IsLocallyConstant.eq_const` immediately gives global constancy.

The remaining open input — local constancy — is the **max-modulus**
classical content (the value-modulus is forced to be constant by
max-mod; then the open-mapping theorem for analytic functions
upgrades the constant-modulus conclusion to constant-value local
constancy). This is in reach of mathlib's
`Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm` +
`Complex.norm_eventually_eq_of_isLocalMax` + chart-wise reduction,
and a follow-up chip can attack it.

## What this chip ships

* `HolomorphicLocallyConstant X` (named hypothesis) — the
  max-modulus consequence, see docstring.

* `liouvilleOnCompactConnected_of_holomorphicLocallyConstant` —
  composition theorem reducing zz346's `LiouvilleOnCompactConnected X`
  to the named hypothesis.

* `riemannRochGenusZero_from_existence_RR_and_localConstancy` —
  the full chain back to `RiemannRochGenusZero X` from
  `ExistsNonConstantBoundedByDeltaP_GenusZero X` +
  `HolomorphicLocallyConstant X`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named hypothesis: holomorphic functions on `X` are locally
constant.**

Classical max-modulus content: a holomorphic function on a compact
connected complex 1-manifold has constant modulus on `X` (because
the modulus achieves its max at some `c`, the max-mod principle
forces local constancy in a chart, and the set where the max is
attained is clopen in connected `X`); the open-mapping theorem then
upgrades constant-modulus to constant-value, hence locally constant
(in fact globally constant, but locally constant is the natural
intermediate).

For non-zero meromorphic `f` with order `≥ 0` everywhere (genuinely
holomorphic), this gives `IsLocallyConstant f.toFun`. -/
def HolomorphicLocallyConstant : Prop :=
  ∀ (f : MeromorphicNonzero X),
    (∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) →
    IsLocallyConstant f.toFun

/-- **`LiouvilleOnCompactConnected X` from `HolomorphicLocallyConstant
X`.** Composition via mathlib's `IsLocallyConstant.eq_const` on
`PreconnectedSpace X` (auto from `ConnectedSpace X`). -/
theorem liouvilleOnCompactConnected_of_holomorphicLocallyConstant
    (h : HolomorphicLocallyConstant X) :
    LiouvilleOnCompactConnected X := by
  intro f h_holo
  -- f.toFun is locally constant.
  have h_lc : IsLocallyConstant f.toFun := h f h_holo
  -- Pick any point x : X (X is nonempty as a CompactSpace + ConnectedSpace).
  -- Get a base x : X via the global `Inhabited` provided by `ConnectedSpace`
  -- (which requires nonempty). Use `Classical.choice` of `Nonempty X`.
  haveI : Nonempty X := inferInstance
  -- IsLocallyConstant on a PreconnectedSpace ⇒ all values equal.
  -- Use `IsLocallyConstant.eq_const`.
  classical
  let x₀ := Classical.choice (inferInstance : Nonempty X)
  -- IsLocallyConstant on PreconnectedSpace ⇒ f = Function.const _ (f x₀).
  have h_const : f.toFun = Function.const X (f.toFun x₀) := h_lc.eq_const x₀
  -- For any y : X, f.toFun y = f.toFun x₀.
  refine ⟨f.toFun x₀, ?_⟩
  intro x
  exact congr_fun h_const x

/-- **Final chain: RiemannRochGenusZero X from the genuinely open
classical input + local-constancy hypothesis.** -/
theorem riemannRochGenusZero_from_existence_RR_and_localConstancy
    (hA : ExistsNonConstantBoundedByDeltaP_GenusZero X)
    (hLC : HolomorphicLocallyConstant X) :
    RiemannRochGenusZero X :=
  riemannRochGenusZero_from_split X hA
    (liouvilleOnCompactConnected_of_holomorphicLocallyConstant X hLC)

end JacobianChallenge

end
