/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere

set_option diagnostics.threshold 100

/-! # The Riemann sphere — carrier and inherited topology

This file declares the **Riemann sphere** as the type abbreviation
`RiemannSphere := OnePoint ℂ` and records the inherited
`CompactSpace` / `T2Space` / `ConnectedSpace` instances.

## Scope of this file

This is the minimal, CI-green slice of the planned manifold module. It ships:

* `JacobianChallenge.RiemannSphere` — type abbreviation for `OnePoint ℂ`,
  carrying the one-point compactification topology.
* Inherited `CompactSpace`, `T2Space`, `ConnectedSpace` instances, recorded
  as `example` declarations so the file fails fast if mathlib's `OnePoint`
  API ever drops them.

## Deferred to follow-up files

The planned next steps — building an explicit two-chart atlas
(`chartN`, `chartS`) as `OpenPartialHomeomorph`s, packaging them into a
`ChartedSpace ℂ RiemannSphere` instance, proving analytic compatibility of
the four atlas-pair transitions, and synthesizing
`IsManifold 𝓘(ℂ) ω RiemannSphere` — were drafted in an earlier 419-LOC
draft (commit `e366489` on `feat/riemann-sphere`) but did not survive
mathlib pin `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`: the draft used
several lemma names that don't exist at this pin
(`Filter.tendsto_inv_nhdsNE_zero`, `nhdsWithin_compl_singleton_sup_pure`,
unqualified `cobounded`) and exposed a `Decidable (x = ∞)` instance gap
in `chartAtFun`. Rather than ship `sorry`s — which violates this repo's
hard rule (`DEVELOPMENT.md`) — those pieces are dropped here and left for
a separate PR that can stage each chart-construction step against CI in
isolation. -/

open OnePoint

namespace JacobianChallenge

/-- The **Riemann sphere**: the one-point compactification of `ℂ`. As a type,
this is `Option ℂ` with the compactification topology making it compact,
Hausdorff, and connected. -/
abbrev RiemannSphere : Type := OnePoint ℂ

namespace RiemannSphere

/-- Compactness of the Riemann sphere — inherited from
`OnePoint.instCompactSpace`. -/
example : CompactSpace RiemannSphere := inferInstance

/-- Hausdorff property — inherited from `OnePoint`'s `T2Space` instance,
which applies because `ℂ` is weakly locally compact and Hausdorff. -/
example : T2Space RiemannSphere := inferInstance

/-- Connectedness — inherited because `ℂ` is preconnected and noncompact. -/
example : ConnectedSpace RiemannSphere := inferInstance

end RiemannSphere

end JacobianChallenge
