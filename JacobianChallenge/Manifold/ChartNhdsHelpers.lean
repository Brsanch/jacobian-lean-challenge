/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Defs.Filter

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Small chart-source / nhds helper lemmas (Chip D infra)

This file collects the tiny `(chartAt H x).source ∈ 𝓝 x` /
`∈ 𝓝[≠] x` lemmas that get re-derived inline at many call sites in this
repository (e.g. `Manifold/MeromorphicExtension.lean`,
`Divisor/MeromorphicNonzeroGerm.lean`, `Divisor/PrincipalDivisor.lean`).

Each statement is a one-line corollary of either
`PartialHomeomorph.open_source.mem_nhds` (combined with `mem_chart_source`)
or `mem_nhdsWithin_of_mem_nhds`. They introduce **no new mathematical
content** — only stable named handles so call sites can `exact
chart_source_mem_nhds x` instead of repeating the two-line `have`.

Lemmas provided (all in the `JacobianChallenge` namespace):

* `chart_source_mem_nhds` — `(chartAt H x).source ∈ 𝓝 x`.
* `chart_source_mem_nhdsNE` — `(chartAt H x).source ∈ 𝓝[≠] x`.
* `chart_mem_source` — `x ∈ (chartAt H x).source` (rebrand of
  `mem_chart_source` so it is reachable through this helper file too).
* `chartAt_isOpen_source` — `IsOpen (chartAt H x).source` (ditto, for
  `PartialHomeomorph.open_source`).

No `axiom`, no `sorry`. Each body is at most one line.
-/

noncomputable section

open scoped Manifold Topology
open Filter Set

namespace JacobianChallenge

universe u v

variable {H : Type v} [TopologicalSpace H]
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]

/-- The chart source containing `x` is a neighbourhood of `x`. -/
lemma chart_source_mem_nhds (x : X) :
    (chartAt H x).source ∈ 𝓝 x :=
  (chartAt H x).open_source.mem_nhds (mem_chart_source H x)

/-- The chart source is a punctured neighbourhood of `x`. -/
lemma chart_source_mem_nhdsNE (x : X) :
    (chartAt H x).source ∈ 𝓝[≠] x :=
  mem_nhdsWithin_of_mem_nhds (chart_source_mem_nhds (H := H) x)

/-- `x` belongs to its own chart source. (Rebrand of `mem_chart_source`
reachable through this helper file.) -/
lemma chart_mem_source (x : X) : x ∈ (chartAt H x).source :=
  mem_chart_source H x

/-- The chart source is open. (Rebrand of
`PartialHomeomorph.open_source`.) -/
lemma chartAt_isOpen_source (x : X) : IsOpen (chartAt H x).source :=
  (chartAt H x).open_source

end JacobianChallenge
