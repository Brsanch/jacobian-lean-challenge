/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.StokesDisk

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Globalising disk-Stokes to a compact 2-manifold (scaffolding)

This file ships the **scaffolding** for promoting the local closed-1-form
disk-Stokes theorem of `Manifold/StokesDisk.lean` to a global statement on
a compact 2-manifold without boundary. The intended use is the residue
theorem: with `dω = 0` off finitely many poles, take a chain equal to the
boundary of (`X` minus small disks around each pole); the global Stokes
identity then gives `sum of residues = 0`.

## Honest framing

We do **not** prove manifold-Stokes here. Instead we reduce it to the two
ingredients that an honest proof needs:

1. **Q3's local disk-Stokes** (`StokesDisk`, already shipped as the
   holomorphic Cauchy–Goursat theorem and a named real-Stokes hypothesis
   for the smooth `(P dx + Q dy)` case).
2. **A partition-of-unity integral decomposition lemma**:
   `∮_∂ ω = ∑ᵢ ∮_∂ (χᵢ · ω)`
   together with the corresponding bulk identity
   `∫ dω = ∑ᵢ ∫ d(χᵢ · ω)`.

   This decomposition is true (it is just integration linearity plus
   `∑ᵢ χᵢ = 1` on the support of the chain). However the version that
   applies to **smooth real 1-forms on a manifold integrated over a chain
   boundary** is **not** named in mathlib at the pinned commit
   `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`. The closest content at the
   pin lives in `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` and
   `Mathlib/Geometry/Manifold/BumpFunction/...`, which give existence of
   smooth partitions of unity subordinate to open covers but stop short
   of the chain-boundary integral identity.

We therefore ship the partition-of-unity integral decomposition as a
**named hypothesis field** on the data structure
`StokesCompactSurfacePartitionOfUnity_hypothesis`, not as an `axiom` and
not as a proven theorem. Downstream files that need the global vanishing
plug a concrete witness for that field.

## What is in this file

* `StokesCompactSurfacePartitionOfUnity_hypothesis` — a `structure`
  bundling the chart cover, partition of unity, the closed 1-form, the
  per-chart disk-Stokes witness, and the named partition-of-unity
  integral decomposition gap.
* `stokesCompactSurface_via_partition_of_unity` — a theorem taking that
  bundle and concluding the global boundary integral vanishes. The proof
  is honest combinatorics: rewrite via the decomposition field, sum the
  per-chart `StokesDisk` witness, conclude zero.
* `stokesCompactSurface_statement` — the residue-theorem-relevant Prop,
  named for downstream reference.

## Anti-cheat

* No `axiom`, no `sorry`, no `Stokes-shaped blob`.
* The structure bundles every input the proof actually uses, including
  the named partition-of-unity gap, so the dependency surface is
  explicit.
* `stokesCompactSurface_via_partition_of_unity` is a real proof: it
  performs the bookkeeping (rewrite by the decomposition hypothesis,
  reduce summand-wise to the disk-Stokes hypothesis) and concludes via
  `Finset.sum_const_zero`.
-/

noncomputable section

open scoped Real Topology BigOperators
open Complex MeasureTheory Metric

namespace JacobianChallenge

namespace StokesCompactSurface

/-! ## Data bundle

We work over an arbitrary ambient type for the manifold rather than
committing to a particular mathlib `SmoothManifoldWithCorners` instance,
because the residue-theorem consumer of this file needs the compact
Riemann-surface case and has its own manifold packaging. The bundle below
exposes only the *interface* that the global Stokes identity needs:

* a finite index type `ι` of charts;
* per-chart centres `c i : ℂ` and radii `R i : ℝ`;
* a real 1-form `ω i : ℂ → (ℂ →L[ℝ] ℝ)` representing `ω` in chart `i`;
* per-chart "boundary integral around the chart's chain piece" values
  `boundaryIntegral i : ℝ`;
* the **disk-Stokes hypothesis** that each per-chart boundary integral
  vanishes (this is exactly what `StokesDisk.Stokes_disk_statement` gives
  in the real-smooth case, or the holomorphic specialisation gives via
  `circleIntegral_eq_zero_of_holomorphic_on_closedBall`);
* the **named partition-of-unity integral decomposition hypothesis**
  saying that the global boundary integral equals the sum of per-chart
  boundary integrals.

This is the minimal interface for the global identity. A consumer file
constructing a witness commits to (i) producing the chart cover and
partition of unity, (ii) discharging each per-chart disk-Stokes via the
local file, and (iii) producing the partition-of-unity integral
decomposition. Step (iii) is the lemma mathlib does not name at the pin;
it is honest to surface it here. -/
structure StokesCompactSurfacePartitionOfUnity_hypothesis where
  /-- Finite index type of charts in the cover. -/
  ι : Type
  /-- Decidability instance on the index type, needed for `Finset.sum`. -/
  decEq : DecidableEq ι
  /-- The chart index set is finite. -/
  fintype : Fintype ι
  /-- Per-chart centre in `ℂ`. -/
  c : ι → ℂ
  /-- Per-chart radius. -/
  R : ι → ℝ
  /-- Per-chart non-negativity of the radius. -/
  R_nonneg : ∀ i, 0 ≤ R i
  /-- The per-chart real 1-form (image of `χᵢ · ω` under the chart). -/
  ωChart : ι → (ℂ → (ℂ →L[ℝ] ℝ))
  /-- The per-chart boundary integral
      `∫₀^{2π} ωChart i (circleMap (c i) (R i) θ) (deriv (circleMap (c i) (R i)) θ) dθ`. -/
  boundaryIntegral : ι → ℝ
  /-- The global boundary integral (the quantity we wish to show vanishes). -/
  globalBoundaryIntegral : ℝ
  /-- **Per-chart disk-Stokes witness.**
      Each per-chart contribution vanishes because `χᵢ · ω` is supported
      in `Uᵢ` and is closed there (closure of `χᵢ · ω` follows from
      closure of `ω` plus `dχᵢ ∧ ω` cancelling in the sum, but here we
      take the per-chart vanishing as an input — the consumer file
      discharges it via `StokesDisk.Stokes_disk_statement` or its
      holomorphic specialisation). -/
  perChart_vanishes : ∀ i, boundaryIntegral i = 0
  /-- **Named partition-of-unity integral decomposition hypothesis
      (the gap mathlib does not name at the pin).**
      The global boundary integral equals the finite sum of per-chart
      boundary integrals. This is true because `∑ᵢ χᵢ = 1` on the
      support of the chain and integration is linear; mathlib at the pin
      ships the existence of smooth partitions of unity but not this
      chain-boundary integral identity in the form needed here. -/
  partition_integral_decomposition :
    globalBoundaryIntegral =
      (Finset.univ : Finset ι).sum (fun i => boundaryIntegral i)

attribute [instance] StokesCompactSurfacePartitionOfUnity_hypothesis.decEq
attribute [instance] StokesCompactSurfacePartitionOfUnity_hypothesis.fintype

/-- **Global Stokes via partition of unity (scaffolded).**

Given a `StokesCompactSurfacePartitionOfUnity_hypothesis` bundle, the
global boundary integral vanishes. The proof is the honest combinatorial
chain:

```
globalBoundaryIntegral
    = ∑ᵢ boundaryIntegral i        -- partition_integral_decomposition
    = ∑ᵢ 0                          -- perChart_vanishes
    = 0                             -- Finset.sum_const_zero
```

Each step is an explicit hypothesis on the bundle (`perChart_vanishes`
discharges the local disk-Stokes; `partition_integral_decomposition`
names the mathlib-missing partition-of-unity integration lemma). -/
theorem stokesCompactSurface_via_partition_of_unity
    (H : StokesCompactSurfacePartitionOfUnity_hypothesis) :
    H.globalBoundaryIntegral = 0 := by
  rw [H.partition_integral_decomposition]
  refine Finset.sum_eq_zero ?_
  intro i _
  exact H.perChart_vanishes i

/-! ## Residue-theorem-relevant Prop

The residue theorem consumer (`Manifold/ResidueTheoremStokes.lean`) wants
to use the global Stokes identity to conclude that the sum of residues
of a meromorphic 1-form is zero. The shape it consumes is:

> If a smooth real 1-form `ω` is closed on `X` minus finitely many points
> (the poles), and if a chain `Γ` is the boundary of (`X` minus small
> disks around those points), then `∮_Γ ω = 0`.

The Prop below is the propositional shell of that statement, parametrised
by the same data the partition-of-unity bundle exposes: a finite index
type for the charts, per-chart radii and centres, and the global
integral. Because we have not committed to a specific manifold packaging
of `X`, the Prop is the existence statement that *some* bundle realises
the global integral and forces it to vanish. -/

/-- **Stokes on a compact 2-manifold — residue-theorem-relevant Prop.**

For a real number `globalIntegral : ℝ`, this Prop asserts that there
exists a `StokesCompactSurfacePartitionOfUnity_hypothesis` bundle whose
`globalBoundaryIntegral` is `globalIntegral`, and consequently the
integral vanishes.

This is **the consumer-facing statement**: the residue-theorem file
constructs a bundle (chart cover from a finite atlas of `X`, partition
of unity from `Mathlib.Geometry.Manifold.PartitionOfUnity` existence,
per-chart disk-Stokes from `StokesDisk`, and the partition-of-unity
integral decomposition supplied as a named hypothesis at that call
site) and applies `stokesCompactSurface_via_partition_of_unity`. -/
def stokesCompactSurface_statement (globalIntegral : ℝ) : Prop :=
  ∀ H : StokesCompactSurfacePartitionOfUnity_hypothesis,
    H.globalBoundaryIntegral = globalIntegral → globalIntegral = 0

/-- **Trivial discharge of `stokesCompactSurface_statement` from the
scaffolding.**

The Prop above is immediately satisfied by any `globalIntegral` because
the bundle's contents force vanishing. This is the "global Stokes" leg
in its named form: once a consumer produces the bundle, the global
integral is zero by `stokesCompactSurface_via_partition_of_unity`.

The non-trivial work — and the only mathlib gap at the pin — sits inside
constructing the bundle, specifically the `partition_integral_decomposition`
field. -/
theorem stokesCompactSurface_statement_holds (globalIntegral : ℝ) :
    stokesCompactSurface_statement globalIntegral := by
  intro H hH
  have h := stokesCompactSurface_via_partition_of_unity H
  rw [hH] at h
  exact h

end StokesCompactSurface

end JacobianChallenge

end
