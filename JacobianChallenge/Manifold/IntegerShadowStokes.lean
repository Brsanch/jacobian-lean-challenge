/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GlobalChainBoundaryDischarge
import JacobianChallenge.Manifold.StokesCompactSurface

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Integer-shadow Stokes for closed compact 2-manifolds (ZZ71 chip)

This file attacks the **integer-shadow Stokes content** that powers the
last-mile reduction in `GlobalChainBoundaryDischarge.lean`. Concretely we
give a *combinatorial* version of "the sum of inward-pointing chart-circle
integers around small balls cut out of a closed surface is zero" — the
content that survives once one strips Stokes of its real-analytic flesh
and keeps only the integer winding numbers around each chart's boundary.

## What integer Stokes really says on a closed surface

On a triangulated closed compact 2-manifold without boundary, every
interior edge is shared by exactly two faces with **opposite** induced
orientations. If one assigns each face an integer "boundary integer"
that decomposes as a sum of integer "edge contributions" with sign
flipping under orientation reversal, then the global face sum
telescopes by pairwise edge cancellation and equals zero.

This is the **integer shadow** of Stokes: the real `∫ d(log f) = 0`
identity on `X ∖ ⋃ B_x` reduces, after pulling out the chart structure
and dividing by `2πi`, to the integer cancellation
`∑_{F ∈ Faces} boundaryInt(F) = 0`.

The faces fall into two kinds: *singular* faces (one per support point
of `f`, contributing the integer order `ord_x f`) and *regular* faces
(every chart not containing a zero/pole, contributing `0` by closed-form
Stokes — `StokesDiskClosedForm`). Their sum is then `∑_{x ∈ S} ord_x f`,
which the cancellation forces to be zero.

## What this file proves vs. what it reduces to

* `IntegerShadowChainComplex` — a **structure** bundling exactly the
  combinatorial data needed: a finite face set, a finite edge set, a
  signed face-edge incidence, and the **edge cancellation hypothesis**
  (each edge's incidences sum to zero across its two adjacent faces).
* `IntegerShadowChainComplex.boundaryInt_sum_eq_zero` — **proven, no
  `sorry`, no `axiom`**: under the bundled cancellation hypothesis, the
  global sum of face boundary integers is `0`. The proof is honest
  finite-sum manipulation (Fubini swap on `Face × Edge`, then per-edge
  cancellation).
* `chartIntegralFibreBalanceOn_of_integerShadow` — **proven** wrapper:
  if the integer-shadow chain complex realises the bundle's
  `chartIntegral` data on the support, then the chart-integer fibre
  balance from `GlobalChainBoundaryDischarge` follows.

The remaining geometric content (constructing the triangulation +
edge cancellation witness from a chart cover of `X`) is **named** as
the hypothesis fields of `IntegerShadowChainComplex`; this file does
not produce a triangulation of an arbitrary compact 2-manifold from
mathlib.

## Honest framing

* **No `axiom`, no `sorry`.** No signature change anywhere else.
* This is a **strictly smaller reduction** than the chart-integer
  fibre balance: the cancellation step is now a single named
  combinatorial hypothesis (`edge_cancellation`) on a finite signed
  incidence — not a chart-cover-and-Stokes hypothesis.
* The geometric inputs that *would* discharge `edge_cancellation`
  (triangulation of a closed surface, induced edge orientations on
  shared faces) are classical but not bundled in mathlib at the pin.
  See the "missing-mathlib content" docstring at the bottom of this
  file for the precise gap.
-/

noncomputable section

open scoped BigOperators

namespace JacobianChallenge

namespace IntegerShadowStokes

universe u

/-! ## The combinatorial integer-shadow chain complex

We capture the cancellation argument purely on integer-valued data.
The mental model:

* `Face` — a finite type whose elements are the closed pieces of a
  triangulation of `X` after cutting out small disks around each
  support point of `f`. Some faces are *singular* (one per support
  point, contributing `ord_x f`); the rest are regular (chart-disks
  not enclosing any singularity, contributing `0` by closed-form
  disk-Stokes).

* `Edge` — a finite type whose elements are the **oriented interior
  edges** of the triangulation, each shared by exactly two faces.

* `incidence F e` — the signed integer that face `F` contributes to
  the boundary integer along edge `e`. The cancellation hypothesis
  says that for each edge `e`, summing `incidence F e` across all
  faces adjacent to `e` (in fact across the whole `Face` finite type;
  faces not adjacent to `e` contribute `0`) yields `0`.

* `boundaryInt F` — the chart-circle integer of face `F`, defined as
  `∑_e incidence F e`.

The conclusion: `∑_F boundaryInt F = 0`.
-/

/-- **Integer-shadow chain complex.** Pure-integer data carrying
exactly the cancellation argument the residue theorem needs on a
closed compact 2-manifold. -/
structure IntegerShadowChainComplex where
  /-- Finite type of faces (regular charts ∪ singular cut-out disks). -/
  Face : Type
  /-- Finite type of (oriented) interior edges of the triangulation. -/
  Edge : Type
  /-- Decidable equality on `Face`, needed for `Finset.sum` over `Face × Edge`. -/
  decEqFace : DecidableEq Face
  /-- Decidable equality on `Edge`. -/
  decEqEdge : DecidableEq Edge
  /-- Faces are finite. -/
  fintypeFace : Fintype Face
  /-- Edges are finite. -/
  fintypeEdge : Fintype Edge
  /-- Signed face-edge incidence. -/
  incidence : Face → Edge → ℤ
  /-- **Edge cancellation hypothesis** — the integer-shadow Stokes content.
      For each interior edge `e`, the sum across faces of the signed
      incidence is `0`. On a triangulation of a closed surface this
      holds because each interior edge is shared by exactly two faces
      with opposite induced orientations. -/
  edge_cancellation : ∀ e : Edge,
    (Finset.univ : Finset Face).sum (fun F => incidence F e) = 0

attribute [instance] IntegerShadowChainComplex.decEqFace
attribute [instance] IntegerShadowChainComplex.decEqEdge
attribute [instance] IntegerShadowChainComplex.fintypeFace
attribute [instance] IntegerShadowChainComplex.fintypeEdge

namespace IntegerShadowChainComplex

/-- **Per-face boundary integer.** Sum of edge contributions of the
face `F`. Models the chart-circle integer of `d(log f)/(2πi)` around
the boundary of face `F` in the triangulation. -/
def boundaryInt (C : IntegerShadowChainComplex) (F : C.Face) : ℤ :=
  (Finset.univ : Finset C.Edge).sum (fun e => C.incidence F e)

/-- **Integer-shadow Stokes — main combinatorial identity.**

The sum of face boundary integers over a closed-surface triangulation
is zero: by Fubini swap and the per-edge cancellation hypothesis. -/
theorem boundaryInt_sum_eq_zero (C : IntegerShadowChainComplex) :
    (Finset.univ : Finset C.Face).sum (fun F => C.boundaryInt F) = 0 := by
  classical
  -- Expand `boundaryInt F = ∑_e incidence F e`.
  have hexpand :
      (Finset.univ : Finset C.Face).sum (fun F => C.boundaryInt F)
        = (Finset.univ : Finset C.Face).sum (fun F =>
            (Finset.univ : Finset C.Edge).sum (fun e => C.incidence F e)) := by
    apply Finset.sum_congr rfl
    intro F _
    rfl
  -- Fubini-swap to put the edge sum on the outside.
  have hswap :
      (Finset.univ : Finset C.Face).sum (fun F =>
        (Finset.univ : Finset C.Edge).sum (fun e => C.incidence F e))
        = (Finset.univ : Finset C.Edge).sum (fun e =>
            (Finset.univ : Finset C.Face).sum (fun F => C.incidence F e)) := by
    exact Finset.sum_comm
  -- Each inner sum is zero by `edge_cancellation`.
  have hinner :
      (Finset.univ : Finset C.Edge).sum (fun e =>
        (Finset.univ : Finset C.Face).sum (fun F => C.incidence F e)) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact C.edge_cancellation e
  rw [hexpand, hswap, hinner]

end IntegerShadowChainComplex

/-! ## Bridge to the chart-integer fibre balance

The `boundaryInt_sum_eq_zero` identity lands on `Face`-indexed sums.
The downstream gap in `GlobalChainBoundaryDischarge.lean` is on a
support-`Finset X` with a `chartIntegral : X → ℤ`. The bridge is the
hypothesis that the chain complex's faces are partitioned into
support-faces (one per `x ∈ S`, with `boundaryInt = chartIntegral x`)
and regular faces (with `boundaryInt = 0`). On those data, the global
sum collapses to `∑_{x ∈ S} chartIntegral x = 0`.
-/

/-- **Realisation of the chart-integer data by an integer-shadow chain complex.**

A `ChartIntegralRealisation S chartIntegral C` says: the chain complex
`C` has a distinguished injection `support : S ↪ C.Face` whose image
faces carry `boundaryInt = chartIntegral`, and every face outside the
image has `boundaryInt = 0`.

This packages the geometric content "small disks around each support
point are faces with chart-integer boundary; every other face is a
regular chart contributing zero" without committing to a particular
manifold packaging.
-/
structure ChartIntegralRealisation
    {X : Type u} (S : Finset X) (chartIntegral : X → ℤ)
    (C : IntegerShadowChainComplex) where
  /-- Map from support points to faces. -/
  support : X → C.Face
  /-- The map is injective on `S` (distinct support points give
      distinct singular faces). -/
  support_injOn : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S →
    support x = support y → x = y
  /-- The image of `support` on `S`. -/
  supportImage : Finset C.Face
  /-- `supportImage` is exactly the image. -/
  supportImage_eq : supportImage = S.image support
  /-- Singular faces carry the chart integer. -/
  boundaryInt_on_support : ∀ x ∈ S,
    C.boundaryInt (support x) = chartIntegral x
  /-- Regular faces (outside `supportImage`) contribute zero. -/
  boundaryInt_off_support : ∀ F : C.Face,
    F ∉ supportImage → C.boundaryInt F = 0

namespace ChartIntegralRealisation

/-- **Sum reduction.** The total face sum equals the support sum of
chart integers. -/
lemma face_sum_eq_support_sum
    {X : Type u} {S : Finset X} {chartIntegral : X → ℤ}
    {C : IntegerShadowChainComplex}
    (R : ChartIntegralRealisation S chartIntegral C) :
    (Finset.univ : Finset C.Face).sum (fun F => C.boundaryInt F)
      = ∑ x ∈ S, chartIntegral x := by
  classical
  -- Split the face sum by membership in `supportImage`.
  have hsplit :
      (Finset.univ : Finset C.Face).sum (fun F => C.boundaryInt F)
        = (R.supportImage.sum (fun F => C.boundaryInt F))
          + (Finset.univ.filter (fun F => F ∉ R.supportImage)).sum
              (fun F => C.boundaryInt F) := by
    -- Use `sum_filter_add_sum_filter_not` with predicate `F ∈ supportImage`.
    have hbase :
        (Finset.univ : Finset C.Face).sum (fun F => C.boundaryInt F)
          = (Finset.univ.filter (fun F => F ∈ R.supportImage)).sum
                (fun F => C.boundaryInt F)
            + (Finset.univ.filter (fun F => F ∉ R.supportImage)).sum
                (fun F => C.boundaryInt F) :=
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset C.Face))
        (p := fun F => F ∈ R.supportImage)
        (f := fun F => C.boundaryInt F)).symm
    -- Replace the first filter with `supportImage` itself.
    have hfilter_eq :
        (Finset.univ.filter (fun F => F ∈ R.supportImage))
          = R.supportImage := by
      ext F
      simp [Finset.mem_filter]
    rw [hbase, hfilter_eq]
  -- Off-support contributes zero.
  have hoff :
      (Finset.univ.filter (fun F => F ∉ R.supportImage)).sum
          (fun F => C.boundaryInt F) = 0 := by
    apply Finset.sum_eq_zero
    intro F hF
    rw [Finset.mem_filter] at hF
    exact R.boundaryInt_off_support F hF.2
  -- On-support sum equals `∑ x ∈ S, chartIntegral x` via the
  -- injective image lemma.
  have hsupport :
      R.supportImage.sum (fun F => C.boundaryInt F)
        = ∑ x ∈ S, chartIntegral x := by
    rw [R.supportImage_eq]
    rw [Finset.sum_image (fun x hx y hy h => R.support_injOn hx hy h)]
    apply Finset.sum_congr rfl
    intro x hx
    exact R.boundaryInt_on_support x hx
  rw [hsplit, hoff, hsupport, add_zero]

/-- **Headline reduction.** A realisation of the chart-integer data by
an integer-shadow chain complex implies the chart-integer-sum-zero
identity on `S`. -/
theorem chartIntegral_sum_eq_zero
    {X : Type u} {S : Finset X} {chartIntegral : X → ℤ}
    {C : IntegerShadowChainComplex}
    (R : ChartIntegralRealisation S chartIntegral C) :
    ∑ x ∈ S, chartIntegral x = 0 := by
  have hface := C.boundaryInt_sum_eq_zero
  have hbridge := R.face_sum_eq_support_sum
  -- `hbridge : face_sum = support_sum`; `hface : face_sum = 0`.
  -- So `support_sum = 0`.
  rw [← hbridge]
  exact hface

end ChartIntegralRealisation

/-! ## Wiring into `GlobalChainBoundaryDischarge` -/

/-- **Chart-integer fibre balance from an integer-shadow realisation.**

This is the consumer-facing reduction: any
`ChartIntegralRealisation S chartIntegral C` discharges the
`chartIntegralFibreBalanceOn` Prop from
`GlobalChainBoundaryDischarge.lean`.

This packages the full pairwise-edge-cancellation argument as a single
hypothesis bundle (`IntegerShadowChainComplex` + `ChartIntegralRealisation`)
and shows that the bundle implies the fibre-balance Prop the bundle
constructor of `mkBundle_of_chartIntegralFibreBalance` consumes. -/
theorem chartIntegralFibreBalanceOn_of_integerShadow
    {X : Type u} [DecidableEq X]
    {S : Finset X} {chartIntegral : X → ℤ}
    {C : IntegerShadowChainComplex}
    (R : ChartIntegralRealisation S chartIntegral C) :
    JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn
      S chartIntegral := by
  classical
  apply (JacobianChallenge.GlobalResidueSum.chartIntegralFibreBalanceOn_iff_sum_eq_zero
          S chartIntegral).mpr
  exact ChartIntegralRealisation.chartIntegral_sum_eq_zero R

/-! ## Missing-mathlib content (concrete gap)

What this file does **not** provide — the inputs that would close
`edge_cancellation` and `ChartIntegralRealisation` unconditionally on
a real compact connected complex 1-manifold `X`:

1. **A finite triangulation of `X`** as a finite simplicial complex
   whose underlying set is `X` and whose 2-cells partition `X` (up to
   boundaries). Mathlib at the pin ships `Mathlib.Topology.SimplicialSet.*`
   for abstract simplicial machinery and `Mathlib.AlgebraicTopology.*`
   for singular homology, but **no theorem of the form**
   "every compact Hausdorff topological 2-manifold admits a finite
   triangulation" is named at the pin. (Radó 1925 / Cairns 1934 in
   the literature.)

2. **Edge orientation cancellation on a closed surface.** On any
   triangulated closed (no-boundary) 2-manifold each interior edge is
   shared by exactly two faces, and the induced orientations on the
   edge from those two faces are opposite. Mathlib at the pin does
   not name this combinatorial fact in any of `SimplicialComplex`,
   `SimplicialSet`, or the topology library.

3. **Chart-disk realisation of singular faces.** That for each
   `x ∈ S`, a small chart-disk `B_x` is a 2-cell of the triangulation
   whose chart-circle integer of `d(log f)/(2πi)` equals `ord_x f`.
   This is `chartIntegral_eq_order` (already a bundle field on
   `GlobalResidueSum_hypothesis`) plus the requirement that `B_x` be
   a face of the triangulation — the latter is a triangulation
   refinement statement, again not named in mathlib.

4. **Closed-form vanishing on regular faces.** That on every face not
   containing a singular point, the chart-circle integer is zero by
   `StokesDiskClosedForm.chartCircleIntegralOfFun_eq_zero_of_diffContOnCl`.
   This *is* in the repo; what's missing is the structured assignment
   "regular face ↦ a chart on which `f` is holomorphic non-vanishing".

Items (1), (2) are the genuine R5-shadow wall; (3), (4) are wiring
work consuming (1), (2). -/

end IntegerShadowStokes

end JacobianChallenge

end
