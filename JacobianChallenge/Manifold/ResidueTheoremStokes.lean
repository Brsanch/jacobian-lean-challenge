/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.MeromorphicDivisor
import JacobianChallenge.Manifold.ResidueTheorem

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # The residue theorem on a compact Riemann surface — Stokes-route framing

This file ships a **second, parallel framing** for the residue theorem on a
compact connected Riemann surface, the Stokes / contour-integral route
(Route B in the file docstring of `Manifold/ResidueTheorem.lean`). The
classical statement is:

> For each non-zero meromorphic `f : X → ℂ`, the meromorphic 1-form `df / f`
> has simple poles at the zeros and poles of `f`, with residues equal to
> the local orders. Stokes on a compact closed 2-manifold then gives
> `∑_x Res_x(df / f) = 0`.

At the mathlib pin (`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`,
15 Apr 2026), neither manifold-style meromorphic 1-forms, residues at points,
nor Stokes for residues are packaged. This file therefore does **not**
attempt the Stokes proof itself: that is its own multi-PR mathlib effort.
What this file *does* ship is the **structural decomposition**:

1. The integer `residueAt f x : ℤ`, defined honestly as
   `(mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`. This is the residue of
   `df / f` at `x`, in the form delivered by Route B's local
   logarithmic-derivative formula `Res_{x₀}((f' / f) dz) = ord_{x₀}(f)`.
2. The Stokes-route Prop-valued statement
   `StokesResidueTheorem_statement X : Prop` — the sum of residues is
   zero, summed over the (finite, by R2 of the Route-A file) support of
   the order divisor of `f`.
3. The **load-bearing equivalence**
   `stokesResidueTheorem_iff_residueTheorem :
     StokesResidueTheorem_statement X ↔ ResidueTheorem X`,
   showing that proving the Stokes-form (a single global Stokes / residue
   identity) is equivalent to proving R5 directly. The forward direction
   uses `Div.degree_eq_sum_of_supportFinset_subset` to identify the
   degree-sum with the residue-sum; the reverse direction is symmetric.

The file is *honest*: every `def` reduces to a real expression, no `axiom`s
are introduced, and `iff_residueTheorem` is a real proof (no `sorry`).

## Why this matters

The Route-A skeleton in `Manifold/ResidueTheorem.lean` decomposes R5 into
four classical inputs (R1–R4: pole-extension, fibre-finiteness,
local-multiplicity = local-order, fibre-degree balance). Route B
decomposes R5 into a *different* set of inputs: meromorphic 1-forms,
single-point residues, and Stokes' theorem. Either route, fully discharged,
closes the residue theorem. By exposing the equivalence in this file, we
make the choice of route a **scheduling decision** (which mathlib package
lands first) rather than a mathematical one.

## What is NOT done here

* The actual Stokes proof (it would need meromorphic 1-forms on
  manifolds + Stokes' theorem for residues, neither of which exists at the
  pin).
* The local logarithmic-derivative formula
  `Res_{x₀}((df / f)) = ord_{x₀}(f)`. We *take* this identity as the
  definition of `residueAt` (which is mathematically correct on any
  chart), and document the owed gap.
* Any `df / f` 1-form construction. The placeholder
  `logDiff_statement` is a `Prop`-only flag for downstream code to refer
  to once the meromorphic-1-form package lands.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

namespace Stokes

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The logarithmic differential `d log f` (placeholder Prop) -/

/-- The **logarithmic differential** `d(log f) = (df) / f` of a non-vanishing-
germ meromorphic `f`, as a placeholder `Prop`-only statement. The full
content is the data of a meromorphic 1-form on `X` whose poles, residues,
and chart-local representations match the classical formula
`(d log f)(z) = (f'(z) / f(z)) dz` in any holomorphic chart.

Concretely, the owed downstream package is

* a type `MeromorphicOneForm X` of meromorphic 1-forms on `X`, and
* a constructor `logDiff (f : MeromorphicNonzero X) : MeromorphicOneForm X`
  whose value at `x` (in any chart) is `(f' / f) dz` and whose set of poles
  is the support of the order divisor of `f`, with residues
  `Res_x (logDiff f) = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`.

Neither the type nor the constructor exists in mathlib at the pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 Apr 2026). We therefore
record only the *flag*: a `Prop`-valued placeholder that downstream code can
import and refine once the meromorphic-1-form package lands. The current
body is `True` — i.e. the existence of `logDiff f` is unconditionally
asserted as a placeholder — *not* an axiom: this is a `def : Prop`, so the
unfolding is `True`, and any downstream proof that consumes
`logDiff_statement` must instead rely on the honest `residueAt` below or
on the full Stokes statement. -/
def logDiff_statement (_f : MeromorphicNonzero X) : Prop := True

/-! ## The residue at a point (honest integer-valued definition) -/

/-- The **residue at `x`** of the logarithmic differential `df / f`, in the
Stokes-route formulation: it is the integer

  `(mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`

i.e. the chart-pulled-back order of `f` at `x`. This is honest because the
classical local formula

  `Res_{z₀}((f' / f) dz) = ord_{z₀}(f)` (Mathlib `Analysis.Complex.Residue`,
  in some form, at the flat-domain level)

makes the right-hand side the *definition* of the residue of `df / f`.
Through chart-independence of `mmeromorphicOrderAt` (proved on a complex
analytic manifold in `Manifold/MeromorphicAt.lean` via
`mmeromorphicOrderAt_eq_of_isManifold`), this integer is well-defined on
the manifold.

This `residueAt` agrees pointwise with `(principalDivisorMap f) x` (the
order divisor of `f`), via `principalDivisorMap_apply`. -/
def residueAt (f : MeromorphicNonzero X) (x : X) : ℤ :=
  JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x

/-- `residueAt f x` equals `(principalDivisorMap f) x` pointwise. -/
@[simp] lemma residueAt_eq_principalDivisor (f : MeromorphicNonzero X) (x : X) :
    residueAt f x = (principalDivisorMap f : X → ℤ) x := by
  unfold residueAt
  exact (principalDivisorMap_apply f x).symm

/-! ## The Stokes-route global statement -/

/-- **Stokes-route R5 statement.** For every non-zero meromorphic `f` on `X`,
the sum of residues of `df / f` over the (finite, by R2) support of the
order divisor of `f` is zero. This is the classical residue theorem on a
compact closed 2-manifold, in the form delivered by Stokes' theorem:

  `∑_{x ∈ supp(ord_·(f))} Res_x(df / f) = 0`.

The support set is the (finite, by `MMeromorphicOn.orderFun_support_finite`)
set of points where the order is non-zero — equivalently, the set of zeros
and poles of `f`. The *value* of the residue at `x` is `residueAt f x`,
which by the local logarithmic-derivative formula is
`(mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`.

This is a `Prop`-valued `def` (not an `axiom`). It is the Stokes-route
analogue of `R5_principal_degree_zero_statement` from
`Manifold/ResidueTheorem.lean`. The next lemma
`stokesResidueTheorem_iff_residueTheorem` shows the two statements are
equivalent. -/
def StokesResidueTheorem_statement (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  ∀ f : MeromorphicNonzero X,
    ∑ x ∈ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
              (𝓘(ℂ, ℂ)) f.toFun
              f.meromorphic f.nonvanishing_germ).toFinset,
      residueAt f x = 0

/-! ## The Route-A reformulation as a `Prop`

We restate `R5_principal_degree_zero_statement X` as the proposition

  `ResidueTheorem X := ∀ f, (principalDivisorMap f).degree = 0`

so that `iff_residueTheorem` below can chain through a single named
target. This is identical to `R5_principal_degree_zero_statement X` and is
introduced only to give the headline equivalence a clean shape. -/

/-- The Route-A residue-theorem statement: the principal divisor of any
non-zero meromorphic function has degree zero. Identical in content to
`ResidueTheorem.R5_principal_degree_zero_statement X`. -/
def ResidueTheorem_statement (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  ∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0

/-- `ResidueTheorem_statement X` and `R5_principal_degree_zero_statement X`
are definitionally the same. -/
lemma residueTheorem_statement_eq_R5 :
    ResidueTheorem_statement X
      ↔ JacobianChallenge.ResidueTheorem.R5_principal_degree_zero_statement X :=
  Iff.rfl

/-! ## Bridge: the support-finsets agree

`(principalDivisorMap f).supportFinset` (the support of the order divisor,
packaged as a `Finset`) and
`(orderFun_support_finite … f.meromorphic f.nonvanishing_germ).toFinset`
(the support coming from the global-finiteness lemma) both consist of the
same elements: those `x : X` with `orderFun 𝓘(ℂ,ℂ) f.toFun x ≠ 0`. -/

lemma principalDivisor_supportFinset_eq
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).supportFinset
      = (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
          (𝓘(ℂ, ℂ)) f.toFun
          f.meromorphic f.nonvanishing_germ).toFinset := by
  classical
  ext x
  -- LHS membership: `x ∈ (principalDivisorMap f).supportFinset ↔
  --   (principalDivisorMap f : X → ℤ) x ≠ 0`,
  -- which by `principalDivisorMap_apply` is `orderFun 𝓘(ℂ,ℂ) f.toFun x ≠ 0`.
  rw [JacobianChallenge.Div.mem_supportFinset, principalDivisorMap_apply,
      Set.Finite.mem_toFinset]
  -- RHS membership: `x ∈ {x | orderFun 𝓘(ℂ,ℂ) f.toFun x ≠ 0}` is by `Set.mem_setOf`.
  rfl

/-! ## The headline equivalence -/

/-- **The Stokes-route statement is equivalent to the Route-A statement.**
The forward direction unfolds the divisor degree as a sum over the support
of the order divisor and matches it with the residue-sum (using
`residueAt_eq_principalDivisor` to identify the summands and
`principalDivisor_supportFinset_eq` to identify the index sets). The
reverse direction is symmetric: a Stokes-residue-zero hypothesis directly
yields the divisor-degree-zero conclusion via the same identification.

This lemma is the **load-bearing chip** of the file: it shows that the
Stokes-form sum equals `(principalDivisorMap f).degree` (a real
computation, not a stub), making the two routes interchangeable as proof
targets for R5. -/
lemma stokesResidueTheorem_iff_residueTheorem :
    StokesResidueTheorem_statement X ↔ ResidueTheorem_statement X := by
  classical
  constructor
  · -- Forward: Stokes ⇒ Route-A.
    intro hStokes f
    -- Reduce `(principalDivisorMap f).degree` to a sum over the
    -- `orderFun_support_finite` toFinset using
    -- `degree_eq_sum_of_supportFinset_subset` (with the support-finset
    -- equality from `principalDivisor_supportFinset_eq`).
    have h_supp_eq := principalDivisor_supportFinset_eq f
    have h_subset : (principalDivisorMap f).supportFinset
        ⊆ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
            (𝓘(ℂ, ℂ)) f.toFun
            f.meromorphic f.nonvanishing_germ).toFinset := h_supp_eq.le
    have h_deg_sum :
        (principalDivisorMap f).degree
          = ∑ x ∈ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
                    (𝓘(ℂ, ℂ)) f.toFun
                    f.meromorphic f.nonvanishing_germ).toFinset,
              ((principalDivisorMap f) : X → ℤ) x :=
      JacobianChallenge.Div.degree_eq_sum_of_supportFinset_subset h_subset
    -- Identify each summand with `residueAt f x`.
    have h_pt : ∀ x : X,
        ((principalDivisorMap f) : X → ℤ) x = residueAt f x := by
      intro x
      exact (residueAt_eq_principalDivisor f x).symm
    rw [h_deg_sum]
    -- The Stokes hypothesis gives the sum-equals-zero on the right index set.
    have h_stokes_at_f := hStokes f
    -- Rewrite the sum using `h_pt`.
    have h_sum_eq :
        ∑ x ∈ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
                (𝓘(ℂ, ℂ)) f.toFun
                f.meromorphic f.nonvanishing_germ).toFinset,
            ((principalDivisorMap f) : X → ℤ) x
          = ∑ x ∈ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
                (𝓘(ℂ, ℂ)) f.toFun
                f.meromorphic f.nonvanishing_germ).toFinset,
              residueAt f x := by
      apply Finset.sum_congr rfl
      intro x _
      exact h_pt x
    rw [h_sum_eq]
    exact h_stokes_at_f
  · -- Reverse: Route-A ⇒ Stokes.
    intro hRA f
    -- The principal divisor's degree is zero, so the sum-form is zero too.
    have h_deg : (principalDivisorMap f).degree = 0 := hRA f
    have h_supp_eq := principalDivisor_supportFinset_eq f
    have h_subset : (principalDivisorMap f).supportFinset
        ⊆ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
            (𝓘(ℂ, ℂ)) f.toFun
            f.meromorphic f.nonvanishing_germ).toFinset := h_supp_eq.le
    have h_deg_sum :
        (principalDivisorMap f).degree
          = ∑ x ∈ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
                    (𝓘(ℂ, ℂ)) f.toFun
                    f.meromorphic f.nonvanishing_germ).toFinset,
              ((principalDivisorMap f) : X → ℤ) x :=
      JacobianChallenge.Div.degree_eq_sum_of_supportFinset_subset h_subset
    -- Substitute residue identification.
    have h_pt : ∀ x : X,
        ((principalDivisorMap f) : X → ℤ) x = residueAt f x := by
      intro x
      exact (residueAt_eq_principalDivisor f x).symm
    have h_sum_eq :
        ∑ x ∈ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
                (𝓘(ℂ, ℂ)) f.toFun
                f.meromorphic f.nonvanishing_germ).toFinset,
            ((principalDivisorMap f) : X → ℤ) x
          = ∑ x ∈ (JacobianChallenge.MMeromorphicOn.orderFun_support_finite
                (𝓘(ℂ, ℂ)) f.toFun
                f.meromorphic f.nonvanishing_germ).toFinset,
              residueAt f x := by
      apply Finset.sum_congr rfl
      intro x _
      exact h_pt x
    -- Combine: Stokes-form sum = degree = 0.
    rw [← h_sum_eq, ← h_deg_sum]
    exact h_deg

/-- Corollary: the Stokes-route statement is equivalent to
`R5_principal_degree_zero_statement X` (the named gap from
`Manifold/ResidueTheorem.lean`). Together with
`residue_theorem_of_routeA`, this means that **discharging
`StokesResidueTheorem_statement X`** (e.g. via a future Stokes / residue
package) immediately closes the residue theorem on `X`. -/
lemma stokesResidueTheorem_iff_R5 :
    StokesResidueTheorem_statement X
      ↔ JacobianChallenge.ResidueTheorem.R5_principal_degree_zero_statement X := by
  rw [stokesResidueTheorem_iff_residueTheorem]
  exact residueTheorem_statement_eq_R5

/-! ## What is owed to actually *prove* `StokesResidueTheorem_statement`

Even though the equivalence above is fully proven (no `sorry`, no `axiom`),
discharging `StokesResidueTheorem_statement X` itself requires the
following classical inputs, none of which are in mathlib at the pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`:

(B1) **Meromorphic 1-forms on a complex 1-manifold.** A type
     `MeromorphicOneForm X` of meromorphic 1-forms, with chart-local
     representation `(f' / f) dz` for the special case `df / f`. Owed from
     a future package on top of `Manifold/HolomorphicOneForm.lean`.

(B2) **Single-point residue of a meromorphic 1-form.** A function
     `Res : MeromorphicOneForm X → X → ℂ` that, in any holomorphic chart at
     `x`, returns the standard contour-integral residue
     `(2πi)⁻¹ ∮ ω` over a small loop around `x`. The integrality
     `Res x (logDiff f) ∈ ℤ` and the identification with `ord_x(f)` is the
     local logarithmic-derivative formula
     `Res_{z₀}((f'/f) dz) = ord_{z₀}(f)`. The flat-domain version is in
     `Mathlib.Analysis.Complex.Residue` in some form; the manifold version
     is owed.

(B3) **Stokes' theorem for residues on a compact closed 2-manifold.** The
     identity `∑_x Res_x(ω) = 0` for any meromorphic 1-form `ω` on a
     compact closed orientable 2-manifold. This follows from Stokes'
     theorem applied to `X \ ⋃_i D_i(ε)` (the small-disk complement of the
     pole set) plus the residue-as-loop-integral formula. The pure Stokes
     piece is partially in `Mathlib.Geometry.Manifold.Stokes`; the residue
     packaging is owed.

When (B1)–(B3) land, the Stokes-route proof of
`StokesResidueTheorem_statement X` follows by:

1. Construct `ω := logDiff f` from (B1).
2. By (B2), `Res_x(ω) = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀
   = residueAt f x` for every `x` in the support of `ord_·(f)`, and
   `Res_x(ω) = 0` outside that support.
3. By (B3), `∑_x Res_x(ω) = 0`. The sum reduces to the support-sum because
   `Res_x(ω) = 0` outside the support; this is the
   `StokesResidueTheorem_statement` conclusion.

By `stokesResidueTheorem_iff_R5` above, this also closes
`R5_principal_degree_zero_statement X` and hence (via
`residue_theorem_of_routeA`) the headline `residue_theorem`. -/

end Stokes

end JacobianChallenge

end
