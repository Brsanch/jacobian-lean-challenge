/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibreCardWellDefinedAtRegular
import JacobianChallenge.Manifold.PreconnectedFromFiniteComplement

/-! # Hurwitz constant-card, staged on `h_path` (ZZ160)

Compose ZZ155 (`fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo`)
with ZZ159 (`h_topo_of_h_path`) so that the *only* topological residual
exposed at the headline is the manifold-lift content `(M1)`:

```
∀ C : Set Y, C.Finite → (Cᶜ).Nonempty → IsPathConnected (Cᶜ : Set Y).
```

When `(M1)` lands unconditionally (target of ZZ165), this theorem
becomes one rewrite away from the strict-closure of the constant-card
statement.

## What this file does and does not deliver

This file *stages* the topological side. ZZ155 still needs two analytic
hypotheses that this file does not — and cannot, at the present pin —
discharge:

* `h_lc`: local-constancy of the fibre cardinality on the regular subset.
  ZZ158 (`HLcUnconditional.lean`) supplies this *conditional on a per-fibre
  `LocalSheetData` supplier and fibre-finiteness on `Cᶜ`*. The
  `LocalSheetData` supplier is the analytic content that `ZZ152`
  (`AnalyticAt.exists_local_biholomorphism`) produces in chart-flat
  coordinates and which a separate supplier chip transports to `f : X → Y`.

* `h_C_fin`: finiteness of the chosen critical-value set `C`. Specialising
  `C := f.criticalValues` is what ZZ100
  (`criticalValues_finite_of_nonconstant_of_witness`) produces, but only
  for `f : MeromorphicNonzero X` (Riemann-sphere target) under a
  `CriticalSetWitness`. For an arbitrary `f : X → Y` between general
  complex 1-manifolds, no unconditional finiteness is available at this
  pin.

The wrapper below therefore exposes the full hypothesis set as
parameters, with `h_path` factored out via ZZ159 so the topological
residual is the single named manifold-lift content `(M1)`.

No `sorry`, no `axiom`. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ContMDiff

namespace Owed.degree

universe u v

/-- **Hurwitz constant-card, staged on `h_path`.**

Given:

* `h_path` — manifold-lift `(M1)`: the complement of any finite set in
  `Y` is path-connected (when nonempty). This is the *single* named
  topological residual; ZZ159 turns it into the `IsPreconnected`
  hypothesis that ZZ155 consumes.
* `h_lc` — ZZ155-shape local-constancy of fibre cardinality. ZZ158
  supplies this conditional on a `LocalSheetData` supplier on `Cᶜ`.
* `h_C_fin` — finiteness of every chosen critical-value set `C`.

Conclude the unfolded form of `fibre_card_well_defined_at_regular_statement`.

When ZZ165 lands `h_path` unconditionally as a theorem of complex
1-manifolds, this wrapper closes to a ZZ155-shape statement parameterised
only on the analytic residuals `h_lc` and `h_C_fin`. -/
theorem fibre_card_well_defined_at_regular_holds_of_h_path
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_path : ∀ C : Set Y, C.Finite → (Cᶜ : Set Y).Nonempty →
      IsPathConnected (Cᶜ : Set Y))
    (h_lc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y),
        IsLocallyConstant (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard))
    (h_C_fin : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f → ∀ (C : Set Y), C.Finite) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y) (w₁ w₂ : RegularValueWitnessReg f C), w₁.card = w₂.card := by
  -- Build h_topo from h_path via ZZ159.
  have h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y) :=
    JacobianChallenge.Manifold.h_topo_of_h_path h_path
  -- Apply ZZ155.
  exact fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo
    h_lc h_topo h_C_fin

end Owed.degree

end ContMDiff

end JacobianChallenge
