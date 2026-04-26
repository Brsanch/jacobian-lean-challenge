import Mathlib -- compiles with commit 8e3c989104daaa052921bf43de9eef0e1ac9fbf5 (15th April 2026)
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.LocalMultiplicity
import JacobianChallenge.Jacobian

/-!

# Jacobians

An AI challenge to make an API for Jacobians, by Kevin Buzzard. v0.3.

Source: https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9

This file is the verbatim challenge signature. Definitions and proofs are
filled in incrementally; every `sorry` corresponds to one open challenge item
listed in `OPEN.md`.

## Main missing definitions

* `genus` -- genus of a compact Riemann surface
* `Jacobian` -- the Jacobian of a compact Riemann surface
* `Jacobian.ofCurve` -- the Abel-Jacobi map from a compact Riemann surface to its Jacobian
* `ContMDiff.degree` -- the degree of a holomorphic map between compact Riemann surfaces.
    Equal to 0 if the map is constant, otherwise equal to the usual degree.
* `Jacobian.pushforward` -- the pushforward map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.
* `Jacobian.pullback` -- the pullback map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.

## Main missing theorems

* `genus_eq_zero_iff_homeo` -- a compact Riemann surface has genus 0 iff it is homeomorphic to
     the sphere
* `ofCurve_inj` -- the Abel-Jacobi map is injective iff the genus is positive
* `Jacobian.ofCurve_contMDiff` -- the Abel-Jacobi map is holomorphic
* `Jacobian.pushforward_contMDiff` -- the pushforward map is holomorphic
* `Jacobian.pullback_contMDiff` -- the pullback map is holomorphic
* `pushforward_pullback` -- pullback then pushforward is multiplication by degree

## Changelog (Buzzard's, upstream)

* v0.3: drop [Nonempty X] in the presence of [ConnectedSpace X] (connected => nonempty).
* v0.2: `Type*` not `Type u`; use `𝓘(ℂ)` instead of `modelWithCornersSelf ℂ ℂ`; docstrings
  and comments
* v0.1: initial public release
-/

open scoped ContDiff -- for ω notation

open scoped Manifold -- for 𝓘 notation

/-- The genus of a compact Riemann surface, defined as the complex dimension of
the space of global holomorphic 1-forms (the *geometric* genus).

For a compact connected Riemann surface this equals the topological genus, but
that identification is challenge item 14 (`genus_eq_zero_iff_homeo`) and is not
proved here. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  JacobianChallenge.genus X

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- this proof avoids the hack answer `∀ X, genus X = 0`
lemma genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  sorry

universe u in
-- data
/-- The Jacobian of a compact Riemann surface, defined as the (placeholder)
Picard group of degree-zero divisor classes from `JacobianChallenge.Divisor`.

`abbrev` so the `AddCommGroup` / `TopologicalSpace` / `T2Space` instances on
`JacobianChallenge.Jacobian X` flow through automatically. See the docstring
of `JacobianChallenge.Jacobian` for the placeholder caveats — at this pin the
principal-divisor subgroup is `⊥`, so this is canonically isomorphic to
`Div0 X` rather than the analytic Jacobian `ℂᵍ / Λ`. -/
abbrev Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u :=
  JacobianChallenge.Jacobian X

namespace Jacobian

-- data
/-- The Jacobian of a compact Riemann surface is naturally an additive commutative group. -/
noncomputable instance : AddCommGroup (Jacobian X) := inferInstance

-- data
/-- The Jacobian of a compact Riemann surface is naturally a topological space. -/
instance : TopologicalSpace (Jacobian X) := inferInstance

-- Prop
instance : T2Space (Jacobian X) := inferInstance

-- Prop
instance : CompactSpace (Jacobian X) := sorry

-- data
/-- The Jacobian of a compact Riemann surface is a complex manifold, of dimension
equal to the genus of the surface. -/
instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := sorry

-- Prop
instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := sorry

-- Prop
instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := sorry

/-- The Abel-Jacobi map from a compact Riemann surface to its Jacobian. **Stub
at this pin** — see `JacobianChallenge.Jacobian.ofCurve` for the constant-zero
placeholder; honest `Q ↦ [Q] - [P]` is owed once the single-point-divisor
constructor lands in `Divisor.lean`. The `ofCurve_inj` lemma (item 16) is
*false* for this stub when `genus X > 0` and is therefore left `sorry`. -/
noncomputable def ofCurve (P : X) : X → Jacobian X :=
  JacobianChallenge.Jacobian.ofCurve P

lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) := sorry

lemma ofCurve_self (P : X) : ofCurve P P = 0 :=
  JacobianChallenge.Jacobian.ofCurve_self P

-- this is the lemma which stops the hack answer "J(X)=0 for all X"
-- At this pin the hypothesis `h : 0 < genus X` is unused: the placeholder
-- `PrincDiv X = ⊥` makes `Pic0 X` faithful over `Div0 X`, so injectivity of
-- `Q ↦ [δ Q − δ P]` reduces to `Div.single_eq_iff`. When `PrincDiv` becomes
-- honest, this delegation must be revisited and the hypothesis becomes
-- load-bearing (Abel–Jacobi theorem).
lemma ofCurve_inj (P : X) (_h : 0 < genus X) : Function.Injective (ofCurve P) :=
  JacobianChallenge.Jacobian.ofCurve_inj P

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- The pushforward map between Jacobians associated to a map of the underlying curves. -/
noncomputable def pushforward (f : X → Y)
    (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  JacobianChallenge.Jacobian.pushforward f

-- pushforward is holomorphic
theorem pushforward_contMDiff :
  ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
  (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) := sorry

-- functoriality
lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P :=
  JacobianChallenge.Jacobian.pushforward_id_apply P

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- functoriality
lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) :=
  JacobianChallenge.Jacobian.pushforward_comp_apply f g P

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant.

**Stub at this pin** — delegated to `JacobianChallenge.Jacobian.pullback`,
which is the zero `ContinuousAddMonoidHom`. This satisfies the *signature*
of item 13, but mathematically the true pullback is the descent of the
fiber-sum `single y ↦ ∑_{x ∈ f⁻¹(y)} single x`. See the section docstring
of `JacobianChallenge.Jacobian.pullback` for what is owed before this can
become honest (a `Div.fiberSum` construction with finite-fiber hypotheses,
plus degree preservation). -/
def pullback (f : X → Y)
    (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  JacobianChallenge.Jacobian.pullback f

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) := sorry

-- functoriality
-- This lemma is **false** for the current zero-stub `pullback` (we would
-- need `0 P = P`, which fails for `P ≠ 0`). It stays `sorry` until
-- `pullback` becomes honest. See `JacobianChallenge.Jacobian.pullback`
-- docstring for the construction that is owed.
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P := sorry

-- functoriality
-- For the zero-stub `pullback`, both sides reduce to `0`, so the statement
-- holds. When `pullback` becomes honest this lemma will need a real proof;
-- the statement itself, however, is exactly the strict-reader check and is
-- preserved.
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) :=
  JacobianChallenge.Jacobian.pullback_comp_apply f g P

/-- The degree of a holomorphic map between compact Riemann surfaces. Equal to
zero for constant maps, otherwise equal to the usual degree.

**Stub at this pin** — see `JacobianChallenge.Manifold.degreeStub` for the
constant-vs-non-constant indicator. Returns `1` for any non-constant map
regardless of actual sheet count; the honest regular-value-cardinality
definition is owed once chart-independence of `mmeromorphicOrderAt` lands. -/
noncomputable def _root_.ContMDiff.degree
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  JacobianChallenge.Manifold.degreeStub f hf

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := sorry

end Jacobian
