import Mathlib -- compiles with commit 8e3c989104daaa052921bf43de9eef0e1ac9fbf5 (15th April 2026)
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.LocalMultiplicity
import JacobianChallenge.Manifold.Degree
import JacobianChallenge.Manifold.NearbyRegularWitnessUnconditional
import JacobianChallenge.Jacobian
import JacobianChallenge.JacobianPullbackHonest

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
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  JacobianChallenge.Jacobian.pushforward hf

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
  JacobianChallenge.Jacobian.pushforward_comp_apply hf hg P

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant.

**Honest body (post-ZZ172 swap).** The body delegates to
`JacobianChallenge.Jacobian.pullbackHonest_of_rsum`, which cases on
`IsConstantMap f`:
* constant `f` ⇒ the zero `ContinuousAddMonoidHom`;
* non-constant `f` ⇒ the multiplicity-weighted divisor pullback
  `Jacobian.pullbackWeighted` with `e := manifoldRamificationIndex f`
  and `N := degreeFiber f hf`.

The Riemann-Hurwitz total-weight obligation
(`Owed.degree.ramificationSumEqualsDegree_statement X Y`) is supplied
unconditionally by `ramificationSumEqualsDegree_holds_unconditional`. -/
noncomputable def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X := by
  classical
  exact JacobianChallenge.Jacobian.pullbackHonest_of_rsum
    (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional X Y)
    f hf

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) := sorry

-- functoriality
-- Post-ZZ:BasicSwap (honest `pullback` body) and `pullbackHonest_of_rsum_id`
-- (item 22 chip): the honest pullback is the identity on `Jacobian X`.
-- The proof case-splits on `IsConstantMap (id : X → X)`. Constant `id`
-- forces `Subsingleton X`, hence `Subsingleton (Pic0 X)`, so any element
-- equals any other. Non-constant `id` activates the divisor-pullback
-- machinery with singleton fibres `id ⁻¹' {y} = {y}` and weights
-- `manifoldRamificationIndex id y = 1`, collapsing to the identity.
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P := by
  classical
  exact JacobianChallenge.Jacobian.pullbackHonest_of_rsum_id _ P

-- functoriality
-- Post-ZZ:BasicSwap + chip ZZ-PullCompFunc-v2: `pullback` is the honest
-- body (`pullbackHonest_of_rsum`), and `pullbackHonest_of_rsum_comp`
-- in `JacobianPullbackHonest.lean` supplies contravariant functoriality.
-- Three of the four case-split branches collapse to `0` on both sides;
-- the both-non-constant case delegates to the divisor chain rule
-- `Div.fiberSumWeighted_comp_apply` with multiplicative weights given by
-- `manifoldRamificationIndex_comp_unconditional`.
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  classical
  show JacobianChallenge.Jacobian.pullbackHonest_of_rsum
        (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional X Z)
        (g.comp f) (hg.comp hf) P
      = JacobianChallenge.Jacobian.pullbackHonest_of_rsum
          (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional X Y)
          f hf
          (JacobianChallenge.Jacobian.pullbackHonest_of_rsum
            (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional Y Z)
            g hg P)
  exact JacobianChallenge.Jacobian.pullbackHonest_of_rsum_comp
    (h_rsum_XY :=
      JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional X Y)
    (h_rsum_YZ :=
      JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional Y Z)
    (h_rsum_XZ :=
      JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional X Z)
    f g hf hg P

/-- The degree of a holomorphic map between compact Riemann surfaces. Equal to
zero for constant maps, otherwise equal to the usual degree.

**Honest fibre-cardinality definition.** Delegates to
`JacobianChallenge.ContMDiff.degreeFiber`, which returns `0` for constant
maps and otherwise extracts a regular fibre cardinality via
`Classical.choice` on `Nonempty (RegularValueWitness f)`. The
existence of a regular-value witness for non-constant holomorphic maps is
discharged unconditionally by ZZ49
(`Owed.degree.regular_value_exists_statement_holds_unconditional`), so this
returns a real fibre count rather than a constant-vs-non-constant indicator.
Independence of the chosen witness (i.e. well-definedness of the fibre count
across regular values) is the deeper classical fact still owed at this pin
(see `Manifold/Degree.lean` and ZZ156). -/
noncomputable def _root_.ContMDiff.degree
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  JacobianChallenge.ContMDiff.degreeFiber f hf

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : DecidableEq Y := Classical.decEq Y
  -- `pushforward f hf = JacobianChallenge.Jacobian.pushforward f` (the `_hf`
  -- argument is dropped at `Basic.lean.pushforward`), and `pullback f hf P =
  -- JacobianChallenge.Jacobian.pullbackHonest_of_rsum _ f hf P` (same body
  -- swap as in `pullback_comp_apply` above).
  show JacobianChallenge.Jacobian.pushforward hf
        (JacobianChallenge.Jacobian.pullbackHonest_of_rsum
          (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional X Y)
          f hf P)
      = (ContMDiff.degree f hf) • P
  -- `ContMDiff.degree f hf = JacobianChallenge.ContMDiff.degreeFiber f hf`
  -- by definition; convert the `ℕ`-smul on the RHS to the `ℤ`-cast smul,
  -- matching the shape of `pushforward_pullbackHonest_of_rsum`.
  have hZ : ∀ (m : ℕ) (Q : Jacobian Y), ((m : ℤ) • Q) = m • Q := by
    intro m Q
    induction m with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, Nat.cast_succ, add_zsmul, one_zsmul, ih]
  rw [← hZ (ContMDiff.degree f hf) P]
  exact JacobianChallenge.Jacobian.pushforward_pullbackHonest_of_rsum
    (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional X Y)
    f hf P

end Jacobian
