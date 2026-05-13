/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.RiemannRochGenusZeroDecomposition
import JacobianChallenge.Topology.RiemannRochGenusZeroSingleInput
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics.threshold 100

/-! # Split `ExistsMeroSimplePole_GenusZero X` into two named pieces

This chip decomposes zz337's `ExistsMeroSimplePole_GenusZero X` —
the Forster Theorem 16.9 existence statement — into two more
elementary classical inputs:

  (A) `ExistsNonConstantBoundedByDeltaP_GenusZero X` — under
      `genus X = 0`, ∃ p, ∃ f : MeromorphicNonzero X non-constant
      with `ord_p f ≥ -1` and `ord_x f ≥ 0` for `x ≠ p`. This is
      the **dim L(δp) ≥ 2** content of Riemann-Roch + Serre duality
      (the 1-dimensional constants give the trivial 1, the non-trivial
      direction adds a non-constant element).

  (B) `LiouvilleOnCompactConnected X` — any `ContMDiff ω` function
      `g : X → ℂ` on a compact connected complex 1-manifold is
      constant. (Classical max-modulus argument, in reach with
      mathlib's `Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm`
      + chart-level reduction.)

Composition: under (A), we have a non-constant `f` with `ord_p f ≥ -1`
and `ord_x f ≥ 0` for `x ≠ p`. If `ord_p f = 0` (no pole at `p`), then
`f` is holomorphic on all of `X` (every order is ≥ 0), so by (B) `f`
is constant — contradiction. Hence `ord_p f = -1` exactly, which
matches the `ExistsMeroSimplePole_GenusZero` shape.

The compositional theorem
`existsMeroSimplePole_genusZero_from_RR_and_Liouville` reduces zz337's
existence hypothesis to (A) + (B). Combined with the proven
`uniformSimplePoleRegularity_holds` (zz344), `RiemannRochGenusZero X`
is now conditional on (A) + (B) only.

(B) is in reach of existing mathlib content; the next chip will
attack it directly via max-modulus and analytic continuation.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named hypothesis (A): a non-constant function bounded by δp at
genus 0.** Under `genus X = 0`, there exist `p : X` and a non-constant
`f : MeromorphicNonzero X` with order at every point at least `-1`
at `p` and `≥ 0` elsewhere.

Classical content: this is the `dim L(δp) ≥ 2` consequence of
Riemann-Roch (`dim L(D) - dim L(K-D) ≥ deg D + 1 - g`) plus Serre
duality (`dim L(K-D) = dim Ω(-D) ≤ dim Ω = g = 0`) at genus 0. The
constants supply a 1-dimensional subspace; (A) asserts the second
dimension is realised by a *non-constant* element. -/
def ExistsNonConstantBoundedByDeltaP_GenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
  ∃ (p : X) (f : MeromorphicNonzero X),
    (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) ∧
    (((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p) ∧
    ¬ JacobianChallenge.IsConstantMap f.toFun

/-- **Named hypothesis (B): Liouville on compact connected complex
1-manifolds.** Any `MeromorphicNonzero X` function with order `≥ 0`
everywhere (i.e. holomorphic globally) is constant.

Classical content: complex max-modulus + analytic continuation +
compactness force the modulus to attain its max, and the max-modulus
principle then forces local constancy in any chart around the max,
which globalises by connectedness.

(B) is in reach of existing mathlib content. Discharging (B)
unconditionally is the next-chip target. -/
def LiouvilleOnCompactConnected : Prop :=
  ∀ (f : MeromorphicNonzero X),
    (∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) →
    JacobianChallenge.IsConstantMap f.toFun

/-- **Composition: (A) + (B) discharge `ExistsMeroSimplePole_GenusZero X`.**

Under (A) we have non-constant `f` with `ord_p f ≥ -1` and
`ord_x f ≥ 0` for `x ≠ p`. If `ord_p f` were `≥ 0`, every order
would be `≥ 0`, and (B) would force `f` constant — contradiction.
So `ord_p f` is strictly negative and `≥ -1`, hence exactly `-1`. -/
theorem existsMeroSimplePole_genusZero_from_RR_and_Liouville
    (hA : ExistsNonConstantBoundedByDeltaP_GenusZero X)
    (hB : LiouvilleOnCompactConnected X) :
    ExistsMeroSimplePole_GenusZero X := by
  intro hg
  obtain ⟨p, f, h_holo_ne_p, h_ge_neg1_p, h_nonconst⟩ := hA hg
  -- Case-split on whether the order at p is also non-negative.
  by_cases h_nonneg_p : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p
  · -- Order ≥ 0 at p too ⇒ holomorphic everywhere ⇒ constant by (B).
    have h_all : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
      intro x
      by_cases hx : x = p
      · rw [hx]; exact h_nonneg_p
      · exact h_holo_ne_p x hx
    exact absurd (hB f h_all) h_nonconst
  · -- Order < 0 at p, plus `≥ -1`, forces order = -1 exactly.
    rw [not_le] at h_nonneg_p
    -- h_nonneg_p : order < 0; h_ge_neg1_p : -1 ≤ order
    have h_eq : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p
        = ((-1 : ℤ) : WithTop ℤ) := by
      -- The germ at p is non-zero, so order ≠ ⊤; we have order ∈ ℤ.
      have h_ne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p ≠ ⊤ :=
        f.nonvanishing_germ p
      -- Coerce to ℤ via `untop`.
      set n : ℤ := (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p).untop h_ne_top with hn_def
      have hn_coe : ((n : ℤ) : WithTop ℤ) = mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p := by
        simp [hn_def, WithTop.coe_untop]
      -- From `-1 ≤ order` and `order < 0` in `WithTop ℤ`, derive integer
      -- inequalities, conclude `n = -1`.
      have h_le : (-1 : ℤ) ≤ n := by
        rw [← WithTop.coe_le_coe, hn_coe]; exact h_ge_neg1_p
      have h_lt : n < 0 := by
        have : ((n : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by
          rw [hn_coe]; exact_mod_cast h_nonneg_p
        exact_mod_cast this
      have h_n_eq : n = -1 := by linarith
      rw [← hn_coe, h_n_eq]
    -- Convert h_holo_ne_p to required form (already correct).
    -- Final witness.
    exact ⟨p, f, h_eq, h_holo_ne_p, h_nonconst⟩

/-- **`RiemannRochGenusZero X` from (A) + (B).** Combined with zz345,
`RiemannRochGenusZero X` is now conditional on only the two split
inputs. -/
theorem riemannRochGenusZero_from_split
    (hA : ExistsNonConstantBoundedByDeltaP_GenusZero X)
    (hB : LiouvilleOnCompactConnected X) :
    RiemannRochGenusZero X :=
  riemannRochGenusZero_from_existence X
    (existsMeroSimplePole_genusZero_from_RR_and_Liouville X hA hB)

end JacobianChallenge

end
