/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexAffineReparam
import JacobianChallenge.Manifold.Smooth2SimplexMidpointSubdivision
import JacobianChallenge.Manifold.SmoothPathReverse
import JacobianChallenge.Manifold.SmoothPathExt

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Affine segment path of a `Smooth2Simplex`

Given `σ : Smooth2Simplex I X` and two source points `p q : Fin 2 → ℝ`,
produces the smooth path

```
affineSegmentPath σ p q : SmoothPath I X
  t ∈ [0, 1] ↦ σ.toFun ((1 - t) • p + t • q)
```

from `σ.toFun p` to `σ.toFun q`. This is the **1D affine line** in
`Fin 2 → ℝ` from `p` to `q`, pushed through `σ`.

The affine reparameterisation `Smooth2Simplex.affineReparam σ a b c`
has the property that each of its faces is an `affineSegmentPath`:

* `(affineReparam σ a b c).face0 = affineSegmentPath σ b c`
* `(affineReparam σ a b c).face1 = affineSegmentPath σ a c`
* `(affineReparam σ a b c).face2 = affineSegmentPath σ a b`

And the reverse identity holds at the SmoothPath level via
`SmoothPath.ext`:

```
(affineSegmentPath σ p q).reverse = affineSegmentPath σ q p
```

These two ingredients together let us reduce the boundary period of
the 4-way midpoint subdivision of `σ` to a sum of `affineSegmentPath`
integrals on which orientation cancellation is direct.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace Smooth2Simplex

/-! ## The 1D affine line `t ↦ (1 - t) • p + t • q` -/

/-- **Affine line in `Fin 2 → ℝ`.** Sends `0 ↦ p`, `1 ↦ q`. -/
def lineParam (p q : Fin 2 → ℝ) : ℝ → (Fin 2 → ℝ) :=
  fun t => (1 - t) • p + t • q

@[simp] lemma lineParam_zero (p q : Fin 2 → ℝ) : lineParam p q 0 = p := by
  unfold lineParam
  simp

@[simp] lemma lineParam_one (p q : Fin 2 → ℝ) : lineParam p q 1 = q := by
  unfold lineParam
  simp

/-- **`lineParam p q` is `C^∞` as a map `ℝ → (Fin 2 → ℝ)`.** -/
lemma lineParam_contMDiff (p q : Fin 2 → ℝ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin 2 → ℝ)) ∞ (lineParam p q) := by
  rw [contMDiff_iff_contDiff]
  unfold lineParam
  have h_coeff_p : ContDiff ℝ ∞ (fun t : ℝ => 1 - t) :=
    contDiff_const.sub contDiff_id
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => (1 - t) • p) :=
    h_coeff_p.smul contDiff_const
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => t • q) :=
    contDiff_id.smul contDiff_const
  exact h1.add h2

/-- **`lineParam p q (1 - s) = lineParam q p s`.** Direct algebraic
identity: both sides equal `s • p + (1 - s) • q`. -/
lemma lineParam_reverse (p q : Fin 2 → ℝ) (s : ℝ) :
    lineParam p q (1 - s) = lineParam q p s := by
  unfold lineParam
  have h_sub : 1 - (1 - s) = s := by ring
  rw [h_sub]
  ext i
  show s • p i + (1 - s) • q i = (1 - s) • q i + s • p i
  ring

/-- **`affineCombo p q c (face2Param t) = lineParam p q t`.** Applied
to `Smooth2Simplex.affineCombo` with face2Param `t ↦ (t, 0)`, the
output collapses to the 1D affine line `p → q`. -/
lemma affineCombo_face2Param_eq_lineParam
    (p q c : Fin 2 → ℝ) (t : ℝ) :
    affineCombo p q c (Smooth2Simplex.face2Param t) = lineParam p q t := by
  unfold affineCombo lineParam Smooth2Simplex.face2Param
  ext i
  fin_cases i <;> simp

/-- **`affineCombo p q c (face1Param t) = lineParam p c t`.** -/
lemma affineCombo_face1Param_eq_lineParam
    (p q c : Fin 2 → ℝ) (t : ℝ) :
    affineCombo p q c (Smooth2Simplex.face1Param t) = lineParam p c t := by
  unfold affineCombo lineParam Smooth2Simplex.face1Param
  ext i
  fin_cases i <;> simp

/-- **`affineCombo p q c (face0Param t) = lineParam q c t`.** -/
lemma affineCombo_face0Param_eq_lineParam
    (p q c : Fin 2 → ℝ) (t : ℝ) :
    affineCombo p q c (Smooth2Simplex.face0Param t) = lineParam q c t := by
  unfold affineCombo lineParam Smooth2Simplex.face0Param
  ext i
  fin_cases i <;> simp

/-! ## The affine segment path construction

We construct `affineSegmentPath σ p q : SmoothPath I X` directly,
without going through the `pathOfUnitIntervalMap` helper (which is
`private` in `Smooth2Simplex.lean`). The continuous-`Path` field
uses `Path.mk` with a `ContinuousMap` built from the smooth function
`σ ∘ lineParam p q`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **Affine segment path of a `Smooth2Simplex`.** Pushes the 1D
affine line `[0, 1] → (Fin 2 → ℝ)` from `p` to `q` through `σ.toFun`,
producing a smooth path from `σ.toFun p` to `σ.toFun q`. -/
def affineSegmentPath (σ : Smooth2Simplex I X) (p q : Fin 2 → ℝ) :
    SmoothPath I X where
  src := σ.toFun p
  tgt := σ.toFun q
  toPath :=
    { toFun := fun t : unitInterval => σ.toFun (lineParam p q t.val)
      continuous_toFun :=
        ((σ.smooth.continuous.comp (lineParam_contMDiff p q).continuous).comp
          continuous_subtype_val)
      source' := by
        show σ.toFun (lineParam p q (0 : ℝ)) = σ.toFun p
        rw [lineParam_zero]
      target' := by
        show σ.toFun (lineParam p q (1 : ℝ)) = σ.toFun q
        rw [lineParam_one] }
  smooth := by
    refine ⟨fun t : ℝ => σ.toFun (lineParam p q t), ?_, ?_⟩
    · exact σ.smooth.comp (lineParam_contMDiff p q)
    · intro t
      rfl

@[simp] lemma affineSegmentPath_src (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) : (affineSegmentPath σ p q).src = σ.toFun p := rfl

@[simp] lemma affineSegmentPath_tgt (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) : (affineSegmentPath σ p q).tgt = σ.toFun q := rfl

@[simp] lemma affineSegmentPath_toPath_apply (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) (t : unitInterval) :
    (affineSegmentPath σ p q).toPath t = σ.toFun (lineParam p q t.val) := rfl

/-! ## Face identifications for `affineReparam` -/

/-- **`(affineReparam σ a b c).face0 = affineSegmentPath σ b c`** as
SmoothPaths. The face opposite `v₀` of the affine reparameterisation
is parameterised by `t ↦ σ(affineCombo a b c (1 - t, t))`, which equals
`σ(lineParam b c t)` since `affineCombo a b c (face0Param t) = lineParam b c t`. -/
lemma affineReparam_face0 (σ : Smooth2Simplex I X) (a b c : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam σ a b c).face0 = affineSegmentPath σ b c := by
  apply SmoothPath.ext
  · -- src
    show σ.toFun (affineCombo a b c Smooth2Simplex.v1) = σ.toFun b
    rw [affineCombo_v1]
  · -- tgt
    show σ.toFun (affineCombo a b c Smooth2Simplex.v2) = σ.toFun c
    rw [affineCombo_v2]
  · -- pointwise toPath
    intro t
    show σ.toFun (affineCombo a b c (Smooth2Simplex.face0Param t.val)) =
         σ.toFun (lineParam b c t.val)
    rw [affineCombo_face0Param_eq_lineParam]

/-- **`(affineReparam σ a b c).face1 = affineSegmentPath σ a c`** as
SmoothPaths. -/
lemma affineReparam_face1 (σ : Smooth2Simplex I X) (a b c : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam σ a b c).face1 = affineSegmentPath σ a c := by
  apply SmoothPath.ext
  · show σ.toFun (affineCombo a b c Smooth2Simplex.v0) = σ.toFun a
    rw [affineCombo_v0]
  · show σ.toFun (affineCombo a b c Smooth2Simplex.v2) = σ.toFun c
    rw [affineCombo_v2]
  · intro t
    show σ.toFun (affineCombo a b c (Smooth2Simplex.face1Param t.val)) =
         σ.toFun (lineParam a c t.val)
    rw [affineCombo_face1Param_eq_lineParam]

/-- **`(affineReparam σ a b c).face2 = affineSegmentPath σ a b`** as
SmoothPaths. -/
lemma affineReparam_face2 (σ : Smooth2Simplex I X) (a b c : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam σ a b c).face2 = affineSegmentPath σ a b := by
  apply SmoothPath.ext
  · show σ.toFun (affineCombo a b c Smooth2Simplex.v0) = σ.toFun a
    rw [affineCombo_v0]
  · show σ.toFun (affineCombo a b c Smooth2Simplex.v1) = σ.toFun b
    rw [affineCombo_v1]
  · intro t
    show σ.toFun (affineCombo a b c (Smooth2Simplex.face2Param t.val)) =
         σ.toFun (lineParam a b t.val)
    rw [affineCombo_face2Param_eq_lineParam]

/-! ## Reverse identity at the SmoothPath level

For any `p q : Fin 2 → ℝ`, the reversed `affineSegmentPath σ p q`
equals `affineSegmentPath σ q p` as a SmoothPath, by `SmoothPath.ext`:
endpoints swap as expected, and the pointwise parameter identity
`lineParam p q (1 - t) = lineParam q p t` from `lineParam_reverse`
matches the two toPath maps. -/

/-- **`(affineSegmentPath σ p q).reverse = affineSegmentPath σ q p`** as
SmoothPaths. -/
lemma affineSegmentPath_reverse (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) :
    (affineSegmentPath σ p q).reverse = affineSegmentPath σ q p := by
  apply SmoothPath.ext
  · -- src: `(reverse).src = σ q = (affineSegmentPath σ q p).src`.
    show (affineSegmentPath σ p q).tgt = σ.toFun q
    rfl
  · -- tgt: `(reverse).tgt = σ p = (affineSegmentPath σ q p).tgt`.
    show (affineSegmentPath σ p q).src = σ.toFun p
    rfl
  · -- Pointwise toPath: both equal `σ.toFun (lineParam q p t.val)`.
    intro t
    show (affineSegmentPath σ p q).toPath.symm t =
          σ.toFun (lineParam q p t.val)
    -- Unfold `Path.symm`: `(γ.symm) t = γ ⟨1 - t.val, _⟩`.
    show σ.toFun (lineParam p q (1 - t.val)) = σ.toFun (lineParam q p t.val)
    rw [lineParam_reverse]

end Smooth2Simplex

end JacobianChallenge

end
