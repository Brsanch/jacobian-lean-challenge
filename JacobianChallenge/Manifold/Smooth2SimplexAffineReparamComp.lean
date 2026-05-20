/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexAffineReparam

set_option linter.unusedSectionVars false

/-! # Composition identity for `affineCombo` / `affineReparam`

The affine reparameterisation `affineCombo v0' v1' v2'` is itself an
affine map; composing two of them yields another `affineCombo` whose
target vertices are the outer map's values on the inner map's
vertices. Stated as a `toFun`-level identity for `affineReparam`, this
flattens a depth-2 iterated reparameterisation into a single
reparameterisation. Downstream uses: structural flattening of
`iteratedMidpointList` into a `List` of single `affineReparam`s.

No `sorry`, no `axiom`. -/

noncomputable section

namespace JacobianChallenge

namespace Smooth2Simplex

/-- **Composition of two `affineCombo`s.**

For any six vectors in `Fin 2 → ℝ`,
`affineCombo a b c ∘ affineCombo a' b' c'`
equals `affineCombo` with vertices
`(affineCombo a b c a', affineCombo a b c b', affineCombo a b c c')`.

This is the algebraic fact that `affineCombo a b c` is an affine map
(coefficients `(1 - t₀ - t₁, t₀, t₁)` sum to `1`), hence commutes with
affine combinations. -/
@[simp] lemma affineCombo_comp (a b c a' b' c' : Fin 2 → ℝ) :
    affineCombo a b c ∘ affineCombo a' b' c'
    = affineCombo
        (affineCombo a b c a')
        (affineCombo a b c b')
        (affineCombo a b c c') := by
  funext t i
  simp only [Function.comp_apply, affineCombo,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]

/-- **`toFun`-level composition for `affineReparam`.**

`(affineReparam (affineReparam σ a b c) a' b' c').toFun`
agrees with
`(affineReparam σ (affineCombo a b c a') (affineCombo a b c b')
    (affineCombo a b c c')).toFun`
as functions on `Fin 2 → ℝ`. -/
@[simp] lemma affineReparam_comp_toFun (σ : Smooth2Simplex I X)
    (a b c a' b' c' : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam
        (Smooth2Simplex.affineReparam σ a b c) a' b' c').toFun
      = (Smooth2Simplex.affineReparam σ
          (affineCombo a b c a')
          (affineCombo a b c b')
          (affineCombo a b c c')).toFun := by
  -- Both sides reduce to `σ.toFun ∘ (some affineCombo composition)`;
  -- the equality of the `affineCombo` compositions is `affineCombo_comp`.
  -- `affineReparam_apply` is `rfl`, so simp doesn't make progress;
  -- congrArg + congrFun gives a direct proof.
  funext t
  exact congrArg σ.toFun (congrFun (affineCombo_comp a b c a' b' c') t)

/-- **Pointwise composition identity for `affineReparam`.** A more
ergonomic restatement of `affineReparam_comp_toFun`: evaluating an
iterated `affineReparam` at any point equals evaluating a single
`affineReparam` whose target vertices are the outer affine combination
of the inner vertices. -/
@[simp] lemma affineReparam_comp_apply (σ : Smooth2Simplex I X)
    (a b c a' b' c' : Fin 2 → ℝ) (t : Fin 2 → ℝ) :
    (Smooth2Simplex.affineReparam
        (Smooth2Simplex.affineReparam σ a b c) a' b' c').toFun t
      = (Smooth2Simplex.affineReparam σ
          (affineCombo a b c a')
          (affineCombo a b c b')
          (affineCombo a b c c')).toFun t :=
  congrFun (affineReparam_comp_toFun σ a b c a' b' c') t

end Smooth2Simplex

end JacobianChallenge

end
