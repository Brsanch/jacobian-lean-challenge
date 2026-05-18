/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereAntipodeSmooth
import JacobianChallenge.Manifold.RiemannSphereTranslate
import JacobianChallenge.Manifold.RiemannSphereRealManifold
import JacobianChallenge.Manifold.ContMDiffRealification

set_option linter.unusedSectionVars false

/-! # `mobiusComposed c`: smooth Möbius `RS → RS` sending `(some c) ↦ ∞`

Composes `antipode ∘ translateBy (-c)`:

* `translateBy (-c)` sends `(some c) ↦ (some 0)`, fixes `∞`.
* `antipode` sends `(some 0) ↦ ∞`, `∞ ↦ (some 0)`.

So `mobiusComposed c (some c) = antipode (some 0) = ∞`. The map is
smooth at `𝓘(ℂ, ℂ) ω` (composition of two `ω`-smooth maps) and
hence at `𝓘(ℝ, ℂ) ∞` (via `ContMDiff.complex_to_real`).

## What ships

* `mobiusComposed c : RS → RS := antipode ∘ translateBy (-c)`.
* `mobiusComposed_apply_some c : mobiusComposed c (some c) = ∞`.
* `contMDiff_mobiusComposed_real c :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (mobiusComposed c)`.

The inverse direction (`mobiusComposed`'s inverse exists smoothly and
sends `∞ ↦ (some c)`):

* `mobiusComposedInv c : RS → RS := translateBy c ∘ antipode`.
* `mobiusComposed_left_inv c x : mobiusComposedInv c (mobiusComposed c x) = x`.
* `contMDiff_mobiusComposedInv_real c`.

No `sorry`, no `axiom`. -/

open OnePoint
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- The Möbius transformation `antipode ∘ translateBy (-c)` sending
`(some c)` to `∞`. -/
noncomputable def mobiusComposed (c : ℂ) : RiemannSphere → RiemannSphere :=
  fun x => antipode (translateBy (-c) x)

/-- `mobiusComposed c (some c) = ∞`. Both the translation step
(`translateBy (-c) (some c) = some 0`) and the antipode step
(`antipode (some 0) = ∞`) are immediate from the defining equations. -/
@[simp] lemma mobiusComposed_apply_some (c : ℂ) :
    mobiusComposed c ((c : ℂ) : RiemannSphere) = (OnePoint.infty : RiemannSphere) := by
  unfold mobiusComposed
  -- translateBy (-c) (some c) = some (c + (-c)) = some 0.
  have h_trans : translateBy (-c) ((c : ℂ) : RiemannSphere)
      = ((0 : ℂ) : RiemannSphere) := by
    show ((((c + -c) : ℂ)) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)
    congr 1
    ring
  rw [h_trans, antipode_coe_zero]

/-- `mobiusComposed c` is `ω`-smooth as a self-map of `RS` (with the
complex model). -/
theorem contMDiff_mobiusComposed (c : ℂ) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ (mobiusComposed c) := by
  unfold mobiusComposed
  exact contMDiff_antipode.comp (contMDiff_translateBy (-c))

/-- `mobiusComposed c` is `C^∞` in the real-model. -/
theorem contMDiff_mobiusComposed_real (c : ℂ) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (mobiusComposed c) :=
  JacobianChallenge.ContMDiff.complex_to_real (contMDiff_mobiusComposed c)

/-! ## Inverse of `mobiusComposed c` -/

/-- The inverse Möbius map `translateBy c ∘ antipode`, sending `∞` to
`(some c)`. -/
noncomputable def mobiusComposedInv (c : ℂ) : RiemannSphere → RiemannSphere :=
  fun x => translateBy c (antipode x)

/-- `mobiusComposedInv c ∘ mobiusComposed c = id`. -/
lemma mobiusComposed_left_inv (c : ℂ) (x : RiemannSphere) :
    mobiusComposedInv c (mobiusComposed c x) = x := by
  unfold mobiusComposed mobiusComposedInv
  -- antipode is an involution, translateBy c ∘ translateBy (-c) = id.
  rw [antipode_antipode]
  -- Now: translateBy c (translateBy (-c) x) = x.
  induction x using OnePoint.rec with
  | infty =>
    -- translateBy (-c) ∞ = ∞; translateBy c ∞ = ∞.
    show OnePoint.rec _ _ (OnePoint.rec (∞ : RiemannSphere) _ (∞ : RiemannSphere))
      = (∞ : RiemannSphere)
    rfl
  | coe z =>
    show OnePoint.rec _ _
        (OnePoint.rec (∞ : RiemannSphere) _ ((z : ℂ) : RiemannSphere))
      = ((z : ℂ) : RiemannSphere)
    -- translateBy (-c) (some z) = some (z + (-c)) = some (z - c).
    -- translateBy c (some (z - c)) = some (z - c + c) = some z.
    show ((((z + -c) + c : ℂ)) : RiemannSphere)
      = (((z : ℂ)) : RiemannSphere)
    congr 1
    ring

/-- `mobiusComposed c ∘ mobiusComposedInv c = id`. -/
lemma mobiusComposed_right_inv (c : ℂ) (x : RiemannSphere) :
    mobiusComposed c (mobiusComposedInv c x) = x := by
  unfold mobiusComposed mobiusComposedInv
  -- translateBy (-c) (translateBy c (antipode x)) = antipode x (since translates compose to id).
  induction x using OnePoint.rec with
  | infty =>
    show antipode (OnePoint.rec _ _ (translateBy c (antipode (∞ : RiemannSphere))))
      = (∞ : RiemannSphere)
    rw [antipode_infty]
    show antipode (OnePoint.rec _ _
      (translateBy c (((0 : ℂ) : RiemannSphere)))) = (∞ : RiemannSphere)
    -- translateBy c (some 0) = some (0 + c) = some c.
    show antipode (OnePoint.rec _ _
      (((0 + c : ℂ) : RiemannSphere))) = (∞ : RiemannSphere)
    -- translateBy (-c) (some c) = some (c + (-c)) = some 0.
    -- antipode (some 0) = ∞.
    have h_arith : (0 + c : ℂ) = c := by ring
    show antipode ((((0 + c) + (-c) : ℂ) : RiemannSphere)) = (∞ : RiemannSphere)
    have h_eq : ((0 + c) + (-c) : ℂ) = 0 := by ring
    rw [show (((0 + c) + (-c) : ℂ) : RiemannSphere)
          = (((0 : ℂ) : RiemannSphere)) from by rw [h_eq]]
    exact antipode_coe_zero
  | coe z =>
    show antipode (translateBy (-c) (translateBy c (antipode ((z : ℂ) : RiemannSphere))))
      = ((z : ℂ) : RiemannSphere)
    -- antipode (some z) cases on z = 0 vs z ≠ 0.
    by_cases hz : z = 0
    · subst hz
      rw [antipode_coe_zero]
      show antipode (translateBy (-c) (translateBy c (∞ : RiemannSphere)))
        = (((0 : ℂ) : RiemannSphere))
      -- translateBy c ∞ = ∞; translateBy (-c) ∞ = ∞; antipode ∞ = some 0.
      show antipode (OnePoint.rec _ _ (OnePoint.rec (∞ : RiemannSphere) _ (∞ : RiemannSphere)))
        = (((0 : ℂ) : RiemannSphere))
      exact antipode_infty
    · rw [antipode_coe_of_ne hz]
      -- antipode (some z) = some (-z⁻¹). Now:
      -- translateBy c (some (-z⁻¹)) = some (-z⁻¹ + c).
      -- translateBy (-c) (some (-z⁻¹ + c)) = some (-z⁻¹ + c + (-c)) = some (-z⁻¹).
      -- antipode (some (-z⁻¹)) = some (-(-z⁻¹)⁻¹) = some z (since -1/(-1/z) = z) for z ≠ 0.
      show antipode (translateBy (-c) (translateBy c (((-z⁻¹ : ℂ) : RiemannSphere))))
        = (((z : ℂ) : RiemannSphere))
      show antipode (translateBy (-c) ((((-z⁻¹ + c : ℂ)) : RiemannSphere)))
        = (((z : ℂ) : RiemannSphere))
      show antipode ((((-z⁻¹ + c + (-c) : ℂ)) : RiemannSphere))
        = (((z : ℂ) : RiemannSphere))
      have h_arith : ((-z⁻¹ + c + (-c)) : ℂ) = -z⁻¹ := by ring
      rw [show (((-z⁻¹ + c + (-c) : ℂ)) : RiemannSphere)
            = (((-z⁻¹ : ℂ)) : RiemannSphere) from by rw [h_arith]]
      -- antipode (some (-z⁻¹)) = some z (since -z⁻¹ ≠ 0).
      have hnz : (-z⁻¹ : ℂ) ≠ 0 := by
        intro h
        apply hz
        have := neg_eq_zero.mp h
        exact inv_eq_zero.mp this
      rw [antipode_coe_of_ne hnz]
      congr 1
      field_simp

/-- `mobiusComposedInv c` is `ω`-smooth. -/
theorem contMDiff_mobiusComposedInv (c : ℂ) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ (mobiusComposedInv c) := by
  unfold mobiusComposedInv
  exact (contMDiff_translateBy c).comp contMDiff_antipode

/-- `mobiusComposedInv c` in the real model. -/
theorem contMDiff_mobiusComposedInv_real (c : ℂ) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (mobiusComposedInv c) :=
  JacobianChallenge.ContMDiff.complex_to_real (contMDiff_mobiusComposedInv c)

end RiemannSphere

end JacobianChallenge
