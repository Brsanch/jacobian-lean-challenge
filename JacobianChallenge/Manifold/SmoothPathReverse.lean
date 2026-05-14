/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConst
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathConnected
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # `SmoothPath.reverse` and `SmoothPathConnected` equivalence-relation lemmas

Companion primitive to `SmoothPath.concat`. Given a smooth path
`γ : SmoothPath I X` from `γ.src` to `γ.tgt`, builds the reversed
smooth path `γ.reverse : SmoothPath I X` from `γ.tgt` to `γ.src`.

## Construction

* Underlying continuous path: `γ.toPath.symm` (mathlib's `Path.symm`,
  reparameterised as `t ↦ γ.toPath ⟨1 - t.val, _⟩`).
* Ambient extension: `fun t : ℝ => γ.ambient (1 - t)`. C^∞ on `ℝ` by
  composition of `γ.ambient_contMDiff` with the affine map
  `t ↦ 1 - t`. Agreement on `unitInterval` follows from
  `γ.ambient_eq_on_unitInterval` evaluated at `⟨1 - t.val, _⟩`.

## What this file delivers

* `SmoothPath.reverseAmbient γ : ℝ → X` — the C^∞ ambient
  `t ↦ γ.ambient (1 - t)`.
* `SmoothPath.contMDiff_reverseAmbient` — C^∞ proof.
* `SmoothPath.reverse γ : SmoothPath I X` — the reversed smooth path,
  with `src = γ.tgt` and `tgt = γ.src`.
* `SmoothPath.reverse_src` / `reverse_tgt` — endpoint identities.
* `SmoothPathConnected.refl` — every `p : X` is connected to itself
  (via `SmoothPath.const`).
* `SmoothPathConnected.symm` — `(∃ γ, γ.src = p ∧ γ.tgt = q) ⇒
   (∃ γ', γ'.src = q ∧ γ'.tgt = p)`, via `reverse`.
* `SmoothPathConnected.trans` — composition via `concat`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-! ## Reverse ambient -/

/-- The reverse ambient of a smooth path: `t ↦ γ.ambient (1 - t)`. -/
def reverseAmbient (γ : SmoothPath I X) : ℝ → X :=
  fun t => γ.ambient (1 - t)

/-- The reverse ambient is C^∞ globally on `ℝ`. The affine map
`t ↦ 1 - t` is C^∞, and `γ.ambient` is C^∞ as the smoothness witness
of `γ`; composition is C^∞. -/
lemma contMDiff_reverseAmbient (γ : SmoothPath I X) :
    ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) (γ.reverseAmbient) := by
  intro t
  have h_affine : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => 1 - s) t := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => 1 - s) :=
      contDiff_const.sub contDiff_id
    exact h.contMDiff t
  have h_amb : ContMDiffAt 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞)
      γ.ambient (1 - t) := γ.ambient_contMDiff (1 - t)
  exact h_amb.comp t h_affine

/-! ## Endpoint identities for `γ.ambient`

These are the projections of `Path.source'` / `Path.target'` through
`γ.ambient_eq_on_unitInterval` at `t = 0` and `t = 1`. They are
reproduced here (instead of imported from another file) because the
corresponding lemmas in `Manifold/SmoothPathConcat.lean` are
`private` to that file. -/

private lemma ambient_zero_eq_src (γ : SmoothPath I X) :
    γ.ambient 0 = γ.src := by
  have h0_val : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
      = 0 := rfl
  have heq := γ.ambient_eq_on_unitInterval
    ⟨0, by constructor <;> norm_num⟩
  rw [h0_val] at heq
  rw [heq]
  exact γ.toPath.source'

private lemma ambient_one_eq_tgt (γ : SmoothPath I X) :
    γ.ambient 1 = γ.tgt := by
  have h1_val : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
      = 1 := rfl
  have heq := γ.ambient_eq_on_unitInterval
    ⟨1, by constructor <;> norm_num⟩
  rw [h1_val] at heq
  rw [heq]
  exact γ.toPath.target'

/-! ## Endpoint identities for reverseAmbient -/

private lemma reverseAmbient_zero (γ : SmoothPath I X) :
    γ.reverseAmbient 0 = γ.tgt := by
  unfold reverseAmbient
  simp only [sub_zero]
  exact γ.ambient_one_eq_tgt

private lemma reverseAmbient_one (γ : SmoothPath I X) :
    γ.reverseAmbient 1 = γ.src := by
  unfold reverseAmbient
  simp only [sub_self]
  exact γ.ambient_zero_eq_src

/-! ## The reversed smooth path -/

/-- **Reverse of a smooth path.** Given `γ : SmoothPath I X` from
`γ.src` to `γ.tgt`, produces a smooth path from `γ.tgt` to `γ.src`
via `Path.symm` for the continuous part and the bumped reverse
ambient. -/
noncomputable def reverse (γ : SmoothPath I X) : SmoothPath I X where
  src := γ.tgt
  tgt := γ.src
  toPath := γ.toPath.symm
  smooth := by
    refine ⟨γ.reverseAmbient, γ.contMDiff_reverseAmbient, ?_⟩
    intro t
    -- Goal: γ.reverseAmbient t.val = γ.toPath.symm t.
    -- mathlib's `Path.symm γ = γ ∘ σ` where `σ : unitInterval → unitInterval`
    -- sends `t ↦ ⟨1 - t.val, _⟩`. So `γ.symm t = γ.toPath ⟨1 - t.val, _⟩`,
    -- which by `ambient_eq_on_unitInterval` equals `γ.ambient (1 - t.val)`.
    show γ.ambient (1 - t.val) = γ.toPath.symm t
    have h_symm_val : (unitInterval.symm t).val = 1 - t.val := rfl
    have h_eq := γ.ambient_eq_on_unitInterval (unitInterval.symm t)
    rw [h_symm_val] at h_eq
    rw [h_eq]
    rfl

@[simp] lemma reverse_src (γ : SmoothPath I X) : γ.reverse.src = γ.tgt := rfl

@[simp] lemma reverse_tgt (γ : SmoothPath I X) : γ.reverse.tgt = γ.src := rfl

end SmoothPath

/-! ## `SmoothPathConnected` equivalence-relation lemmas

The smooth-path-connected predicate becomes an equivalence relation
on `X` (when `Nonempty X`): reflexivity via `SmoothPath.const`,
symmetry via `SmoothPath.reverse`, transitivity via
`SmoothPath.concat`. -/

namespace JacobianChallenge

namespace SmoothPathConnected

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **Reflexivity-flavored existence.** Every `p : X` is connected to
itself by the constant smooth path `SmoothPath.const I X p`. This
matches `SmoothPathConnected.diagonal` (already in
`Manifold/SmoothPathConnected.lean`) but exposes a slightly different
phrasing useful for the equivalence-relation packaging. -/
lemma exists_smoothPath_self (p : X) :
    ∃ γ : SmoothPath I X, γ.src = p ∧ γ.tgt = p :=
  ⟨SmoothPath.const I X p, SmoothPath.const_src p, SmoothPath.const_tgt p⟩

/-- **Symmetry of smooth-path-connectedness.** A smooth path from `p`
to `q` gives one from `q` to `p` (via `SmoothPath.reverse`). -/
lemma exists_smoothPath_symm {p q : X}
    (h : ∃ γ : SmoothPath I X, γ.src = p ∧ γ.tgt = q) :
    ∃ γ' : SmoothPath I X, γ'.src = q ∧ γ'.tgt = p := by
  obtain ⟨γ, hp, hq⟩ := h
  refine ⟨γ.reverse, ?_, ?_⟩
  · rw [SmoothPath.reverse_src]; exact hq
  · rw [SmoothPath.reverse_tgt]; exact hp

/-- **Transitivity of smooth-path-connectedness.** Smooth paths
`p → q` and `q → r` compose to a smooth path `p → r` via
`SmoothPath.concat`. -/
lemma exists_smoothPath_trans {p q r : X}
    (h₁ : ∃ γ : SmoothPath I X, γ.src = p ∧ γ.tgt = q)
    (h₂ : ∃ δ : SmoothPath I X, δ.src = q ∧ δ.tgt = r) :
    ∃ γ : SmoothPath I X, γ.src = p ∧ γ.tgt = r := by
  obtain ⟨γ, hγ_src, hγ_tgt⟩ := h₁
  obtain ⟨δ, hδ_src, hδ_tgt⟩ := h₂
  have h_eq : γ.tgt = δ.src := by rw [hγ_tgt, hδ_src]
  refine ⟨γ.concat δ h_eq, ?_, ?_⟩
  · rw [SmoothPath.concat_src]; exact hγ_src
  · rw [SmoothPath.concat_tgt]; exact hδ_tgt

end SmoothPathConnected

end JacobianChallenge

end
