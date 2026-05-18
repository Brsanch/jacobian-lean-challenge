/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConcat

set_option linter.unusedSectionVars false

/-! # Bump-half reparameterisations of a smooth path

Two smooth-path reparameterisations of `γ` that arise as the
"side faces" of `Smooth2Simplex.ofSmoothPathConcat`:

* `SmoothPath.bumpedHalfLeft γ` — same src/tgt as `γ`, with ambient
  function `t ↦ γ.ambient (concatRepLeft (t / 2))`. At unitInterval
  parameter `t ∈ [0, 1]`, the argument `t/2 ∈ [0, 1/2]`, and
  `concatRepLeft` traces `[0, 1]` smoothly with flat zones at the
  endpoints. So this path is the bump-flattened-near-endpoints
  reparameterisation of `γ`.

* `SmoothPath.bumpedHalfRight δ` — same src/tgt as `δ`, with ambient
  function `t ↦ δ.ambient (concatRepRight ((1 + t) / 2))`. Symmetric
  construction for the right half of the concat ambient.

These are used to identify `face2` and `face0` of the concat 2-simplex
with explicit `SmoothPath` terms (separate chip).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-! ## Smoothness of the half-reparam maps -/

/-- The map `t ↦ concatRepLeft (t / 2)` is C^∞ on `ℝ`. -/
lemma contDiff_concatRepLeft_half :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => concatRepLeft (t / 2)) := by
  have h_div : ContDiff ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => t / 2) := by
    have h_id : ContDiff ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => t) := contDiff_id
    have h_const : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ => (2 : ℝ)) := contDiff_const
    exact h_id.div h_const (fun _ => by norm_num)
  exact contDiff_concatRepLeft.comp h_div

/-- The map `t ↦ concatRepRight ((1 + t) / 2)` is C^∞ on `ℝ`. -/
lemma contDiff_concatRepRight_shift :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun t : ℝ => concatRepRight ((1 + t) / 2)) := by
  have h_div : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun t : ℝ => (1 + t) / 2) := by
    have h_id : ContDiff ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => t) := contDiff_id
    have h_one : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ => (1 : ℝ)) :=
      contDiff_const
    have h_sum : ContDiff ℝ (∞ : WithTop ℕ∞)
        (fun t : ℝ => 1 + t) := h_one.add h_id
    have h_two : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ => (2 : ℝ)) :=
      contDiff_const
    exact h_sum.div h_two (fun _ => by norm_num)
  exact contDiff_concatRepRight.comp h_div

/-! ## Endpoint identities -/

/-- `concatRepLeft (0 / 2) = 0`. -/
@[simp] lemma concatRepLeft_half_zero : concatRepLeft ((0 : ℝ) / 2) = 0 := by
  have h : (0 : ℝ) / 2 = 0 := by norm_num
  rw [h, concatRepLeft_zero]

/-- `concatRepLeft (1 / 2) = 1`. (Since `1/2 ≥ 3/8`.) -/
@[simp] lemma concatRepLeft_half_one : concatRepLeft ((1 : ℝ) / 2) = 1 := by
  exact concatRepLeft_eq_one_of_ge (1/2) (by norm_num)

/-- `concatRepRight ((1 + 0) / 2) = 0`. (Since `1/2 ≤ 5/8`.) -/
@[simp] lemma concatRepRight_shift_zero :
    concatRepRight ((1 + (0 : ℝ)) / 2) = 0 := by
  have h_arg : (1 + (0 : ℝ)) / 2 = 1/2 := by norm_num
  rw [h_arg]
  exact concatRepRight_eq_zero_of_le (1/2) (by norm_num)

/-- `concatRepRight ((1 + 1) / 2) = 1`. (Since `1 ≥ 7/8`.) -/
@[simp] lemma concatRepRight_shift_one :
    concatRepRight ((1 + (1 : ℝ)) / 2) = 1 := by
  have h_arg : (1 + (1 : ℝ)) / 2 = 1 := by norm_num
  rw [h_arg, concatRepRight_one]

/-! ## The bumped-half reparameterised paths -/

/-- `γ.ambient 0 = γ.src`. -/
lemma ambient_zero_eq_src (γ : SmoothPath I X) :
    γ.ambient 0 = γ.src := by
  have h0_val : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
      = 0 := rfl
  have heq := γ.ambient_eq_on_unitInterval
    ⟨0, by constructor <;> norm_num⟩
  rw [h0_val] at heq
  rw [heq]
  exact γ.toPath.source'

/-- `γ.ambient 1 = γ.tgt`. -/
lemma ambient_one_eq_tgt (γ : SmoothPath I X) :
    γ.ambient 1 = γ.tgt := by
  have h1_val : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
      = 1 := rfl
  have heq := γ.ambient_eq_on_unitInterval
    ⟨1, by constructor <;> norm_num⟩
  rw [h1_val] at heq
  rw [heq]
  exact γ.toPath.target'

/-- The C^∞ ambient `t ↦ γ.ambient (concatRepLeft (t / 2))` is C^∞ as a
manifold map `𝓘(ℝ, ℝ) → I`. -/
lemma contMDiff_bumpedHalfLeftAmbient (γ : SmoothPath I X) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => γ.ambient (concatRepLeft (t / 2))) := by
  have h_inner : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => concatRepLeft (t / 2)) :=
    contDiff_concatRepLeft_half.contMDiff
  exact γ.ambient_contMDiff.comp h_inner

/-- The C^∞ ambient `t ↦ δ.ambient (concatRepRight ((1 + t) / 2))`. -/
lemma contMDiff_bumpedHalfRightAmbient (δ : SmoothPath I X) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => δ.ambient (concatRepRight ((1 + t) / 2))) := by
  have h_inner : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => concatRepRight ((1 + t) / 2)) :=
    contDiff_concatRepRight_shift.contMDiff
  exact δ.ambient_contMDiff.comp h_inner

/-- **The left-bumped-half reparameterisation of a smooth path.**

`bumpedHalfLeft γ` is a `SmoothPath` from `γ.src` to `γ.tgt` with
ambient `t ↦ γ.ambient (concatRepLeft (t / 2))`. -/
noncomputable def bumpedHalfLeft (γ : SmoothPath I X) : SmoothPath I X where
  src := γ.src
  tgt := γ.tgt
  toPath :=
    { toFun := fun t : unitInterval => γ.ambient (concatRepLeft (t.val / 2))
      continuous_toFun := by
        have h_contMDiff := γ.contMDiff_bumpedHalfLeftAmbient
        have h_cont : Continuous
            (fun t : ℝ => γ.ambient (concatRepLeft (t / 2))) :=
          h_contMDiff.continuous
        exact h_cont.comp continuous_subtype_val
      source' := by
        show γ.ambient (concatRepLeft ((0 : ℝ) / 2)) = γ.src
        rw [concatRepLeft_half_zero]
        exact γ.ambient_zero_eq_src
      target' := by
        show γ.ambient (concatRepLeft ((1 : ℝ) / 2)) = γ.tgt
        rw [concatRepLeft_half_one]
        exact γ.ambient_one_eq_tgt }
  smooth :=
    ⟨fun t : ℝ => γ.ambient (concatRepLeft (t / 2)),
      γ.contMDiff_bumpedHalfLeftAmbient,
      fun _ => rfl⟩

/-- **The right-bumped-half reparameterisation of a smooth path.**

`bumpedHalfRight δ` is a `SmoothPath` from `δ.src` to `δ.tgt` with
ambient `t ↦ δ.ambient (concatRepRight ((1 + t) / 2))`. -/
noncomputable def bumpedHalfRight (δ : SmoothPath I X) : SmoothPath I X where
  src := δ.src
  tgt := δ.tgt
  toPath :=
    { toFun := fun t : unitInterval =>
        δ.ambient (concatRepRight ((1 + t.val) / 2))
      continuous_toFun := by
        have h_contMDiff := δ.contMDiff_bumpedHalfRightAmbient
        have h_cont : Continuous
            (fun t : ℝ => δ.ambient (concatRepRight ((1 + t) / 2))) :=
          h_contMDiff.continuous
        exact h_cont.comp continuous_subtype_val
      source' := by
        show δ.ambient (concatRepRight ((1 + (0 : ℝ)) / 2)) = δ.src
        rw [concatRepRight_shift_zero]
        exact δ.ambient_zero_eq_src
      target' := by
        show δ.ambient (concatRepRight ((1 + (1 : ℝ)) / 2)) = δ.tgt
        rw [concatRepRight_shift_one]
        exact δ.ambient_one_eq_tgt }
  smooth :=
    ⟨fun t : ℝ => δ.ambient (concatRepRight ((1 + t) / 2)),
      δ.contMDiff_bumpedHalfRightAmbient,
      fun _ => rfl⟩

@[simp] lemma bumpedHalfLeft_src (γ : SmoothPath I X) :
    (γ.bumpedHalfLeft).src = γ.src := rfl

@[simp] lemma bumpedHalfLeft_tgt (γ : SmoothPath I X) :
    (γ.bumpedHalfLeft).tgt = γ.tgt := rfl

@[simp] lemma bumpedHalfLeft_toPath_apply (γ : SmoothPath I X)
    (t : unitInterval) :
    (γ.bumpedHalfLeft).toPath t
      = γ.ambient (concatRepLeft (t.val / 2)) := rfl

@[simp] lemma bumpedHalfRight_src (δ : SmoothPath I X) :
    (δ.bumpedHalfRight).src = δ.src := rfl

@[simp] lemma bumpedHalfRight_tgt (δ : SmoothPath I X) :
    (δ.bumpedHalfRight).tgt = δ.tgt := rfl

@[simp] lemma bumpedHalfRight_toPath_apply (δ : SmoothPath I X)
    (t : unitInterval) :
    (δ.bumpedHalfRight).toPath t
      = δ.ambient (concatRepRight ((1 + t.val) / 2)) := rfl

end SmoothPath

end
