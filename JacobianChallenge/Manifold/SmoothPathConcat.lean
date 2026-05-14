/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathConst
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # Smooth-path-connectedness primitive 3: `SmoothPath.concat`

Builds the binary concatenation `γ ⋆ δ : SmoothPath I X` of two smooth
paths sharing an endpoint (`γ.tgt = δ.src`). This primitive depends
crucially on the C^∞ refactor of `SmoothPath` (2026-05-15): at the
analytic regularity `ω`, smooth concatenation is generically obstructed
because analytic germs are determined globally and cannot in general
agree across a junction unless the two paths analytically continue each
other. At C^∞ regularity, smooth bumps can flatten both paths near the
junction so that they are constant in a neighborhood of the join — a
standard partition-of-unity trick.

## Construction

Let `σ = Real.smoothTransition`. Define two reparameterisations:

* `concatRepLeft t := σ(4 (t - 1/8))` — C^∞ on `ℝ`, equals `0` for
  `t ≤ 1/8` and `1` for `t ≥ 3/8`.
* `concatRepRight t := σ(4 (t - 5/8))` — C^∞ on `ℝ`, equals `0` for
  `t ≤ 5/8` and `1` for `t ≥ 7/8`.

The concatenated ambient function `g : ℝ → X` is defined piecewise:

    `g t = if t ≤ 1/2 then γ.ambient (concatRepLeft t)
                       else δ.ambient (concatRepRight t)`

Key flat-zone identities ensure the join at `t = 1/2` is smooth:

* For `t ∈ [3/8, 1/2]`: `concatRepLeft t = 1`, so the left piece is the
  constant `γ.ambient 1 = γ.tgt`.
* For `t ∈ [1/2, 5/8]`: `concatRepRight t = 0`, so the right piece is
  the constant `δ.ambient 0 = δ.src`.

Under the gluing hypothesis `γ.tgt = δ.src`, both pieces equal the
common junction point on `(3/8, 5/8)`. The piecewise function `g` is
therefore constant on this open neighborhood of `1/2`, hence C^∞ at
the junction. Outside the junction region, the function locally agrees
with one of the two C^∞ pieces and is C^∞ there as well.

## What this file delivers

* `SmoothPath.concatRepLeft` / `concatRepRight` — the
  `Real.smoothTransition`-based reparameterisations and their flat-zone
  identities.
* `SmoothPath.contMDiff_concatRepLeft` / `_concatRepRight` — C^∞
  smoothness of the reparameterisations as manifold maps
  `𝓘(ℝ, ℝ) → 𝓘(ℝ, ℝ)`.
* `SmoothPath.concatAmbient γ δ : ℝ → X` — the piecewise ambient.
* `SmoothPath.concatAmbient_eqOn_left` / `_right` / `_middle` —
  local-identity lemmas for the three regions.
* `SmoothPath.concatAmbient_zero` / `_one` — endpoint identities.
* `SmoothPath.contMDiff_concatAmbient` — global C^∞-smoothness under
  `γ.tgt = δ.src`.
* `SmoothPath.concat γ δ h : SmoothPath I X` — the concatenation.
* `SmoothPath.concat_src` / `concat_tgt` — endpoint identities.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-! ## Bump-flatten reparameterisations -/

/-- Left half-interval reparameterisation: `concatRepLeft t = σ(4(t - 1/8))`
where `σ = Real.smoothTransition`. C^∞ on `ℝ`, identically `0` on
`(-∞, 1/8]` and identically `1` on `[3/8, ∞)`. Used to smooth-flatten
`γ.ambient` near `t = 1/2` for the concatenation. -/
def concatRepLeft (t : ℝ) : ℝ := Real.smoothTransition (4 * (t - 1/8))

/-- Right half-interval reparameterisation: `concatRepRight t = σ(4(t - 5/8))`.
C^∞ on `ℝ`, identically `0` on `(-∞, 5/8]` and identically `1` on
`[7/8, ∞)`. Used to smooth-flatten `δ.ambient` near `t = 1/2` for the
concatenation. -/
def concatRepRight (t : ℝ) : ℝ := Real.smoothTransition (4 * (t - 5/8))

@[simp] lemma concatRepLeft_zero : concatRepLeft 0 = 0 := by
  unfold concatRepLeft
  have h : (4 : ℝ) * (0 - 1/8) ≤ 0 := by norm_num
  exact Real.smoothTransition.zero_of_nonpos h

@[simp] lemma concatRepRight_one : concatRepRight 1 = 1 := by
  unfold concatRepRight
  have h : (1 : ℝ) ≤ 4 * (1 - 5/8) := by norm_num
  exact Real.smoothTransition.one_of_one_le h

/-- For `t ≥ 3/8`, the left reparameterisation saturates to `1`. -/
lemma concatRepLeft_eq_one_of_ge (t : ℝ) (h : 3/8 ≤ t) :
    concatRepLeft t = 1 := by
  unfold concatRepLeft
  have h' : (1 : ℝ) ≤ 4 * (t - 1/8) := by linarith
  exact Real.smoothTransition.one_of_one_le h'

/-- For `t ≤ 5/8`, the right reparameterisation is identically `0`. -/
lemma concatRepRight_eq_zero_of_le (t : ℝ) (h : t ≤ 5/8) :
    concatRepRight t = 0 := by
  unfold concatRepRight
  have h' : (4 : ℝ) * (t - 5/8) ≤ 0 := by linarith
  exact Real.smoothTransition.zero_of_nonpos h'

/-- `concatRepLeft` is C^∞ on `ℝ`. -/
lemma contDiff_concatRepLeft : ContDiff ℝ ∞ concatRepLeft := by
  unfold concatRepLeft
  have h_inner : ContDiff ℝ ∞ (fun t : ℝ => 4 * (t - 1/8)) :=
    (contDiff_const.mul (contDiff_id.sub contDiff_const))
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp h_inner

/-- `concatRepRight` is C^∞ on `ℝ`. -/
lemma contDiff_concatRepRight : ContDiff ℝ ∞ concatRepRight := by
  unfold concatRepRight
  have h_inner : ContDiff ℝ ∞ (fun t : ℝ => 4 * (t - 5/8)) :=
    (contDiff_const.mul (contDiff_id.sub contDiff_const))
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp h_inner

/-- Manifold-side smoothness of `concatRepLeft` at C^∞. -/
lemma contMDiff_concatRepLeft :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ concatRepLeft :=
  contDiff_concatRepLeft.contMDiff

/-- Manifold-side smoothness of `concatRepRight` at C^∞. -/
lemma contMDiff_concatRepRight :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ concatRepRight :=
  contDiff_concatRepRight.contMDiff

/-! ## Concatenated ambient -/

/-- The ambient extension `ℝ → X` of the concatenation `γ ⋆ δ`,
piecewise: `γ.ambient (concatRepLeft t)` on `(-∞, 1/2]` and
`δ.ambient (concatRepRight t)` on `(1/2, ∞)`. The bump-flatten
reparameterisations make both pieces locally constant near `t = 1/2`,
so the piecewise definition is C^∞ globally under
`γ.tgt = δ.src`. -/
def concatAmbient (γ δ : SmoothPath I X) : ℝ → X :=
  fun t => if t ≤ 1/2 then γ.ambient (concatRepLeft t)
                       else δ.ambient (concatRepRight t)

/-- `γ.ambient 0 = γ.src` — projected from
`ambient_eq_on_unitInterval` at `t = 0` plus `Path.source'`. Stated
as an auxiliary for the concatenation endpoint identities. -/
private lemma ambient_zero_eq_src (γ : SmoothPath I X) :
    γ.ambient 0 = γ.src := by
  have h0_val : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
      = 0 := rfl
  have heq := γ.ambient_eq_on_unitInterval
    ⟨0, by constructor <;> norm_num⟩
  rw [h0_val] at heq
  rw [heq]
  exact γ.toPath.source'

/-- `γ.ambient 1 = γ.tgt` — projected from `ambient_eq_on_unitInterval`
at `t = 1` plus `Path.target'`. -/
private lemma ambient_one_eq_tgt (γ : SmoothPath I X) :
    γ.ambient 1 = γ.tgt := by
  have h1_val : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
      = 1 := rfl
  have heq := γ.ambient_eq_on_unitInterval
    ⟨1, by constructor <;> norm_num⟩
  rw [h1_val] at heq
  rw [heq]
  exact γ.toPath.target'

@[simp] lemma concatAmbient_zero (γ δ : SmoothPath I X) :
    γ.concatAmbient δ 0 = γ.src := by
  show (if (0 : ℝ) ≤ 1/2 then γ.ambient (concatRepLeft 0)
                          else δ.ambient (concatRepRight 0)) = γ.src
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 1/2), concatRepLeft_zero]
  exact γ.ambient_zero_eq_src

@[simp] lemma concatAmbient_one (γ δ : SmoothPath I X) :
    γ.concatAmbient δ 1 = δ.tgt := by
  show (if (1 : ℝ) ≤ 1/2 then γ.ambient (concatRepLeft 1)
                          else δ.ambient (concatRepRight 1)) = δ.tgt
  rw [if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1/2), concatRepRight_one]
  exact δ.ambient_one_eq_tgt

/-! ## Local-identity lemmas -/

/-- On the closed left half `t ≤ 1/2`, the concatenation ambient
agrees with `γ.ambient ∘ concatRepLeft`. -/
lemma concatAmbient_eqOn_left (γ δ : SmoothPath I X) :
    Set.EqOn (γ.concatAmbient δ)
      (fun t => γ.ambient (concatRepLeft t))
      (Set.Iic (1/2 : ℝ)) := by
  intro t ht
  show (if t ≤ 1/2 then γ.ambient (concatRepLeft t)
                    else δ.ambient (concatRepRight t))
      = γ.ambient (concatRepLeft t)
  exact if_pos ht

/-- On the open right half `t > 1/2`, the concatenation ambient agrees
with `δ.ambient ∘ concatRepRight`. -/
lemma concatAmbient_eqOn_right (γ δ : SmoothPath I X) :
    Set.EqOn (γ.concatAmbient δ)
      (fun t => δ.ambient (concatRepRight t))
      (Set.Ioi (1/2 : ℝ)) := by
  intro t ht
  show (if t ≤ 1/2 then γ.ambient (concatRepLeft t)
                    else δ.ambient (concatRepRight t))
      = δ.ambient (concatRepRight t)
  exact if_neg (not_le.mpr ht)

/-- **Middle flat zone.** On the open interval `(3/8, 5/8)`, the
concatenation ambient is constantly equal to the junction point
`γ.tgt = δ.src`. This is the key C^∞-glue identity that makes the
piecewise definition smooth at `t = 1/2`. -/
lemma concatAmbient_eqOn_middle (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) :
    Set.EqOn (γ.concatAmbient δ) (fun _ => γ.tgt)
      (Set.Ioo (3/8 : ℝ) (5/8)) := by
  intro t ht
  obtain ⟨ht_lo, ht_hi⟩ := ht
  show (if t ≤ 1/2 then γ.ambient (concatRepLeft t)
                    else δ.ambient (concatRepRight t)) = γ.tgt
  by_cases ht_half : t ≤ 1/2
  · rw [if_pos ht_half, concatRepLeft_eq_one_of_ge t (by linarith)]
    exact γ.ambient_one_eq_tgt
  · rw [if_neg ht_half, concatRepRight_eq_zero_of_le t
        (by push Not at ht_half; linarith)]
    rw [δ.ambient_zero_eq_src]
    exact h.symm

/-! ## Global C^∞-smoothness of the concatenated ambient -/

/-- **Concatenated ambient is C^∞ globally.** Proven by local
case-analysis on the value of `t`:
* `t < 1/2`: function agrees with `γ.ambient ∘ concatRepLeft` on a
  neighborhood, both C^∞.
* `t > 1/2`: function agrees with `δ.ambient ∘ concatRepRight` on a
  neighborhood, both C^∞.
* `t = 1/2`: function is constantly `γ.tgt` on the open neighborhood
  `(3/8, 5/8)`, hence C^∞. -/
lemma contMDiff_concatAmbient (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (γ.concatAmbient δ) := by
  intro t
  rcases lt_trichotomy t (1/2 : ℝ) with ht | ht | ht
  · -- t < 1/2: agree with γ.ambient ∘ concatRepLeft on (..., 1/2).
    have h_open : IsOpen (Set.Iio (1/2 : ℝ)) := isOpen_Iio
    have h_mem : t ∈ Set.Iio (1/2 : ℝ) := ht
    have h_eq : Set.EqOn (γ.concatAmbient δ)
        (fun s => γ.ambient (concatRepLeft s)) (Set.Iio (1/2 : ℝ)) :=
      (concatAmbient_eqOn_left γ δ).mono Set.Iio_subset_Iic_self
    have h_target : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
        (fun s => γ.ambient (concatRepLeft s)) t := by
      have h_inner : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ concatRepLeft t :=
        contMDiff_concatRepLeft t
      have h_outer : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ.ambient (concatRepLeft t) :=
        γ.ambient_contMDiff (concatRepLeft t)
      exact h_outer.comp t h_inner
    exact h_target.congr_of_eventuallyEq
      (h_eq.eventuallyEq_of_mem (h_open.mem_nhds h_mem))
  · -- t = 1/2: function = γ.tgt on (3/8, 5/8).
    have h_open : IsOpen (Set.Ioo (3/8 : ℝ) (5/8)) := isOpen_Ioo
    have h_mem : t ∈ Set.Ioo (3/8 : ℝ) (5/8) := by
      rw [ht]; constructor <;> norm_num
    have h_eq := concatAmbient_eqOn_middle γ δ h
    have h_target : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun _ : ℝ => γ.tgt) t :=
      contMDiffAt_const
    exact h_target.congr_of_eventuallyEq
      (h_eq.eventuallyEq_of_mem (h_open.mem_nhds h_mem))
  · -- t > 1/2: agree with δ.ambient ∘ concatRepRight on (1/2, ...).
    have h_open : IsOpen (Set.Ioi (1/2 : ℝ)) := isOpen_Ioi
    have h_mem : t ∈ Set.Ioi (1/2 : ℝ) := ht
    have h_eq : Set.EqOn (γ.concatAmbient δ)
        (fun s => δ.ambient (concatRepRight s)) (Set.Ioi (1/2 : ℝ)) :=
      concatAmbient_eqOn_right γ δ
    have h_target : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
        (fun s => δ.ambient (concatRepRight s)) t := by
      have h_inner : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ concatRepRight t :=
        contMDiff_concatRepRight t
      have h_outer : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ δ.ambient (concatRepRight t) :=
        δ.ambient_contMDiff (concatRepRight t)
      exact h_outer.comp t h_inner
    exact h_target.congr_of_eventuallyEq
      (h_eq.eventuallyEq_of_mem (h_open.mem_nhds h_mem))

/-! ## The concatenation -/

/-- **Concatenation of two smooth paths.** Given `γ : SmoothPath I X`
with `γ.tgt = δ.src` for some `δ : SmoothPath I X`, build the
concatenation `γ.concat δ h : SmoothPath I X` from `γ.src` to `δ.tgt`.
The ambient is `concatAmbient γ δ`, C^∞ globally on `ℝ` by
`contMDiff_concatAmbient`. The continuous `Path` representation
restricts `concatAmbient` to `unitInterval`. -/
noncomputable def concat (γ δ : SmoothPath I X) (h : γ.tgt = δ.src) :
    SmoothPath I X where
  src := γ.src
  tgt := δ.tgt
  toPath :=
    { toFun := fun t : unitInterval => γ.concatAmbient δ t.val
      continuous_toFun :=
        ((γ.contMDiff_concatAmbient δ h).continuous).comp continuous_subtype_val
      source' := by
        have h0 : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
            = 0 := rfl
        show γ.concatAmbient δ
            ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val) = γ.src
        rw [h0]
        exact γ.concatAmbient_zero δ
      target' := by
        have h1 : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
            = 1 := rfl
        show γ.concatAmbient δ
            ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val) = δ.tgt
        rw [h1]
        exact γ.concatAmbient_one δ }
  smooth := ⟨γ.concatAmbient δ, γ.contMDiff_concatAmbient δ h,
    fun _ => rfl⟩

@[simp] lemma concat_src (γ δ : SmoothPath I X) (h : γ.tgt = δ.src) :
    (γ.concat δ h).src = γ.src := rfl

@[simp] lemma concat_tgt (γ δ : SmoothPath I X) (h : γ.tgt = δ.src) :
    (γ.concat δ h).tgt = δ.tgt := rfl

end SmoothPath

end
