/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromGermfield

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Reducing `RR_DimGE2_GenusZero_Germ` to a single simple-pole hypothesis

The classical Riemann-Roch theorem at `D = δp` on a genus-0 surface
combines two pieces:

  (a) **Existence**: a meromorphic function with a simple pole at some
      `p` and no other poles.
  (b) **Finite-dimensionality**: `L(δp)` is a finite-dimensional
      ℂ-vector space (with `dim = deg + 1 - g + dim L(K - D) = 2`).

The germfield arc's downstream consumers (chips 5e and the Item14
capstone) only ever use the **strict-containment** consequence:

  `constantsGerm X < linearSystemGermDeltaP p` for some `p`,

which is *equivalent to* "L(δp) contains a non-constant germ" — exactly
(a). The finite-dimensionality (b) is needed only to translate
"2 ≤ finrank" into the strict containment, and is not needed in any
downstream proof. Skipping (b) makes the chain robust to the
finrank-vs-rank pitfall at the `finrank` definition.

## What this file delivers

* **`RR_StrictLt_GenusZero_Germ X : Prop`** — a strict-containment form
  of the classical Riemann-Roch + Serre input, weaker than the existing
  `RR_DimGE2_GenusZero_Germ` (which additionally encodes
  finite-dimensionality).

* **`RR_DimGE2_GenusZero_Germ X → RR_StrictLt_GenusZero_Germ X`** — the
  existing dim form is at least as strong.

* **`ExistsSimplePoleGermAtSomePoint X : Prop`** — the explicit
  "(a)-only" hypothesis: at some `p`, there is a germ in `L(δp)` with
  `orderAt p = -1`. Pure existence content, no dim count.

* **`existsSimplePoleGerm_implies_RR_StrictLt`** — the simple-pole
  hypothesis implies the strict-lt form. Proof: the constant `1` and
  the simple-pole germ have orders `0` and `-1` at `p`, distinct, so
  by mathlib's `meromorphicOrderAt_add_of_ne` no non-trivial linear
  combination vanishes — `linearSystemGermDeltaP p` properly contains
  `constantsGerm`.

* **`existsNonConstantBoundedByDeltaP_of_RR_StrictLt_Germ`,
  `riemannRochGenusZero_from_RR_StrictLt_Germ`** — the alternative
  composition chain bottoming out at `RiemannRochGenusZero X` via the
  weaker hypothesis. Composes with the existing chips.

* **`genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_top`** — the
  item-14 capstone using the simple-pole + top-sphere hypotheses,
  reducing item 14 to **one classical existence statement** plus the
  topological-sphere uniformization.

This pushes the open classical content for the RR side down from
"the full Riemann-Roch dimension formula at δp" to the cleaner
existence statement "there is a meromorphic function with a simple
pole at some point and no other poles". The latter is the *direct*
classical content (e.g. the period-mapping construction or the
Liouville-of-bounded-meromorphic argument); the dim formula is a
consequence.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Strict-containment form of RR -/

/-- **Named hypothesis (strict-containment form of RR at δp, genus 0,
germ field):** under `genus X = 0`, the linear system
`linearSystemGermDeltaP p` strictly contains `constantsGerm` for some
`p : X`.

Weaker than `RR_DimGE2_GenusZero_Germ` (which additionally encodes
finite-dimensionality of `L(δp)`), but sufficient for every downstream
RR use in the germfield arc. -/
def RR_StrictLt_GenusZero_Germ : Prop :=
  JacobianChallenge.genus X = 0 →
  ∃ p : X, constantsGerm X < linearSystemGermDeltaP (X := X) p

/-- **`RR_DimGE2_GenusZero_Germ X → RR_StrictLt_GenusZero_Germ X`.** The
existing dim form is at least as strong. -/
theorem RR_StrictLt_of_RR_DimGE2_GenusZero_Germ
    (hRR : RR_DimGE2_GenusZero_Germ X) :
    RR_StrictLt_GenusZero_Germ X := by
  intro hg
  obtain ⟨p, h_ge_2⟩ := hRR hg
  exact ⟨p, constantsGerm_lt_of_finrank_ge_two X h_ge_2⟩

/-! ## Simple-pole hypothesis -/

/-- **Named hypothesis:** at some point `p ∈ X`, the linear system
`L(δp)` contains a germ with `orderAt p = -1`. Concretely: there
exists a meromorphic function on `X` with a simple pole at `p` and no
other poles or worse-than-simple poles.

This is the explicit "(a)-only" piece of classical RR — pure existence
content, no dim count. -/
def ExistsSimplePoleGermAtSomePoint : Prop :=
  ∃ (p : X) (φ : MeromorphicFunctionGerm X),
    φ ∈ linearSystemGermDeltaP (X := X) p ∧
    φ.orderAt p = ((-1 : ℤ) : WithTop ℤ)

/-! ## Linear-independence and strict containment from a simple-pole germ -/

/-- Manifold-side counterpart of mathlib's `meromorphicOrderAt_add_of_ne`:
if two manifold-meromorphic functions have unequal orders at `y`, then
the order of their sum equals the minimum. -/
lemma mmeromorphicOrderAt_add_of_ne
    {f g : X → ℂ} {y : X}
    (hf : MMeromorphicAt 𝓘(ℂ, ℂ) f y) (hg : MMeromorphicAt 𝓘(ℂ, ℂ) g y)
    (h : mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y ≠ mmeromorphicOrderAt 𝓘(ℂ, ℂ) g y) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (f + g) y
      = min (mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y)
        (mmeromorphicOrderAt 𝓘(ℂ, ℂ) g y) := by
  show meromorphicOrderAt ((f + g) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
      = min (meromorphicOrderAt (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y))
            (meromorphicOrderAt (g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y))
  have h_unf : (f + g) ∘ (chartAt ℂ y).symm
      = (f ∘ (chartAt ℂ y).symm) + (g ∘ (chartAt ℂ y).symm) := rfl
  rw [h_unf]
  exact meromorphicOrderAt_add_of_ne hf hg h

/-- Order of a constant meromorphic function `(fun _ : X => c)` at any
`y` is `0` if `c ≠ 0` and `⊤` if `c = 0`. -/
lemma mmeromorphicOrderAt_const (c : ℂ) (y : X) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun _ : X => c) y
      = if c = 0 then (⊤ : WithTop ℤ) else (0 : WithTop ℤ) := by
  show meromorphicOrderAt ((fun _ : X => c) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
      = if c = 0 then (⊤ : WithTop ℤ) else (0 : WithTop ℤ)
  have h_eq : ((fun _ : X => c) ∘ (chartAt ℂ y).symm) = (fun _ : ℂ => c) := rfl
  rw [h_eq, meromorphicOrderAt_const]

/-- The germ of a constant function `MMer.const c` at `y` has order `0`
if `c ≠ 0`, else `⊤`. -/
lemma orderAt_constGerm (c : ℂ) (y : X) :
    (MeromorphicFunctionGerm.mk (MMer.const c : MMer X)).orderAt y
      = if c = 0 then (⊤ : WithTop ℤ) else (0 : WithTop ℤ) := by
  show mmeromorphicOrderAt 𝓘(ℂ, ℂ) (MMer.const c : MMer X).toFun y
      = if c = 0 then (⊤ : WithTop ℤ) else (0 : WithTop ℤ)
  show mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun _ : X => c) y
      = if c = 0 then (⊤ : WithTop ℤ) else (0 : WithTop ℤ)
  exact mmeromorphicOrderAt_const X c y

/-- **`ExistsSimplePoleGermAtSomePoint X → RR_StrictLt_GenusZero_Germ X`.**
The simple-pole hypothesis implies the strict-containment form
**unconditionally** (no genus hypothesis is used). -/
theorem RR_StrictLt_of_existsSimplePoleGerm
    (hSP : ExistsSimplePoleGermAtSomePoint X) :
    RR_StrictLt_GenusZero_Germ X := by
  intro _hg
  obtain ⟨p, φ, hφ_in, hφ_order⟩ := hSP
  refine ⟨p, ?_⟩
  -- Show `constantsGerm X < linearSystemGermDeltaP p`.
  refine lt_of_le_of_ne (constantsGerm_le_linearSystemGermDeltaP X p) ?_
  intro h_eq
  -- If equal: φ ∈ constantsGerm, i.e., φ = c • 1 for some c. Then orderAt p ≥ 0, contradicting -1.
  have hφ_in_const : φ ∈ constantsGerm X := h_eq ▸ hφ_in
  -- Extract: φ ∈ span ℂ {1}, so φ = c • 1 for some c.
  rw [constantsGerm, Submodule.mem_span_singleton] at hφ_in_const
  obtain ⟨c, hc⟩ := hφ_in_const
  -- `hc : c • (1 : MeromorphicFunctionGerm X) = φ`. Compute orderAt p of c • 1.
  have h_one : (1 : MeromorphicFunctionGerm X)
      = MeromorphicFunctionGerm.mk (1 : MMer X) := rfl
  have h_one_const : (1 : MMer X) = (MMer.const (1 : ℂ) : MMer X) := by
    ext z; show (1 : ℂ) = (1 : ℂ); rfl
  have hφ_eq : φ = MeromorphicFunctionGerm.mk (MMer.const c : MMer X) := by
    rw [← hc, h_one]
    show c • MeromorphicFunctionGerm.mk (1 : MMer X)
        = MeromorphicFunctionGerm.mk (MMer.const c : MMer X)
    rw [MeromorphicFunctionGerm.mk_smul]
    apply Quotient.sound
    intro y
    apply Filter.Eventually.of_forall
    intro z
    show (c • (1 : MMer X)).toFun z = (MMer.const c : MMer X).toFun z
    show c • (1 : ℂ) = c
    rw [smul_eq_mul, mul_one]
  -- So φ.orderAt p = orderAt of constant c, which is 0 (if c ≠ 0) or ⊤ (if c = 0).
  rw [hφ_eq, orderAt_constGerm] at hφ_order
  -- hφ_order : (if c = 0 then ⊤ else 0) = (-1 : WithTop ℤ).
  by_cases hc0 : c = 0
  · rw [if_pos hc0] at hφ_order
    -- ⊤ = -1, contradiction.
    exact absurd hφ_order WithTop.top_ne_coe
  · rw [if_neg hc0] at hφ_order
    -- 0 = -1, contradiction (in WithTop ℤ).
    have : ((0 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by
      have h0 : (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_cast
      rw [← h0]; exact hφ_order
    have := WithTop.coe_injective this
    omega

/-! ## Composition chain via the strict-lt form -/

/-- **`RR_StrictLt_GenusZero_Germ ⇒ ExistsNonConstantBoundedByDeltaP
_GenusZero`.** Strict containment yields an explicit non-constant
witness. -/
theorem existsNonConstantBoundedByDeltaP_of_RR_StrictLt_Germ
    (hRR : RR_StrictLt_GenusZero_Germ X) :
    JacobianChallenge.ExistsNonConstantBoundedByDeltaP_GenusZero X := by
  intro hg
  obtain ⟨p, hlt⟩ := hRR hg
  obtain ⟨φ, hφ_in, hφ_not⟩ :=
    exists_mem_linearSystemGermDeltaP_not_in_constantsGerm X hlt
  obtain ⟨f, h_off, h_p, h_nc⟩ :=
    MeromorphicFunctionGerm.liftToMeromorphicNonzero hφ_in hφ_not
  refine ⟨p, f, h_off, h_p, h_nc⟩

/-- **Unconditional reduction of `RiemannRochGenusZero` to
`RR_StrictLt_GenusZero_Germ`.** -/
theorem riemannRochGenusZero_from_RR_StrictLt_Germ
    (hRR : RR_StrictLt_GenusZero_Germ X) :
    JacobianChallenge.RiemannRochGenusZero X :=
  JacobianChallenge.riemannRochGenusZero_from_existsBoundedByDeltaP X
    (existsNonConstantBoundedByDeltaP_of_RR_StrictLt_Germ X hRR)

/-- **Unconditional reduction of `RiemannRochGenusZero` to
`ExistsSimplePoleGermAtSomePoint`.** Composes the simple-pole reduction
with the strict-lt composition. -/
theorem riemannRochGenusZero_from_ExistsSimplePoleGerm
    (hSP : ExistsSimplePoleGermAtSomePoint X) :
    JacobianChallenge.RiemannRochGenusZero X :=
  riemannRochGenusZero_from_RR_StrictLt_Germ X
    (RR_StrictLt_of_existsSimplePoleGerm X hSP)

/-! ## Item 14 capstone: from simple-pole + top-sphere -/

/-- **Item 14 from a simple-pole germ existence + top-sphere
uniformization.** -/
theorem genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_top
    (hSP : ExistsSimplePoleGermAtSomePoint X)
    (h_top : Nonempty (X ≃ₜ JacobianChallenge.StandardS2) →
      Nonempty (JacobianChallenge.HolomorphicEquiv X
        JacobianChallenge.RiemannSphere)) :
    JacobianChallenge.genus X = 0 ↔
      Nonempty (X ≃ₜ JacobianChallenge.StandardS2) :=
  JacobianChallenge.genus_eq_zero_iff_homeo_from_all_conditionals
    (riemannRochGenusZero_from_ExistsSimplePoleGerm X hSP)
    (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
      X JacobianChallenge.RiemannSphere)
    (JacobianChallenge.surjective_of_NonConstant_Analytic_Manifold_holds
      (X := X) (Y := JacobianChallenge.RiemannSphere))
    (JacobianChallenge.bijectiveAnalyticIsBiholomorphism_holds (X := X))
    h_top

end JacobianChallenge.MeromorphicFunctionField

end
