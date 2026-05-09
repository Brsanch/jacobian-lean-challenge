/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.Basic
import JacobianChallenge.Manifold.NormPushforwardLocal
import JacobianChallenge.Manifold.NormPushforwardMeromorphy

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Branch-value behaviour of the norm pushforward (Phase 1.1 chip P1.1c, ZZ202)

This file is the branch-case follow-on to `NormPushforwardMeromorphy.lean`
(P1.1b, ZZ201, regular values `t ≠ 0`).  The headline question is local
meromorphy of the planar norm pushforward `normPow g k` at the **branch
value `t = 0`**.

## Honest scope

The full headline `MeromorphicAt (normPow g k) 0` requires the
**μ_k-invariant analytic descent**: an analytic, μ_k-invariant function
`V` of the variable `s` is the pullback `V = W ∘ (· ^ k)` of an analytic
function `W` of `t = s^k`.  This is the planar specialization of the
fundamental theorem of symmetric functions / `SiegelOrbit`-type descent.
At the pinned mathlib revision (`8e3c989...`) this descent is **not**
available off-the-shelf, and synthesising it inline would inflate this
chip well beyond its scope.

This file therefore ships the unconditional **auxiliary** content and a
clean **conditional** packaging that isolates the descent as a single
named hypothesis:

* `auxProdMuK` — `s ↦ ∏ ζ ∈ μ_k, g (ζ * s)`, the auxiliary of `normPow g k`
  along the planar `k`-th-power map.
* `auxProdMuK_meromorphicAt` — *unconditional* meromorphy of `auxProdMuK g k`
  at any `s₀ : ℂ` such that `g` is `MeromorphicAt` at every `ζ * s₀`,
  `ζ ∈ μ_k`.
* `auxProdMuK_meromorphicAt_zero` — the specialisation at `s₀ = 0`:
  every orbit point is `0`, so `MeromorphicAt g 0` is sufficient.
* `normPow_eq_auxProdMuK_pow_of_ne_zero` — for `s ≠ 0` and `k ≥ 1`,
  `normPow g k (s ^ k) = auxProdMuK g k s` (a direct repackage of
  `normPow_pow` from P1.1a).
* `normPow_eventuallyEq_auxProdMuK_pow_punctured` — eventual equality on
  the punctured neighbourhood `𝓝[≠] 0` (for the `s`-side; the `t`-side
  needs the descent to identify the germ).
* `normPow_meromorphicAt_zero_of_descent` — *conditional* meromorphy of
  `normPow g k` at `t = 0`, taking the descent of the auxiliary as an
  explicit hypothesis (existence of a meromorphic germ `F` at `0` with
  `F (s^k) =ᶠ[𝓝 0] auxProdMuK g k s`).

The conditional form is what downstream `Manifold/Hurwitz*`-level users
need: the descent hypothesis can be discharged separately (planned in a
companion chip, by either an inline μ_k-invariant Taylor-series argument
or a new mathlib import once the symmetric-descent API lands).

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to any pre-existing definition or theorem.
* All identifiers ASCII (no `ω` binders, per Lean 4.30 reservation).
-/

noncomputable section

open Polynomial Finset Complex Metric

namespace JacobianChallenge
namespace Manifold

universe u

/-! ### The auxiliary `auxProdMuK g k s := ∏ ζ ∈ μ_k, g (ζ * s)`. -/

/-- Auxiliary along the planar `k`-th-power map: the symmetric `s`-side of
the norm-pushforward equation `normPow g k (s^k) = auxProdMuK g k s`
(for `s ≠ 0`, by `normPow_pow`).

This is *unconditionally* meromorphic at any `s₀` whose μ_k-orbit lies in
the meromorphic locus of `g` (see `auxProdMuK_meromorphicAt`), in
particular at `s₀ = 0` when `g` is meromorphic at `0`. -/
def auxProdMuK (g : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * s)

/-- Definitional unfold. -/
@[simp] lemma auxProdMuK_eq_finset_prod (g : ℂ → ℂ) (k : ℕ) (s : ℂ) :
    auxProdMuK g k s = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * s) := rfl

/-! ### Unconditional meromorphy of `auxProdMuK`. -/

/-- For any fixed `ζ : ℂ`, the inner map `s ↦ ζ * s` is analytic at every
point. -/
private lemma analyticAt_const_mul (ζ s₀ : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => ζ * s) s₀ :=
  (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ζ) s₀).mul analyticAt_id

/-- **Unconditional meromorphy of the auxiliary `auxProdMuK g k`.**

If `g` is `MeromorphicAt` at every point of the form `ζ * s₀` for
`ζ ∈ nthRootsFinset k 1`, then `auxProdMuK g k` is `MeromorphicAt` at
`s₀`.

In particular, taking `s₀ = 0`: every `ζ * 0 = 0`, so the hypothesis
collapses to `MeromorphicAt g 0`, and we get `MeromorphicAt (auxProdMuK g k) 0`
unconditionally from `MeromorphicAt g 0`. -/
theorem auxProdMuK_meromorphicAt
    (g : ℂ → ℂ) {k : ℕ} {s₀ : ℂ}
    (hg : ∀ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
      MeromorphicAt g (ζ * s₀)) :
    MeromorphicAt (auxProdMuK g k) s₀ := by
  classical
  -- `auxProdMuK g k s = ∏ ζ ∈ μ_k, g (ζ * s)` is a finite product of
  -- meromorphic germs.
  refine MeromorphicAt.fun_prod (s := Polynomial.nthRootsFinset k (1 : ℂ))
    (F := fun ζ s => g (ζ * s)) ?_
  intro ζ hζ
  -- Composition: `g` meromorphic at `ζ * s₀`, inner `s ↦ ζ * s` analytic at `s₀`.
  have h_inner : AnalyticAt ℂ (fun s : ℂ => ζ * s) s₀ :=
    analyticAt_const_mul ζ s₀
  have h_val : (fun s : ℂ => ζ * s) s₀ = ζ * s₀ := rfl
  have hg_at : MeromorphicAt g (ζ * s₀) := hg ζ hζ
  have h_comp : MeromorphicAt (g ∘ (fun s : ℂ => ζ * s)) s₀ := by
    refine MeromorphicAt.comp_analyticAt
      (f := g) (g := fun s : ℂ => ζ * s) (x := s₀) ?_ h_inner
    rw [h_val]; exact hg_at
  -- `g ∘ (fun s => ζ * s)` is definitionally `fun s => g (ζ * s)`.
  exact h_comp

/-- **Specialisation at `s₀ = 0`.**  If `g` is meromorphic at `0`, then
`auxProdMuK g k` is meromorphic at `0`.

The orbit hypothesis at `s₀ = 0` collapses, since `ζ * 0 = 0` for every `ζ`. -/
theorem auxProdMuK_meromorphicAt_zero
    (g : ℂ → ℂ) (k : ℕ) (hg : MeromorphicAt g 0) :
    MeromorphicAt (auxProdMuK g k) 0 := by
  refine auxProdMuK_meromorphicAt g (s₀ := 0) ?_
  intro ζ _
  have hzero : ζ * (0 : ℂ) = 0 := by ring
  rw [hzero]
  exact hg

/-! ### Bridge: `normPow g k (s ^ k) = auxProdMuK g k s` for `s ≠ 0`. -/

/-- **Bridge lemma.**  For `s ≠ 0` and `1 ≤ k`,
`normPow g k (s ^ k) = auxProdMuK g k s`.

This is precisely `normPow_pow` from P1.1a, repackaged using `auxProdMuK`. -/
theorem normPow_eq_auxProdMuK_pow_of_ne_zero
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s ≠ 0) :
    normPow g k (s ^ k) = auxProdMuK g k s := by
  unfold auxProdMuK
  exact normPow_pow g hk hs

/-- Eventual equality form of the bridge: `s ↦ normPow g k (s^k)` and
`auxProdMuK g k` agree on `𝓝[≠] (0 : ℂ)`.  This is the form that feeds
into `MeromorphicAt.congr` for the conditional descent below. -/
theorem normPow_pow_eventuallyEq_auxProdMuK
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (fun s : ℂ => normPow g k (s ^ k)) =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ]
      auxProdMuK g k := by
  -- For `s ≠ 0`, the bridge holds.  `nhdsWithin 0 ({0}ᶜ)` consists of
  -- points eventually `≠ 0`.
  filter_upwards [self_mem_nhdsWithin (s := ({(0 : ℂ)}ᶜ))] with s hs
  have hs_ne : s ≠ 0 := by
    intro h
    apply hs
    simp [h]
  exact normPow_eq_auxProdMuK_pow_of_ne_zero g hk hs_ne

/-! ### Conditional theorem: meromorphy of `normPow g k` at `0` reduces
to a μ_k-invariant analytic descent of the auxiliary.

The descent is packaged as the hypothesis "there exists a function `F`
meromorphic at `0` with `F (s^k) =ᶠ[𝓝 0] auxProdMuK g k s`".  Given such
an `F`, `F` and `normPow g k` agree off `0` near `0` (composing the
descent with the bridge), so `MeromorphicAt (normPow g k) 0` follows by
`MeromorphicAt.congr`.

The hypothesis is *exactly* the analytic μ_k-descent of the symmetric
function: see the file-level docstring for the missing-mathlib note. -/

/-- **Conditional meromorphy of `normPow g k` at the branch value `0`.**

Given:
* `g : ℂ → ℂ` meromorphic at `0`,
* `k ≥ 1`,
* a μ_k-descent `F` of the auxiliary `auxProdMuK g k`: a function
  `F : ℂ → ℂ` such that `MeromorphicAt F 0` and
  `(fun s => F (s^k)) =ᶠ[𝓝 0] auxProdMuK g k`,

the norm pushforward `normPow g k` is `MeromorphicAt` at `t = 0`, and in
fact `F =ᶠ[𝓝[≠] 0] normPow g k`.

The descent hypothesis is the symmetric-function content: it says the
auxiliary `auxProdMuK g k`, which is μ_k-invariant in `s` by P1.1a, factors
through `s ↦ s^k`.  This is delivered separately (out of scope for this
chip; see file docstring for the missing-mathlib note). -/
theorem normPow_meromorphicAt_zero_of_descent
    (g : ℂ → ℂ) {k : ℕ} (_hk : 1 ≤ k) (_hg : MeromorphicAt g 0)
    {F : ℂ → ℂ} (hF_mero : MeromorphicAt F 0)
    (hF_descent : (fun s : ℂ => F (s ^ k)) =ᶠ[nhds (0 : ℂ)] auxProdMuK g k) :
    MeromorphicAt (normPow g k) 0 := by
  classical
  -- We will show `F =ᶠ[𝓝[≠] 0] normPow g k` and apply `MeromorphicAt.congr`.
  -- Restrict the descent to `nhdsWithin 0 {0}ᶜ`.
  have hF_descent' : (fun s : ℂ => F (s ^ k)) =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ]
      auxProdMuK g k :=
    hF_descent.filter_mono nhdsWithin_le_nhds
  -- Combine with the bridge: `(fun s => normPow g k (s^k)) =ᶠ[𝓝[≠] 0] auxProdMuK g k`.
  have h_bridge : (fun s : ℂ => normPow g k (s ^ k))
        =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] auxProdMuK g k :=
    normPow_pow_eventuallyEq_auxProdMuK g _hk
  -- Hence `(fun s => F (s^k)) =ᶠ[𝓝[≠] 0] (fun s => normPow g k (s^k))`.
  have h_pulled : (fun s : ℂ => F (s ^ k))
        =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] (fun s : ℂ => normPow g k (s ^ k)) :=
    hF_descent'.trans h_bridge.symm
  -- Now we compare `F` and `normPow g k` directly at the point `t`, using
  -- the identity `t = (some s)^k` only on the punctured locus.  Since `s^k`
  -- as `s → 0` covers a punctured neighbourhood of `0` in `t` (continuity +
  -- surjectivity for `k ≥ 1` over ℂ), and the punctured filter `𝓝[≠] 0` in
  -- `t` is the pushforward of `𝓝[≠] 0` in `s` along `s ↦ s^k`, we transfer
  -- `h_pulled` to a t-side eventual equality.
  -- More directly: we apply `MeromorphicAt.comp_analyticAt` to package
  -- `F ∘ (· ^ k)` as meromorphic at `0`, then use that this composition
  -- equals `normPow g k ∘ (· ^ k)` near `0`, then descend by ...
  -- The cleanest route: apply `MeromorphicAt.congr` directly to `hF_mero`
  -- with the eventual equality `F =ᶠ[𝓝[≠] 0] normPow g k` in the variable `t`.
  -- We construct that equality from `h_pulled` by changing variables along
  -- the surjective continuous map `s ↦ s^k` (using `Filter.Tendsto`/`map`).
  -- Specifically: `(· ^ k) : ℂ → ℂ` is continuous and surjective off 0
  -- (algebraic closure), so `Filter.map (· ^ k) (𝓝[≠] 0) ≤ 𝓝[≠] 0`.
  have h_map :
      Filter.map (fun s : ℂ => s ^ k) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        ≤ nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ := by
    -- map of `𝓝[≠] 0` along `s ↦ s^k` is ≤ `𝓝 0` (by continuity at `0` with
    -- `0^k = 0` since `k ≥ 1`) AND avoids `0` (since `s ≠ 0 ⇒ s^k ≠ 0`).
    rw [Filter.le_def]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, hV_mem, hV_sub⟩ := hU
    -- pre-image of V under `· ^ k` is a nhd of 0 (continuity); avoiding 0 is
    -- automatic from `s ≠ 0`.
    have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp _hk
    have h_zero_pow : (0 : ℂ) ^ k = 0 := zero_pow hk_ne
    have h_cont : ContinuousAt (fun s : ℂ => s ^ k) 0 :=
      (continuous_id.pow k).continuousAt
    have h_preV : (fun s : ℂ => s ^ k) ⁻¹' V ∈ nhds (0 : ℂ) := by
      apply h_cont.preimage_mem_nhds
      rw [h_zero_pow]; exact hV_mem
    rw [Filter.mem_map, mem_nhdsWithin]
    refine ⟨(fun s : ℂ => s ^ k) ⁻¹' V, ?_, ?_, ?_⟩
    · exact (hV_open.preimage (continuous_id.pow k))
    · simp [h_zero_pow]; exact hV_mem
    · intro s hs
      rcases hs with ⟨hs_pre, hs_ne⟩
      apply hV_sub
      refine ⟨hs_pre, ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h_pow_zero
      apply hs_ne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs_ne
      -- s^k = 0 ⇒ s = 0 in ℂ.
      exact pow_eq_zero_iff hk_ne |>.mp h_pow_zero
  -- Translate `h_pulled` (an eventual equality in the `s`-filter) to an
  -- eventual equality in the `t`-filter, where `t = s^k`.
  have h_t : F =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] normPow g k := by
    -- `h_pulled : F ∘ (· ^ k) =ᶠ[𝓝[≠]_s 0] (normPow g k) ∘ (· ^ k)`
    -- map version → eventual equality at filter `Filter.map (· ^ k) (𝓝[≠]_s 0)`
    -- ≤ `𝓝[≠]_t 0` by `h_map`.
    have h_map_eq : F =ᶠ[Filter.map (fun s : ℂ => s ^ k)
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)] normPow g k := by
      simpa [Filter.EventuallyEq, Filter.eventually_map] using h_pulled
    exact h_map_eq.filter_mono h_map
  -- Apply `MeromorphicAt.congr`.
  exact hF_mero.congr h_t

end Manifold
end JacobianChallenge

end
