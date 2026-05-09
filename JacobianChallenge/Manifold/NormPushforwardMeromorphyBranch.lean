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
import Mathlib.FieldTheory.IsAlgClosed.Basic
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
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) (_hg : MeromorphicAt g 0)
    {F : ℂ → ℂ} (hF_mero : MeromorphicAt F 0)
    (hF_descent : (fun s : ℂ => F (s ^ k)) =ᶠ[nhds (0 : ℂ)] auxProdMuK g k) :
    MeromorphicAt (normPow g k) 0 := by
  classical
  -- We will show `F =ᶠ[𝓝[≠] 0] normPow g k` and apply `MeromorphicAt.congr`.
  -- Step 1: extract a metric ball on which the descent holds.
  have hF_event : ∀ᶠ s in nhds (0 : ℂ), F (s ^ k) = auxProdMuK g k s := hF_descent
  rw [Metric.eventually_nhds_iff_ball] at hF_event
  obtain ⟨ε, hε_pos, hε_descent⟩ := hF_event
  -- Step 2: inside `Metric.ball (0 : ℂ) (ε ^ k)`, every nonzero point `t` is
  -- a `k`-th power `s^k` with `s ∈ ball 0 ε`.  We use `Complex` algebraic
  -- closure: pick `s := t ^ (1 / k)` via the principal branch of `cpow`.
  -- A more elementary route, sufficient here, is to use that `nthRootsFinset
  -- k t` is nonempty (as a fact about ℂ) and pick any element with the
  -- required size estimate.
  -- Step 3: assemble the eventual equality `F =ᶠ[𝓝[≠] 0_t] normPow g k`.
  --
  -- We argue at the level of metric balls.  Set `δ := ε ^ k > 0`.  For any
  -- `t ∈ ball (0 : ℂ) δ`, pick `s := t ^ (1 / (k : ℂ))` (principal `cpow`):
  -- this satisfies `‖s‖ = ‖t‖ ^ (1/k) < δ ^ (1/k) = ε` and `s ^ k = t` for
  -- `t ≠ 0`.  Hence `F t = F (s^k) = auxProdMuK g k s = normPow g k (s^k) = normPow g k t`.
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  set δ : ℝ := ε ^ k with hδ_def
  have hδ_pos : 0 < δ := pow_pos hε_pos k
  -- Assemble the eventual equality on `𝓝[≠] 0_t`.
  have h_t : F =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] normPow g k := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Metric.ball (0 : ℂ) δ ∩ {(0 : ℂ)}ᶜ, ?_, ?_⟩
    · rw [mem_nhdsWithin]
      exact ⟨Metric.ball (0 : ℂ) δ, Metric.isOpen_ball,
             Metric.mem_ball_self hδ_pos, fun _ h => h⟩
    · intro t ht
      rcases ht with ⟨ht_ball, ht_ne⟩
      have ht_ne' : t ≠ 0 := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht_ne
      have ht_norm : ‖t‖ < δ := by
        simpa [Metric.mem_ball, dist_zero_right] using ht_ball
      -- Pick any k-th root of t (algebraic closure of ℂ).
      obtain ⟨s, hs_pow⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) t hk_pos
      have hs_ne : s ≠ 0 := by
        intro h
        rw [h, zero_pow hk_ne] at hs_pow
        exact ht_ne' hs_pow.symm
      -- Norm bound: ‖s‖^k = ‖s^k‖ = ‖t‖ < ε^k, so ‖s‖ < ε (using k ≥ 1).
      have hs_norm_pow : ‖s‖ ^ k = ‖t‖ := by
        rw [← norm_pow]; rw [hs_pow]
      have hs_norm_lt : ‖s‖ < ε := by
        have h_pow_lt : ‖s‖ ^ k < ε ^ k := by
          rw [hs_norm_pow]; exact ht_norm
        exact lt_of_pow_lt_pow_left₀ k hε_pos.le h_pow_lt
      have hs_in_ball : s ∈ Metric.ball (0 : ℂ) ε := by
        simpa [Metric.mem_ball, dist_zero_right] using hs_norm_lt
      have hs_descent : F (s ^ k) = auxProdMuK g k s :=
        hε_descent s (by simpa [Metric.mem_ball, dist_zero_right] using hs_norm_lt)
      have hbridge : normPow g k (s ^ k) = auxProdMuK g k s :=
        normPow_eq_auxProdMuK_pow_of_ne_zero g hk hs_ne
      -- Combine: `F t = F (s^k) = auxProdMuK g k s = normPow g k (s^k) = normPow g k t`.
      calc F t = F (s ^ k) := by rw [hs_pow]
        _ = auxProdMuK g k s := hs_descent
        _ = normPow g k (s ^ k) := hbridge.symm
        _ = normPow g k t := by rw [hs_pow]
  -- Apply `MeromorphicAt.congr`.
  exact hF_mero.congr h_t

end Manifold
end JacobianChallenge

end
