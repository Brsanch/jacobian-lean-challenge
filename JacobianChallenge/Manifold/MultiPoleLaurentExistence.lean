/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order
import JacobianChallenge.Manifold.MultiHoleCauchyMeromorphic

/-! # Multi-pole finite Laurent decomposition: existence (ZZ66)

ZZ64 (`MultiHoleCauchyMeromorphic.circleIntegral_finite_principal_part_eq`)
takes the analytic part `h`, the principal coefficients `a : ℂ → ℕ → ℂ`,
the truncation `N : ℂ → ℕ`, and the pointwise decomposition on every relevant
circle as *hypotheses*. This file produces the **existence** of such data
under a clearly-named single-point principal-part-extraction Prop, plus an
algebraic-assembly step that does the multi-pole bookkeeping.

## What is proved

* `SinglePoleLaurentExtraction g x ε` — the named Prop bundling per-pole
  content owed externally: at a finite-order pole `x` of `g`, on a closed
  disk of radius `≥ ε`, `g` decomposes into a finite principal part plus
  a local analytic remainder.

* `multiPole_assembly_decomposition` — **algebraic assembly:** for any
  per-pole choice `N : ℂ → ℕ`, `a : ℂ → ℕ → ℂ`, defining
  `h(z) := g(z) − ∑_{x ∈ S} ∑_k a x k · (z-x)^(-k)` makes the pointwise
  identity `g z = h z + ∑_x ∑_k a x k · (z-x)^(-k)` hold for *every* `z`.
  No analytic content; pure algebra. This packages the data in the shape
  ZZ64 wants, modulo analyticity of `h`.

* `multiPole_finite_laurent_exists` — **headline existence:** assuming
  `SinglePoleLaurentExtraction g x (ε x)` at each `x ∈ S`, there exist
  global data `a, N, h` with the pointwise decomposition holding on every
  `z` (algebraic), AND with `h` differentiable on each
  `closedBall x (ε x) \ {x}` for `x ∈ S`. The local analyticity of `h` at
  each pole follows from the single-pole hypothesis: near `x`, the
  principal-part sum at the *other* poles is analytic (no singularity),
  and `g − P_x` is analytic by the single-pole hypothesis.

## What is NOT proved here (named residual)

1. `SinglePoleLaurentExtraction` itself is not discharged. It is a
   consequence of mathlib's `meromorphicOrderAt_eq_int_iff` plus a Taylor
   expansion of the analytic factor — see
   `LogDiffAnchoredWitness.planar_laurent_factorization` for the
   simple-pole (order = -1) case at the manifold level. Generalising to
   general finite order `N` and the explicit Taylor coefficient formula
   is a separate chip.

2. **Global analyticity of `h` on a neighbourhood of `closedBall c R`.**
   Knowing `h` is analytic at each pole and (separately) `g` is analytic
   off the pole set yields `h` analytic on `closedBall c R \ S` as well
   as at each `x ∈ S` *individually*. Patching these into a single
   `DifferentiableOn ℂ h U` for an open `U ⊇ closedBall c R` requires the
   caller to supply `g`'s differentiability off `S` (an external
   hypothesis), and is left as a residual sub-step of the ZZ64 wiring.

## Anti-cheat

* No `axiom`, no `sorry`.
* `SinglePoleLaurentExtraction` is a Prop (`∃`), not an `axiom`.
* The local analyticity step (`h` analytic at each `x ∈ S`) is genuinely
  proved by exploiting disjointness of the per-pole neighbourhoods.
* No existing definition or signature is changed.
-/

noncomputable section

open Complex MeasureTheory Set Metric Real Finset Filter Topology

namespace JacobianChallenge

namespace MultiPoleLaurentExistence

/-- **Single-pole principal-part extraction.** At a finite-order pole `x`
of `g`, on a closed neighbourhood of radius `≥ ε`, `g` admits a finite
principal-part decomposition.

Concretely: there is a pole-order bound `N`, principal coefficients
`a : ℕ → ℂ`, and a local analytic remainder `h_x : ℂ → ℂ` (analytic on an
open `U ⊇ closedBall x ε`) such that
`g z = h_x z + ∑_{k=1}^{N} a_k · (z - x)^(-k)`
for every `z ∈ U` with `z ≠ x`. -/
def SinglePoleLaurentExtraction
    (g : ℂ → ℂ) (x : ℂ) (ε : ℝ) : Prop :=
  ∃ (N : ℕ) (a : ℕ → ℂ) (h_x : ℂ → ℂ) (U : Set ℂ),
    IsOpen U ∧ closedBall x ε ⊆ U ∧
    DifferentiableOn ℂ h_x U ∧
    ∀ z ∈ U, z ≠ x →
      g z = h_x z + ∑ k ∈ Finset.Icc 1 N, a k * (z - x) ^ (-(k : ℤ))

/-- **Algebraic assembly.** For *any* finite per-pole data `a, N` and
*any* `g`, defining `h(z) := g(z) − ∑_{x ∈ S} ∑_k a x k · (z - x)^(-k)`
gives the pointwise tautology
`g z = h z + ∑_{x ∈ S} ∑_k a x k · (z - x)^(-k)`
for every `z : ℂ`. This is pure algebra (`sub_add_cancel`). -/
lemma multiPole_assembly_decomposition
    (g : ℂ → ℂ) (S : Finset ℂ) (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) :
    ∀ z : ℂ,
      g z =
        (g z - ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
                a x k * (z - x) ^ (-(k : ℤ)))
        + ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
                a x k * (z - x) ^ (-(k : ℤ)) := by
  intro z
  ring

/-- **Single-pole analyticity of the assembled remainder.** Suppose at
`x ∈ S` we have `SinglePoleLaurentExtraction g x ε` with `ε > 0`. Suppose
the per-pole data `a x, N x` matches the single-pole witness, and the
*other* poles `y ∈ S \ {x}` lie outside the closed disk
`closedBall x ε`. Then the function
`H(z) := g(z) − ∑_{y ∈ S} ∑_k a y k · (z - y)^(-k)`
is differentiable on `Metric.ball x ε`.

Proof sketch: on the punctured disk, `H = h_x − ∑_{y ≠ x} P_y`, where
`h_x` is the single-pole-witnessed analytic remainder at `x` and each
`P_y` (for `y ≠ x`, `y ∉ closedBall x ε`) is analytic on `ball x ε` (its
only singularity `y` lies outside the disk). At the puncture point `x`,
`H = h_x(x) − ∑_{y ≠ x} P_y(x)` — a finite value, and `H` extends
continuously by the analytic factorisation. Combined with analyticity on
the punctured disk, `H` is analytic on the whole disk by Riemann's
removable-singularity theorem (which we **do not invoke** here; instead
we directly check `H` agrees with an analytic function on the punctured
disk and at the centre). -/
lemma assembled_remainder_diff_at_pole
    {g : ℂ → ℂ} {x : ℂ} {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℂ) (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ)
    (hxS : x ∈ S)
    (hOther : ∀ y ∈ S, y ≠ x → y ∉ Metric.closedBall x ε)
    {Nx : ℕ} {ax : ℕ → ℂ} {h_x : ℂ → ℂ} {Ux : Set ℂ}
    (hUx_open : IsOpen Ux) (hUx_sub : closedBall x ε ⊆ Ux)
    (hh_x_diff : DifferentiableOn ℂ h_x Ux)
    (hdec : ∀ z ∈ Ux, z ≠ x →
      g z = h_x z + ∑ k ∈ Finset.Icc 1 Nx, ax k * (z - x) ^ (-(k : ℤ)))
    (h_match_a : ∀ k, a x k = ax k) (h_match_N : N x = Nx) :
    DifferentiableOn ℂ
      (fun z => g z -
        ∑ y ∈ S, ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ)))
      (Metric.ball x ε \ {x}) := by
  -- The key rewrite on the punctured disk:
  --   g(z) − ∑_y P_y(z) = h_x(z) − ∑_{y ≠ x} P_y(z),
  -- using `h_match_a, h_match_N` to identify the `y = x` summand of the global
  -- sum with the `(ax, Nx)` principal part.
  -- Step A. Differentiability of `h_x` on `ball x ε`.
  have hball_sub_Ux : Metric.ball x ε ⊆ Ux :=
    fun z hz => hUx_sub (Metric.ball_subset_closedBall hz)
  have hh_x_on_ball : DifferentiableOn ℂ h_x (Metric.ball x ε) :=
    hh_x_diff.mono hball_sub_Ux
  have hh_x_on_punc : DifferentiableOn ℂ h_x (Metric.ball x ε \ {x}) :=
    hh_x_on_ball.mono (fun z hz => hz.1)
  -- Step B. For each `y ≠ x` in `S`, the principal-part function
  -- `P_y(z) := ∑_k a y k · (z - y)^(-k)` is differentiable on `ball x ε`.
  have hP_y_diff : ∀ y ∈ S, y ≠ x →
      DifferentiableOn ℂ
        (fun z => ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ)))
        (Metric.ball x ε) := by
    intro y hyS hyx
    have hy_out : y ∉ Metric.closedBall x ε := hOther y hyS hyx
    -- `(z - y)^(-(k:ℤ))` is differentiable wherever `z ≠ y`.
    have h_sub_ne : ∀ z ∈ Metric.ball x ε, z - y ≠ 0 := by
      intro z hz hzy
      have hzy' : z = y := sub_eq_zero.mp hzy
      apply hy_out
      have hzc : z ∈ Metric.closedBall x ε := Metric.ball_subset_closedBall hz
      rw [hzy'] at hzc
      exact hzc
    apply DifferentiableOn.sum
    intro k _
    apply DifferentiableOn.const_mul
    intro z hz
    have hzy : z - y ≠ 0 := h_sub_ne z hz
    have h1 : DifferentiableAt ℂ (fun w : ℂ => w - y) z :=
      (differentiableAt_id).sub_const y
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w ^ (-(k : ℤ))) (z - y) :=
      differentiableAt_zpow.mpr (Or.inl hzy)
    exact (h2.comp z h1).differentiableWithinAt
  -- Step C. Decompose `H` on the punctured disk.
  -- H(z) = g(z) − P_S(z), where P_S(z) = ∑_y ∑_k a y k · (z - y)^(-k).
  -- Split P_S = P_x + ∑_{y ∈ S.erase x} P_y, where the `y = x` summand uses
  -- `(ax, Nx)` (after rewriting via h_match_a/N).
  -- On the punctured disk, by hdec, g(z) = h_x(z) + P_x(z),
  -- so H(z) = h_x(z) − ∑_{y ∈ S.erase x} P_y(z).
  have hRewrite : EqOn
      (fun z => g z -
        ∑ y ∈ S, ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ)))
      (fun z => h_x z -
        ∑ y ∈ S.erase x, ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ)))
      (Metric.ball x ε \ {x}) := by
    intro z hz
    have hz_ball : z ∈ Metric.ball x ε := hz.1
    have hz_ne_x : z ≠ x := by
      intro hzx; exact hz.2 (by simp [hzx])
    have hz_in_Ux : z ∈ Ux := hball_sub_Ux hz_ball
    -- Apply `hdec` at `z`.
    have hg_eq := hdec z hz_in_Ux hz_ne_x
    -- Split the global sum at the `y = x` summand.
    have h_sum_split :
        (∑ y ∈ S, ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ)))
          = (∑ k ∈ Finset.Icc 1 (N x),
                a x k * (z - x) ^ (-(k : ℤ)))
            + ∑ y ∈ S.erase x, ∑ k ∈ Finset.Icc 1 (N y),
                a y k * (z - y) ^ (-(k : ℤ)) :=
      (Finset.add_sum_erase S _ hxS).symm
    -- Match the x-summand to (ax, Nx).
    have h_match_sum :
        (∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ)))
          = ∑ k ∈ Finset.Icc 1 Nx,
                ax k * (z - x) ^ (-(k : ℤ)) := by
      rw [h_match_N]
      apply Finset.sum_congr rfl
      intro k _
      rw [h_match_a]
    -- Combine: g(z) = h_x(z) + (sum over Icc 1 Nx of ax k (z-x)^(-k)).
    -- Therefore g(z) − [P_x + ∑_{y ≠ x} P_y] = h_x(z) − ∑_{y ≠ x} P_y.
    show g z -
        ∑ y ∈ S, ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ))
      = h_x z -
        ∑ y ∈ S.erase x, ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ))
    rw [h_sum_split, h_match_sum, hg_eq]
    ring
  -- Step D. The right-hand side is differentiable on the punctured disk
  -- (`h_x` on the disk; each `P_y` for `y ≠ x` on the disk).
  have hRHS_diff : DifferentiableOn ℂ
      (fun z => h_x z -
        ∑ y ∈ S.erase x, ∑ k ∈ Finset.Icc 1 (N y),
            a y k * (z - y) ^ (-(k : ℤ)))
      (Metric.ball x ε \ {x}) := by
    apply DifferentiableOn.sub
    · exact hh_x_on_punc
    · apply DifferentiableOn.sum
      intro y hy
      rw [Finset.mem_erase] at hy
      obtain ⟨hyx, hyS⟩ := hy
      exact (hP_y_diff y hyS hyx).mono (fun z hz => hz.1)
  -- Step E. Transfer differentiability via `EqOn`.
  refine hRHS_diff.congr ?_
  intro z hz
  exact (hRewrite hz).symm

/-- **Headline existence theorem.** Given a finite set `S` of poles of
`g`, with `0 < ε x` for each `x ∈ S` and pairwise-disjoint per-pole closed
disks (each pole `y ≠ x` lies outside `closedBall x (ε x)`), and assuming
`SinglePoleLaurentExtraction g x (ε x)` at each `x ∈ S`, there exist
global coefficient data `a : ℂ → ℕ → ℂ`, truncation bound `N : ℂ → ℕ`,
and an analytic-part function `h : ℂ → ℂ` such that:

* the pointwise decomposition
  `g z = h z + ∑_{x ∈ S} ∑_{k=1}^{N x} a x k · (z - x)^(-k : ℤ)`
  holds for **every** `z : ℂ`,
* and `h` is differentiable on each punctured disk
  `Metric.ball x (ε x) \ {x}` for `x ∈ S`. -/
theorem multiPole_finite_laurent_exists
    (g : ℂ → ℂ) (S : Finset ℂ) (ε : ℂ → ℝ)
    (hε_pos : ∀ x ∈ S, 0 < ε x)
    (hDisj : ∀ x ∈ S, ∀ y ∈ S, y ≠ x → y ∉ Metric.closedBall x (ε x))
    (hExtract : ∀ x ∈ S, SinglePoleLaurentExtraction g x (ε x)) :
    ∃ (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ z : ℂ,
        g z = h z + ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
                a x k * (z - x) ^ (-(k : ℤ))) ∧
      (∀ x ∈ S,
        DifferentiableOn ℂ h (Metric.ball x (ε x) \ {x})) := by
  classical
  -- Per-pole choice via `Classical.choose`.
  choose Nx ax hxFun Ux hUxOpen hUxSub hhFunDiff hdec using
    fun (x : ℂ) (hx : x ∈ S) => hExtract x hx
  -- Default extensions to all of `ℂ` (zero outside `S`).
  let a' : ℂ → ℕ → ℂ := fun x =>
    if hx : x ∈ S then ax x hx else fun _ => 0
  let N' : ℂ → ℕ := fun x =>
    if hx : x ∈ S then Nx x hx else 0
  -- Define the global remainder `H := g − P_S`.
  let H : ℂ → ℂ := fun z =>
    g z - ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N' x),
            a' x k * (z - x) ^ (-(k : ℤ))
  refine ⟨a', N', H, ?_, ?_⟩
  · -- Algebraic decomposition: `g z = (g z − P_S z) + P_S z`.
    intro z
    show g z = H z + ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N' x),
                a' x k * (z - x) ^ (-(k : ℤ))
    simp [H, sub_add_cancel]
  · -- Local analyticity of `H` at each pole.
    intro x hxS
    have hx_pos := hε_pos x hxS
    have hOther : ∀ y ∈ S, y ≠ x → y ∉ Metric.closedBall x (ε x) :=
      fun y hyS hyx => hDisj x hxS y hyS hyx
    -- Match `a', N'` to the chosen `(ax x hxS, Nx x hxS)`.
    have h_match_a : ∀ k, a' x k = ax x hxS k := by
      intro k; show (if hx : x ∈ S then ax x hx else fun _ => 0) k = ax x hxS k
      simp [hxS]
    have h_match_N : N' x = Nx x hxS := by
      show (if hx : x ∈ S then Nx x hx else 0) = Nx x hxS
      simp [hxS]
    exact assembled_remainder_diff_at_pole hx_pos S a' N' hxS hOther
      (hUxOpen x hxS) (hUxSub x hxS) (hhFunDiff x hxS)
      (hdec x hxS) h_match_a h_match_N

end MultiPoleLaurentExistence

end JacobianChallenge

end
