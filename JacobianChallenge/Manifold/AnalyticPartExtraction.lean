/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import JacobianChallenge.Manifold.MultiHoleCauchyMeromorphic

/-! # Analytic-part extraction for finite-pole meromorphic functions (ZZ65)

This file discharges the **analytic-part-extraction** residual of ZZ64
(`MultiHoleCauchyMeromorphic.circleIntegral_finite_principal_part_eq`).

That theorem requires the caller to supply an open `U ⊇ closedBall c R`
together with a differentiable `h : ℂ → ℂ` on `U` such that
`g = h + (principal sum)` pointwise on the relevant circles. ZZ65 proves
that **such an `h` exists** for any `g : ℂ → ℂ` that is differentiable
off a finite pole set `S ⊆ ball c R` on a slightly larger open set, and
whose deviation from each prescribed principal part is **bounded near
each pole**.

## Headline statement

`exists_analytic_part_of_finite_pole_meromorphic`:

> Let `c : ℂ`, `R > 0`, `S : Finset ℂ` with `S ⊆ ball c R`. Let
> `a : ℂ → ℕ → ℂ`, `N : ℂ → ℕ` be principal-coefficient data. Suppose:
>
>  * (geometric) An open `U₀ ⊇ closedBall c R` exists with `g`
>    differentiable on `U₀ \ S`;
>
>  * (boundedness) For each `x ∈ S`, the function
>    `z ↦ g z - ∑_{k=1}^{N x} a x k · (z - x)^(-k:ℤ)` is bounded on
>    some punctured neighbourhood of `x` (this is the *defining*
>    condition that the prescribed principal part actually matches the
>    singular behaviour of `g` at `x`).
>
> Then there exists an open `U ⊇ closedBall c R` and `h : ℂ → ℂ` with
> `DifferentiableOn ℂ h U` and, on every `z ∈ U \ S`,
>     `g z = h z + ∑_{x ∈ S} ∑_{k=1}^{N x} a x k · (z - x)^(-k:ℤ)`.

In particular, restricting the pointwise identity to the outer sphere
`sphere c R` and to each inner sphere `sphere y (ε y)` (which all sit
inside `closedBall c R \ S` whenever the disjoint-ball geometry of ZZ64
holds) discharges the bundled analytic-part hypothesis of ZZ64.

## Strategy

* Take `U := U₀` (the same open set on which `g` is differentiable off
  `S`).
* Define `P : ℂ → ℂ` by
    `P z = ∑_{x ∈ S} ∑_{k=1}^{N x} a x k · (z - x)^(-k:ℤ)`.
* Note `P` is differentiable on `ℂ \ S` (each summand is differentiable
  off its own pole). Therefore `g - P` is differentiable on `U₀ \ S`.
* The boundedness hypothesis at each `x ∈ S` transfers from
  `g - principal_part_at_x` to `g - P` because the *other* summands
  `P_y` for `y ≠ x` are continuous (hence bounded) near `x`.
* Iterate `Complex.differentiableOn_update_limUnder_of_bddAbove` over
  the finite set `S` via `Finset.induction_on`. Each step removes one
  pole by `update`-ing with the limit, preserving boundedness at the
  remaining poles (the `update` only changes one point).
* The final iterated function is differentiable on all of `U₀` and
  agrees with `g - P` off `S`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed.
* Sole external mathlib hooks:
  `Complex.differentiableOn_update_limUnder_of_bddAbove`,
  `differentiableAt_zpow`, `Function.update_of_ne`, finite-set induction.
-/

noncomputable section

open Complex Set Metric Function Filter
open scoped Topology

namespace JacobianChallenge

namespace AnalyticPartExtraction

/-- The full principal-part sum across all poles. -/
def fullPrincipalPart (S : Finset ℂ) (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ))

/-- The principal-part sum at a single pole. -/
def principalPartAt (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) (x z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ))

/-- Single-pole principal part is differentiable away from its pole. -/
lemma principalPartAt_differentiableOn_compl_singleton
    (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) (x : ℂ) :
    DifferentiableOn ℂ (principalPartAt a N x) {z : ℂ | z ≠ x} := by
  unfold principalPartAt
  apply DifferentiableOn.fun_sum
  intro k _
  intro z hz
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z - x) z :=
    (differentiableAt_id).sub_const x
  have h3 : DifferentiableAt ℂ (fun z : ℂ => (z - x) ^ (-(k : ℤ))) z :=
    h1.zpow (Or.inl hzx)
  exact ((differentiableAt_const (a x k)).mul h3).differentiableWithinAt

/-- Single-pole principal part is continuous at any point off its pole. -/
lemma principalPartAt_continuousAt_of_ne
    (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) {x y : ℂ} (hxy : y ≠ x) :
    ContinuousAt (principalPartAt a N x) y := by
  have hd : DifferentiableAt ℂ (principalPartAt a N x) y :=
    ((principalPartAt_differentiableOn_compl_singleton a N x).differentiableAt
      (IsOpen.mem_nhds isOpen_ne hxy))
  exact hd.continuousAt

/-- Full principal part is differentiable on the complement of the pole set. -/
lemma fullPrincipalPart_differentiableOn_compl
    (S : Finset ℂ) (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) :
    DifferentiableOn ℂ (fullPrincipalPart S a N) ((S : Set ℂ)ᶜ) := by
  unfold fullPrincipalPart
  apply DifferentiableOn.fun_sum
  intro x hxS
  have hsub : ((S : Set ℂ)ᶜ) ⊆ {z : ℂ | z ≠ x} := by
    intro z hz hzx; apply hz; rw [hzx]; exact_mod_cast hxS
  exact (principalPartAt_differentiableOn_compl_singleton a N x).mono hsub

/-- Off the pole `x`, the difference between `g` and the *full* principal part
agrees up to a continuous (locally bounded) shift with the difference between
`g` and the *single* principal part at `x`. We only need a `BddAbove` corollary. -/
lemma bddAbove_full_diff_of_bddAbove_single_diff
    {g : ℂ → ℂ} (S : Finset ℂ) (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) {x : ℂ} (hxS : x ∈ S)
    {V : Set ℂ} (hV : V ∈ 𝓝 x)
    (hbdd : BddAbove (norm ∘ (fun z => g z - principalPartAt a N x z) '' (V \ {x}))) :
    ∃ W ∈ 𝓝 x,
      BddAbove (norm ∘ (fun z => g z - fullPrincipalPart S a N z) '' (W \ {x})) := by
  classical
  -- Let T = S \ {x}. Each principalPartAt a N y for y ∈ T is differentiable at x.
  -- So `∑_{y ∈ T} principalPartAt a N y` is differentiable, hence continuous, hence
  -- bounded on a neighbourhood of `x`.
  set T : Finset ℂ := S.erase x with hTdef
  have hT_diff : DifferentiableAt ℂ (fun z => ∑ y ∈ T, principalPartAt a N y z) x := by
    apply DifferentiableAt.fun_sum
    intro y hyT
    have hyx : y ≠ x := (Finset.mem_erase.mp hyT).1
    have hxy : x ≠ y := fun h => hyx h.symm
    exact ((principalPartAt_differentiableOn_compl_singleton a N y).differentiableAt
      (IsOpen.mem_nhds isOpen_ne hxy))
  have hT_cont : ContinuousAt (fun z => ∑ y ∈ T, principalPartAt a N y z) x :=
    hT_diff.continuousAt
  -- bounded on a neighbourhood
  set Mref : ℝ := ‖∑ y ∈ T, principalPartAt a N y x‖ + 1 with hMref
  have hev : ∀ᶠ z in 𝓝 x, ‖∑ y ∈ T, principalPartAt a N y z‖ ≤ Mref := by
    have htend : Filter.Tendsto
        (fun z => ‖∑ y ∈ T, principalPartAt a N y z‖) (𝓝 x)
        (𝓝 ‖∑ y ∈ T, principalPartAt a N y x‖) := hT_cont.norm
    exact htend.eventually_le_const (by exact lt_add_one _)
  rw [Filter.eventually_iff_exists_mem] at hev
  obtain ⟨W₁, hW₁, hbnd₁⟩ := hev
  refine ⟨V ∩ W₁, Filter.inter_mem hV hW₁, ?_⟩
  -- Now bound g - fullPrincipalPart on (V ∩ W₁) \ {x}
  obtain ⟨M₀, hM₀⟩ := hbdd
  refine ⟨M₀ + Mref, ?_⟩
  rintro v ⟨z, ⟨hzVW, hzx⟩, rfl⟩
  -- Decompose: full = principalPartAt x + ∑_{y∈T} principalPartAt y
  have hfull_eq : fullPrincipalPart S a N z =
      principalPartAt a N x z + ∑ y ∈ T, principalPartAt a N y z := by
    unfold fullPrincipalPart principalPartAt
    rw [show S = insert x T by
      simp [hTdef, Finset.insert_erase hxS]]
    rw [Finset.sum_insert (Finset.notMem_erase x S)]
  -- triangle inequality
  have h1 : ‖g z - principalPartAt a N x z‖ ≤ M₀ := by
    apply hM₀; refine ⟨z, ⟨hzVW.1, hzx⟩, rfl⟩
  have h2 : ‖∑ y ∈ T, principalPartAt a N y z‖ ≤ Mref := hbnd₁ z hzVW.2
  have hrearr : g z - fullPrincipalPart S a N z =
      (g z - principalPartAt a N x z) - (∑ y ∈ T, principalPartAt a N y z) := by
    rw [hfull_eq]; ring
  show ‖g z - fullPrincipalPart S a N z‖ ≤ M₀ + Mref
  rw [hrearr]
  calc ‖(g z - principalPartAt a N x z) - (∑ y ∈ T, principalPartAt a N y z)‖
      ≤ ‖g z - principalPartAt a N x z‖ + ‖∑ y ∈ T, principalPartAt a N y z‖ :=
        norm_sub_le _ _
    _ ≤ M₀ + Mref := add_le_add h1 h2

/-- **Iterated removable-singularity update over a `Finset`.**

If `f : ℂ → E` is differentiable on `U \ T` (open `U`, finite `T ⊆ U`) and is
*bounded near every point of `T`*, then there exists `h : ℂ → ℂ` differentiable
on `U` and equal to `f` off `T`.

Proved by induction on `T`. -/
lemma exists_differentiable_extension_of_finite_pole_set
    (T : Finset ℂ) {f : ℂ → ℂ} {U : Set ℂ} (hUopen : IsOpen U)
    (hTsub : (T : Set ℂ) ⊆ U)
    (hf_diff : DifferentiableOn ℂ f (U \ T))
    (hf_bdd : ∀ x ∈ T, ∃ V ∈ 𝓝 x,
        BddAbove (norm ∘ f '' (V \ {x}))) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ ∀ z ∈ U \ T, h z = f z := by
  classical
  revert f U hUopen hTsub hf_diff hf_bdd
  induction T using Finset.induction_on with
  | empty =>
      intro f U _ _ hf_diff _
      refine ⟨f, ?_, fun _ _ => rfl⟩
      simpa using hf_diff
  | @insert x T hxT ih =>
      intro f U hUopen hTsub hf_diff hf_bdd
      -- x ∉ T, x ∈ insert x T ⊆ U.
      have hxU : x ∈ U := hTsub (by exact Finset.mem_insert_self x T)
      have hTsub' : (T : Set ℂ) ⊆ U := by
        intro z hz; exact hTsub (Finset.mem_insert_of_mem hz)
      -- Differentiability on U \ insert x T = (U \ {x}) \ T  (modulo set algebra)
      have hcoe : ((insert x T : Finset ℂ) : Set ℂ) = insert x (T : Set ℂ) := by
        simp
      have hf_diff' : DifferentiableOn ℂ f (U \ insert x (T : Set ℂ)) := by
        rw [hcoe] at hf_diff; exact hf_diff
      -- Get inductive extension across T on the open set U \ {x}.
      have hUopen_x : IsOpen (U \ ({x} : Set ℂ)) :=
        hUopen.sdiff isClosed_singleton
      have hTsub_x : (T : Set ℂ) ⊆ U \ ({x} : Set ℂ) := by
        intro z hz
        refine ⟨hTsub' hz, ?_⟩
        intro hzx; rw [Set.mem_singleton_iff] at hzx
        apply hxT; rw [← hzx]; exact_mod_cast hz
      -- f is differentiable on (U \ {x}) \ T (= U \ insert x T)
      have hf_diff_restr : DifferentiableOn ℂ f ((U \ ({x} : Set ℂ)) \ T) := by
        have hset : (U \ ({x} : Set ℂ)) \ (T : Set ℂ) = U \ insert x (T : Set ℂ) := by
          ext z; simp [Set.mem_diff, Set.mem_insert_iff]; tauto
        rw [hset]; exact hf_diff'
      have hf_bdd_T : ∀ y ∈ T, ∃ V ∈ 𝓝 y, BddAbove (norm ∘ f '' (V \ {y})) := by
        intro y hy; exact hf_bdd y (Finset.mem_insert_of_mem hy)
      obtain ⟨h₁, hh₁_diff, hh₁_eq⟩ :=
        ih hUopen_x hTsub_x hf_diff_restr hf_bdd_T
      -- Now remove the singularity at x via update with limit.
      obtain ⟨V, hVnhd, hVbdd⟩ := hf_bdd x (Finset.mem_insert_self x T)
      -- We need bound on h₁ near x. Since h₁ = f on (U \ {x}) \ T and {x} ∪ T is finite,
      -- and on a small enough nbhd of x, points are in U \ T (T finite, x ∉ T), we can
      -- transfer the bound from f to h₁.
      have hopen_minusT : IsOpen (U \ (T : Set ℂ)) :=
        hUopen.sdiff T.finite_toSet.isClosed
      have hx_in : x ∈ U \ (T : Set ℂ) := ⟨hxU, fun hxT' => hxT (by exact_mod_cast hxT')⟩
      have hnhdT : U \ (T : Set ℂ) ∈ 𝓝 x := hopen_minusT.mem_nhds hx_in
      -- For points z in (U \ T) ∩ V \ {x}: z ∈ (U \ {x}) \ T, so h₁ z = f z.
      have hh₁_bdd : BddAbove (norm ∘ h₁ '' ((V ∩ (U \ (T : Set ℂ))) \ {x})) := by
        obtain ⟨M, hM⟩ := hVbdd
        refine ⟨M, ?_⟩
        rintro v ⟨z, ⟨⟨hzV, hzUT⟩, hzx⟩, rfl⟩
        have hz_in : z ∈ (U \ ({x} : Set ℂ)) \ (T : Set ℂ) := by
          refine ⟨⟨hzUT.1, ?_⟩, hzUT.2⟩
          intro hzx'; exact hzx hzx'
        have heq : h₁ z = f z := hh₁_eq z hz_in
        show ‖h₁ z‖ ≤ M
        rw [heq]; exact hM ⟨z, ⟨hzV, hzx⟩, rfl⟩
      -- We need DifferentiableOn h₁ (W \ {x}) for some W ∈ 𝓝 x. Take W = U \ T.
      have hh₁_diff_punct : DifferentiableOn ℂ h₁ ((U \ (T : Set ℂ)) \ {x}) := by
        have hsub : (U \ (T : Set ℂ)) \ ({x} : Set ℂ) ⊆ U \ ({x} : Set ℂ) := by
          intro z hz; exact ⟨hz.1.1, hz.2⟩
        exact hh₁_diff.mono hsub
      -- Now use removable-singularity. We need W ∈ 𝓝 x with h₁ diff on W \ {x} and bounded.
      -- Take W := V ∩ (U \ T), open neighbourhood of x.
      have hW_mem : V ∩ (U \ (T : Set ℂ)) ∈ 𝓝 x := Filter.inter_mem hVnhd hnhdT
      have hh₁_diff_W : DifferentiableOn ℂ h₁ ((V ∩ (U \ (T : Set ℂ))) \ {x}) :=
        hh₁_diff_punct.mono (fun z hz => ⟨hz.1.2, hz.2⟩)
      have hh₁_extend := Complex.differentiableOn_update_limUnder_of_bddAbove
        (E := ℂ) (f := h₁) (s := V ∩ (U \ (T : Set ℂ))) (c := x)
        hW_mem hh₁_diff_W hh₁_bdd
      -- Patch: outside W, use h₁ itself; inside W, use the update.
      -- The update h₂ := update h₁ x (limUnder ...) is differentiable on W and equal
      -- to h₁ off {x}. We need it differentiable on all of U.
      set h₂ : ℂ → ℂ := update h₁ x (limUnder (𝓝[≠] x) h₁)
      have hh₂_eq_h₁ : ∀ z, z ≠ x → h₂ z = h₁ z := by
        intro z hzx; simp [h₂, Function.update_of_ne hzx]
      refine ⟨h₂, ?_, ?_⟩
      · -- DifferentiableOn h₂ U
        intro z hzU
        by_cases hzx : z = x
        · subst hzx
          exact (hh₁_extend.differentiableAt hW_mem).differentiableWithinAt
        · -- away from x, h₂ = h₁, h₁ diff on U \ {x}
          have : DifferentiableAt ℂ h₂ z := by
            have h₁_diff_at : DifferentiableAt ℂ h₁ z :=
              hh₁_diff.differentiableAt
                (hUopen_x.mem_nhds ⟨hzU, fun hh => hzx (by simpa using hh)⟩)
            -- h₂ = h₁ on a nbhd of z (since z ≠ x).
            have heq : h₂ =ᶠ[𝓝 z] h₁ := by
              have hopen_ne : IsOpen ({y : ℂ | y ≠ x}) := isOpen_ne
              filter_upwards [hopen_ne.mem_nhds hzx] with w hw
              exact hh₂_eq_h₁ w hw
            exact h₁_diff_at.congr_of_eventuallyEq heq
          exact this.differentiableWithinAt
      · -- agreement off insert x T
        intro z hzU
        have hzx : z ≠ x := by
          intro h; apply hzU.2; rw [h]
          rw [hcoe]; exact Set.mem_insert _ _
        have hzT : z ∉ (T : Set ℂ) := by
          intro hzT'; apply hzU.2
          rw [hcoe]; exact Set.mem_insert_of_mem _ hzT'
        rw [hh₂_eq_h₁ z hzx]
        exact hh₁_eq z ⟨⟨hzU.1, hzx⟩, hzT⟩

/-- **Headline (existence of analytic part).**

Given a finite-pole meromorphic-like function `g`, with prescribed principal
parts at each pole and the natural boundedness condition that the prescribed
principal part actually matches the singular behaviour, there exists an
analytic-part function `h : ℂ → ℂ` defined on an open neighbourhood of
`closedBall c R` such that `g = h + (principal sum)` off the pole set. -/
theorem exists_analytic_part_of_finite_pole_meromorphic
    {c : ℂ} {R : ℝ} (_hR : 0 < R)
    (S : Finset ℂ) (_hSsub : (S : Set ℂ) ⊆ ball c R)
    (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ)
    {g : ℂ → ℂ}
    {U₀ : Set ℂ} (hU₀_open : IsOpen U₀) (hU₀_sub : closedBall c R ⊆ U₀)
    (hg_diff : DifferentiableOn ℂ g (U₀ \ S))
    (hg_bdd : ∀ x ∈ S, ∃ V ∈ 𝓝 x,
        BddAbove (norm ∘ (fun z => g z - principalPartAt a N x z) '' (V \ {x}))) :
    ∃ U : Set ℂ, IsOpen U ∧ closedBall c R ⊆ U ∧
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧
        ∀ z ∈ U \ S, g z = h z + fullPrincipalPart S a N z := by
  classical
  -- Choose U := U₀.
  refine ⟨U₀, hU₀_open, hU₀_sub, ?_⟩
  -- Define f := g - fullPrincipalPart on U₀ \ S.
  -- f is differentiable on U₀ \ S (both g and fullPrincipalPart are).
  set P : ℂ → ℂ := fullPrincipalPart S a N with hPdef
  set f : ℂ → ℂ := fun z => g z - P z with hfdef
  -- Differentiability of f on U₀ \ S:
  have hP_diff : DifferentiableOn ℂ P (U₀ \ S) := by
    have hsub : U₀ \ (S : Set ℂ) ⊆ ((S : Set ℂ)ᶜ) := fun z hz => hz.2
    exact (fullPrincipalPart_differentiableOn_compl S a N).mono hsub
  have hf_diff : DifferentiableOn ℂ f (U₀ \ S) := hg_diff.sub hP_diff
  -- Boundedness of f near each pole.
  have hf_bdd : ∀ x ∈ S, ∃ V ∈ 𝓝 x, BddAbove (norm ∘ f '' (V \ {x})) := by
    intro x hxS
    obtain ⟨V, hV, hVbdd⟩ := hg_bdd x hxS
    obtain ⟨W, hW, hWbdd⟩ :=
      bddAbove_full_diff_of_bddAbove_single_diff S a N hxS hV hVbdd
    exact ⟨W, hW, hWbdd⟩
  -- Iterate removable-singularity over S.
  have hSsubU₀ : (S : Set ℂ) ⊆ U₀ := fun z hz => hU₀_sub
    (Metric.ball_subset_closedBall (_hSsub hz))
  obtain ⟨h, hh_diff, hh_eq⟩ :=
    exists_differentiable_extension_of_finite_pole_set
      S hU₀_open hSsubU₀ hf_diff hf_bdd
  refine ⟨h, hh_diff, ?_⟩
  intro z hzU
  have hh_eq_z := hh_eq z hzU
  -- hh_eq_z : h z = g z - P z, so g z = h z + P z.
  show g z = h z + fullPrincipalPart S a N z
  have hzz : h z = g z - fullPrincipalPart S a N z := hh_eq_z
  rw [hzz]; ring

end AnalyticPartExtraction

end JacobianChallenge
