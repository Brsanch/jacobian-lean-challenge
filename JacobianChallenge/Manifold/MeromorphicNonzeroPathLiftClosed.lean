/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftGlobalOpen
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftGlobalClosed
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOn
import Mathlib.Topology.Sequences

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Closedness of `liftReachable`: `sSup ∈ liftReachable`

For non-constant `f.toRiemannSphere`, a continuous `β` taking regular
values on `Icc 0 T`, and a base preimage `x₀` over `β 0`, the
supremum of `liftReachable f β x₀ T` is itself in `liftReachable`.

This is the substantive half of the clopen argument: combined with
`liftReachable_extends_right` (openness) on `[0, T]` connected, it
forces `sSup = T`, hence `T ∈ liftReachable`, hence a global
continuous lift exists on `Icc 0 T`.

## Argument

Set `s := sSup (liftReachable f β x₀ T)`.

* Edge case: `s = 0` ⇒ `s ∈ liftReachable` by `zero_mem_liftReachable`.
* Otherwise `0 < s`. Pick `(b n)_n` in `liftReachable` with
  `b n → s` (any approximating sequence; existence from `IsLUB`).
* For each `n`, extract via `Classical.choose` a continuous lift
  `γ n : ℝ → X` of `β` on `Icc 0 (b n)` starting at `x₀`.
* `X` is compact and (via `ChartedSpace ℂ X + CompactSpace`)
  second-countable, hence first-countable, hence sequentially
  compact. Extract a convergent subsequence
  `γ (φ n) (b (φ n)) → x_s`.
* `f.toRiemannSphere x_s = β s` by continuity of `f.toRiemannSphere`,
  continuity of `β`, and the lift identity at `b (φ n)`.
* `x_s ∈ f.regularSet` since `β s ∈ f.regularValueSet`.
* Pick the `LocalSheetData` at `x_s`. By continuity of `β`,
  `β` maps an interval `Icc (s - δ) (s + δ) ∩ [0, T]` into
  `sheet.V` for some `δ > 0`. By the convergence of the
  subsequence, there is `N` with `γ (φ N) (b (φ N)) ∈ sheet.U`
  and `b (φ N) > s - δ`.
* Build the global lift via the clip-and-`if_le` trick
  (cf. `liftReachable_extends_right`): on `t ≤ b (φ N)` use
  `γ (φ N) t`; on `t ≥ b (φ N)` use `sheet.g (β (clip t))` where
  `clip t = max (b (φ N)) (min s t)`. Agreement at `b (φ N)`
  holds via `sheet.leftInvOn` applied to `γ (φ N) (b (φ N)) ∈ U`.

## What ships

* `MeromorphicNonzero.exists_seq_in_liftReachable_tendsto_sSup` — the
  approximating-sequence helper.
* `MeromorphicNonzero.sSup_mem_liftReachable` — the closedness
  headline.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Approximating sequence from below for `sSup (liftReachable)`.**

The set `f.liftReachable β x₀ T` is non-empty (contains `0`) and
bounded above by `T`. There is therefore a sequence `b : ℕ → ℝ`
in `liftReachable` converging to the supremum. -/
lemma exists_seq_in_liftReachable_tendsto_sSup
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    {x₀ : X} (hx₀ : f.toRiemannSphere x₀ = β 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ b : ℕ → ℝ, (∀ n, b n ∈ f.liftReachable β x₀ T) ∧
      Tendsto b atTop (𝓝 (sSup (f.liftReachable β x₀ T))) := by
  classical
  have h_nonempty : (f.liftReachable β x₀ T).Nonempty :=
    ⟨0, f.zero_mem_liftReachable hx₀ hT⟩
  have h_bdd : BddAbove (f.liftReachable β x₀ T) :=
    f.liftReachable_bddAbove β x₀ T
  -- For every `n`, find `b ∈ liftReachable` with `sSup - 1/(n+1) < b`.
  have h_approx : ∀ n : ℕ, ∃ b ∈ f.liftReachable β x₀ T,
      sSup (f.liftReachable β x₀ T) - 1 / (n + 1 : ℝ) < b := by
    intro n
    have h_eps_pos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      apply one_div_pos.mpr; exact_mod_cast Nat.succ_pos n
    by_contra h
    push Not at h
    have h_le : sSup (f.liftReachable β x₀ T) ≤
        sSup (f.liftReachable β x₀ T) - 1 / (n + 1 : ℝ) :=
      csSup_le h_nonempty h
    linarith
  -- Skolem out the sequence.
  let b : ℕ → ℝ := fun n => (h_approx n).choose
  have hb_mem : ∀ (n : ℕ), b n ∈ f.liftReachable β x₀ T :=
    fun n => (h_approx n).choose_spec.1
  have hb_gt : ∀ (n : ℕ),
      sSup (f.liftReachable β x₀ T) - 1 / ((n : ℝ) + 1) < b n :=
    fun n => (h_approx n).choose_spec.2
  refine ⟨b, hb_mem, ?_⟩
  -- Bound the distance and conclude.
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε_pos
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε_pos
  refine ⟨N, fun n hn => ?_⟩
  have hb_le_s : b n ≤ sSup (f.liftReachable β x₀ T) :=
    le_csSup h_bdd (hb_mem n)
  have hb_close_below :
      sSup (f.liftReachable β x₀ T) - b n < 1 / (n + 1 : ℝ) := by
    have := hb_gt n; linarith
  have h_diff_nonpos :
      b n - sSup (f.liftReachable β x₀ T) ≤ 0 := by linarith
  rw [Real.dist_eq, abs_of_nonpos h_diff_nonpos]
  have h_one_div_mono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast Nat.succ_pos N
    · exact_mod_cast Nat.succ_le_succ hn
  linarith

/-- **Closedness of `liftReachable`.**

The supremum `s := sSup (liftReachable f β x₀ T)` is itself in
`liftReachable`. Combined with `liftReachable_extends_right`
(openness on `Icc 0 T`), this forces `s = T`, hence the global
continuous lift on `Icc 0 T` exists. -/
theorem sSup_mem_liftReachable
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β) (x₀ : X)
    {T : ℝ}
    (hβ_reg : ∀ t ∈ Icc 0 T, β t ∈ f.regularValueSet)
    (hx₀ : f.toRiemannSphere x₀ = β 0) (hT : 0 ≤ T) :
    sSup (f.liftReachable β x₀ T) ∈ f.liftReachable β x₀ T := by
  classical
  set s := sSup (f.liftReachable β x₀ T) with hs_def
  have h_s_le : s ≤ T := f.sSup_liftReachable_le hx₀ hT
  have h_s_nonneg : 0 ≤ s := f.sSup_liftReachable_nonneg hx₀ hT
  -- Edge case: s = 0.
  by_cases h_s_zero : s = 0
  · rw [show s = 0 from h_s_zero] at *
    exact f.zero_mem_liftReachable hx₀ hT
  -- Generic case: 0 < s.
  have h_s_pos : 0 < s := lt_of_le_of_ne h_s_nonneg (Ne.symm h_s_zero)
  -- s ∈ Icc 0 T and β s is regular.
  have h_s_mem_Icc : s ∈ Icc (0 : ℝ) T := ⟨h_s_nonneg, h_s_le⟩
  have hβs_reg : β s ∈ f.regularValueSet := hβ_reg s h_s_mem_Icc
  -- Approximating sequence b : ℕ → ℝ with b n ∈ liftReachable, b n → s.
  obtain ⟨b, hb_mem, hb_tendsto⟩ :=
    f.exists_seq_in_liftReachable_tendsto_sSup hx₀ hT
  -- Extract γ n : ℝ → X continuous with γ n 0 = x₀ lifting β on Icc 0 (b n).
  -- Use Classical.choose on each `hb_mem n`'s existential.
  let γ : ℕ → ℝ → X := fun n => (hb_mem n).2.choose
  have hγ_cont : ∀ n, Continuous (γ n) :=
    fun n => (hb_mem n).2.choose_spec.1
  have hγ_zero : ∀ n, γ n 0 = x₀ :=
    fun n => (hb_mem n).2.choose_spec.2.1
  have hγ_lift : ∀ n, ∀ t ∈ Icc 0 (b n), f.toRiemannSphere (γ n t) = β t :=
    fun n => (hb_mem n).2.choose_spec.2.2
  -- Derive sequential compactness on X.
  haveI : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_sigmaCompact (H := ℂ) (M := X)
  haveI : FirstCountableTopology X := inferInstance
  -- Subsequence γ (φ n) (b (φ n)) → x_s in compact X.
  obtain ⟨x_s, φ, hφ_mono, h_conv⟩ :=
    CompactSpace.tendsto_subseq (fun n => γ n (b n))
  -- The lifted-value sequence f.toRS (γ n (b n)) = β (b n) → β s.
  have h_lift_at_bn : ∀ n, f.toRiemannSphere (γ n (b n)) = β (b n) := by
    intro n
    exact hγ_lift n (b n) ⟨(hb_mem n).1.1, le_refl _⟩
  -- Continuity of f.toRS + h_conv ⇒ f.toRS (γ (φ n) (b (φ n))) → f.toRS x_s.
  have h_f_cont : Continuous f.toRiemannSphere :=
    (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f).continuous
  have h_fγ_conv :
      Tendsto (fun n => f.toRiemannSphere (γ (φ n) (b (φ n))))
        atTop (𝓝 (f.toRiemannSphere x_s)) :=
    h_f_cont.tendsto x_s |>.comp h_conv
  -- f.toRS (γ (φ n) (b (φ n))) = β (b (φ n)).
  have h_fγ_eq_β : ∀ n, f.toRiemannSphere (γ (φ n) (b (φ n))) = β (b (φ n)) :=
    fun n => h_lift_at_bn (φ n)
  -- β (b (φ n)) → β s (continuity of β + b (φ ·) → s).
  have hb_φ_tendsto : Tendsto (fun n => b (φ n)) atTop (𝓝 s) :=
    hb_tendsto.comp hφ_mono.tendsto_atTop
  have hβ_b_conv : Tendsto (fun n => β (b (φ n))) atTop (𝓝 (β s)) :=
    hβ_cont.tendsto s |>.comp hb_φ_tendsto
  -- Hence f.toRS x_s = β s.
  have h_fxs : f.toRiemannSphere x_s = β s := by
    have h_eq : (fun n => f.toRiemannSphere (γ (φ n) (b (φ n))))
        = (fun n => β (b (φ n))) := funext h_fγ_eq_β
    rw [h_eq] at h_fγ_conv
    exact tendsto_nhds_unique h_fγ_conv hβ_b_conv
  -- x_s ∈ regularSet.
  have h_xs_reg : x_s ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hβs_reg h_fxs
  -- Local sheet data at x_s.
  set sheet := f.localSheetData_at_regular hnc h_xs_reg with hsheet_def
  -- x_s ∈ sheet.U.
  have h_xs_U : x_s ∈ sheet.U := sheet.mem_U
  -- β s ∈ sheet.V (via h_fxs and sheet.mem_V).
  have h_βs_V : β s ∈ sheet.V := by
    have h : f.toRiemannSphere x_s ∈ sheet.V := sheet.mem_V
    exact h_fxs ▸ h
  -- β ⁻¹' sheet.V is open in ℝ, contains s. Get δ > 0 with Icc (s - δ) (s + δ) ⊆ β⁻¹ sheet.V.
  have h_preV_open : IsOpen (β ⁻¹' sheet.V) := sheet.V_open.preimage hβ_cont
  have h_s_pre : s ∈ β ⁻¹' sheet.V := h_βs_V
  rw [Metric.isOpen_iff] at h_preV_open
  obtain ⟨δ₀, hδ₀_pos, hδ₀_ball⟩ := h_preV_open s h_s_pre
  -- Shrink to ensure b (φ N) - s ≥ -δ for the eventual choice.
  let δ : ℝ := δ₀ / 2
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < δ₀ := by simp [δ]; linarith
  -- The sequence γ (φ ·) (b (φ ·)) is eventually in sheet.U (which is open with x_s ∈ U).
  have h_eventual_in_U :
      ∀ᶠ n in atTop, γ (φ n) (b (φ n)) ∈ sheet.U :=
    h_conv (sheet.U_open.mem_nhds h_xs_U)
  -- b (φ ·) is eventually in Ioo (s - δ) (s + δ).
  have h_eventual_close :
      ∀ᶠ n in atTop, b (φ n) ∈ Ioo (s - δ) (s + δ) := by
    have h_ball_eq : Metric.ball s δ = Ioo (s - δ) (s + δ) :=
      Real.ball_eq_Ioo s δ
    have := hb_φ_tendsto (Metric.ball_mem_nhds s hδ_pos)
    rwa [h_ball_eq] at this
  -- Pick N satisfying both.
  obtain ⟨N, hN⟩ := (h_eventual_in_U.and h_eventual_close).exists
  obtain ⟨hN_in_U, hN_close⟩ := hN
  -- Notations for the chosen index.
  set m := φ N with hm_def
  set bm := b m with hbm_def
  -- Properties at index m.
  have hbm_mem : bm ∈ f.liftReachable β x₀ T := hb_mem m
  have hbm_in_Icc : bm ∈ Icc (0 : ℝ) T := hbm_mem.1
  have hγm_cont : Continuous (γ m) := hγ_cont m
  have hγm_zero : γ m 0 = x₀ := hγ_zero m
  have hγm_lift : ∀ t ∈ Icc 0 bm, f.toRiemannSphere (γ m t) = β t := hγ_lift m
  have hγm_at_bm_in_U : γ m bm ∈ sheet.U := hN_in_U
  have hbm_lt_s : bm < s + δ := hN_close.2
  have hbm_gt : s - δ < bm := hN_close.1
  -- bm ≤ s holds because s = sSup and bm ∈ liftReachable.
  have hbm_le_s : bm ≤ s := by
    have h_bdd : BddAbove (f.liftReachable β x₀ T) :=
      f.liftReachable_bddAbove β x₀ T
    have : bm ≤ sSup (f.liftReachable β x₀ T) := le_csSup h_bdd hbm_mem
    rwa [← hs_def] at this
  -- β maps Icc bm s into sheet.V.
  have hβ_in_V : ∀ t ∈ Icc bm s, β t ∈ sheet.V := by
    intro t ht
    -- t ∈ Icc bm s ⊆ Metric.ball s δ₀.
    have h_dist : dist t s < δ₀ := by
      rw [Real.dist_eq]
      have h_t_le_s : t ≤ s := ht.2
      have h_t_ge_bm : bm ≤ t := ht.1
      have h_diff_nonpos : t - s ≤ 0 := by linarith
      rw [abs_of_nonpos h_diff_nonpos]
      have : s - t ≤ s - bm := by linarith
      have : s - bm < δ := by linarith
      linarith
    exact hδ₀_ball h_dist
  -- Clipping function (clip t = max bm (min s t)) lives in [bm, s].
  let clip : ℝ → ℝ := fun t => max bm (min s t)
  have h_clip_cont : Continuous clip :=
    (continuous_const.max (continuous_const.min continuous_id))
  have h_clip_in : ∀ t : ℝ, clip t ∈ Icc bm s := by
    intro t
    refine ⟨le_max_left _ _, max_le hbm_le_s (min_le_left _ _)⟩
  have h_clip_id : ∀ t ∈ Icc bm s, clip t = t := by
    intro t ht
    show max bm (min s t) = t
    rw [min_eq_right ht.2, max_eq_right ht.1]
  -- h t = sheet.g (β (clip t)), globally continuous.
  let h_fn : ℝ → X := fun t => sheet.g (β (clip t))
  have h_fn_cont : Continuous h_fn := by
    have hβ_clip_cont : Continuous (fun t => β (clip t)) :=
      hβ_cont.comp h_clip_cont
    have h_g_cont_on : ContinuousOn sheet.g sheet.V := sheet.g_continuousOn
    have h_mapsTo : ∀ t : ℝ, β (clip t) ∈ sheet.V := fun t =>
      hβ_in_V (clip t) (h_clip_in t)
    have h_cont_on_univ : ContinuousOn h_fn Set.univ := by
      refine h_g_cont_on.comp hβ_clip_cont.continuousOn ?_
      intro t _
      exact h_mapsTo t
    rwa [continuousOn_univ] at h_cont_on_univ
  -- Agreement at bm: γ m bm = h_fn bm.
  have h_agree_at_bm : γ m bm = h_fn bm := by
    show γ m bm = sheet.g (β (clip bm))
    rw [h_clip_id bm ⟨le_refl _, hbm_le_s⟩]
    have hγm_lift_bm : f.toRiemannSphere (γ m bm) = β bm :=
      hγm_lift bm ⟨hbm_in_Icc.1, le_refl _⟩
    have h_inv : sheet.g (f.toRiemannSphere (γ m bm)) = γ m bm :=
      sheet.leftInvOn hγm_at_bm_in_U
    show γ m bm = sheet.g (β bm)
    rw [← hγm_lift_bm, h_inv]
  -- Global lift via clip+if_le.
  let γ_glob : ℝ → X := fun t => if t ≤ bm then γ m t else h_fn t
  have hγ_glob_cont : Continuous γ_glob := by
    refine Continuous.if_le hγm_cont h_fn_cont continuous_id continuous_const ?_
    intro t ht
    rw [ht]; exact h_agree_at_bm
  -- Conclude s ∈ liftReachable.
  refine ⟨⟨h_s_nonneg, h_s_le⟩, γ_glob, hγ_glob_cont, ?_, ?_⟩
  · -- γ_glob 0 = x₀.
    show (if (0 : ℝ) ≤ bm then γ m 0 else h_fn 0) = x₀
    rw [if_pos hbm_in_Icc.1, hγm_zero]
  · -- Lift on Icc 0 s.
    intro t ht
    show f.toRiemannSphere (if t ≤ bm then γ m t else h_fn t) = β t
    by_cases htb : t ≤ bm
    · rw [if_pos htb]
      exact hγm_lift t ⟨ht.1, htb⟩
    · push Not at htb
      rw [if_neg (not_le.mpr htb)]
      show f.toRiemannSphere (sheet.g (β (clip t))) = β t
      have ht_in : t ∈ Icc bm s := ⟨le_of_lt htb, ht.2⟩
      rw [h_clip_id t ht_in]
      exact sheet.rightInvOn (hβ_in_V t ht_in)

end MeromorphicNonzero

end JacobianChallenge

end
