/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDz
import JacobianChallenge.Manifold.ComplexTorusConnected
import JacobianChallenge.Manifold.ComplexTorusBasicInstances
import JacobianChallenge.Manifold.ComplexTorusGenusLowerBound
import JacobianChallenge.Topology.LiouvilleForContMDiffOmega

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-! # Genus upper bound on the complex torus: `genus (ℂ ⧸ L) ≤ 1`

End-to-end discharge of the **upper bound**

  `Module.finrank ℂ (HolomorphicOneForm (ℂ ⧸ L)) ≤ 1`

unconditionally on the complex torus `T_L = ℂ ⧸ L`. Combined with
`ComplexTorusGenusLowerBound.one_le_genus`, this closes the
`genus (ℂ ⧸ L) = 1` atom on `T_L` (i.e. the upper-bound half formerly
flagged "Liouville on universal cover" in OPEN.md).

## The strategy: Liouville via global cotangent triviality

The cotangent bundle of `T_L` is canonically trivial because the
chart transitions on `T_L` are translations, with identity Fréchet
derivative (proved in `ComplexTorusTangentCoordChangeId.lean`). This
means: for every holomorphic 1-form `α : HolomorphicOneForm T_L`, the
fiber-valued evaluation `α.eval : T_L → CotangentSpace 𝓘(ℂ,ℂ) _` is
globally `ContMDiff ω` as a map into the **same** fiber type
`ℂ →L[ℂ] ℂ` (no chart-coord plumbing is needed beyond the chart
neighborhood overlap).

Define the **coefficient function**

  `dzCoeff α : ℂ ⧸ L → ℂ`,  `dzCoeff α p := (α.eval p) 1`.

It is `ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω` (compose `α.eval` with
`ContinuousLinearMap.apply ℂ ℂ 1`). The complex torus is compact,
connected, T2, and an `IsManifold 𝓘(ℂ) ω` complex 1-manifold (basic
instances). The unconditional Liouville result
`Topology.LiouvilleForContMDiffOmega.contMDiff_omega_isConstant`
forces `dzCoeff α` to be constant. Let `c := dzCoeff α 0`.

Then for every `p : T_L`, `(α.eval p) 1 = c`. By ℂ-linearity of
`α.eval p : ℂ →L[ℂ] ℂ`, this forces
`α.eval p = c • (ContinuousLinearMap.id ℂ ℂ) = c • (dz L).eval p`.
Hence `α = c • (dz L)` in `HolomorphicOneForm T_L`. Therefore the
ℂ-span of `dz L` is all of `HolomorphicOneForm T_L`, and the
ℂ-dimension is at most `1`.

## What this file ships

* `ComplexTorus.dzCoeff` — the scalar coefficient function.
* `ComplexTorus.dzCoeff_contMDiff` — smoothness of `dzCoeff α` as a
  map `T_L → ℂ`.
* `ComplexTorus.dzCoeff_isConstant` — Liouville: `dzCoeff α` is a
  constant function.
* `ComplexTorus.exists_smul_dz` — for every `α`, `∃ c, α = c • dz L`.
* `ComplexTorus.holomorphicOneForm_eq_span_dz` — the ℂ-span of `dz L`
  is `⊤` in `HolomorphicOneForm (ℂ ⧸ L)`.
* `ComplexTorus.finrank_holomorphicOneForm_le_one` — the upper bound
  `finrank ≤ 1`.
* `ComplexTorus.genus_le_one` — the upper bound `genus T_L ≤ 1`.
* `ComplexTorus.genus_eq_one` — combining with the lower bound,
  `genus T_L = 1`.

No `sorry`, no `axiom`. -/

open Bundle Set Module
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The coefficient function -/

/-- **The `dz`-coefficient of a holomorphic 1-form on `T_L`.**
For `α : HolomorphicOneForm (ℂ ⧸ L)`, the function
`dzCoeff α p := (α.eval p) (1 : ℂ) : ℂ`. -/
def dzCoeff (α : HolomorphicOneForm (ℂ ⧸ L)) : (ℂ ⧸ L) → ℂ :=
  fun p => (α.eval p) (1 : ℂ)

/-! ## Smoothness of the coefficient function -/

/-- The chart-coord representative of `α.eval` at `x₀` agrees with
`α.eval` itself on a neighborhood of `x₀`, because cotangent
coord-changes on `T_L` are the identity. -/
private lemma chart_rep_eq_eval_eventually
    (α : HolomorphicOneForm (ℂ ⧸ L)) (x₀ : ℂ ⧸ L) :
    (fun x : ℂ ⧸ L =>
        (cotangentBundleCore 𝓘(ℂ, ℂ) (ℂ ⧸ L)).coordChange
          (achart ℂ x) (achart ℂ x₀) x (α.eval x))
      =ᶠ[nhds x₀] (fun x : ℂ ⧸ L => α.eval x) := by
  filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds
    (mem_chart_source ℂ x₀)] with x hx
  -- On the chart overlap, the coord change is identity.
  have h_xy : x ∈ (extChartAt 𝓘(ℂ, ℂ) x).source ∩
                (extChartAt 𝓘(ℂ, ℂ) x₀).source := by
    refine ⟨?_, ?_⟩
    · rw [extChartAt_source]; exact mem_chart_source ℂ x
    · rw [extChartAt_source]; exact hx
  exact cotangentBundleCore_coordChange_eq_id_on_overlap L x x₀ h_xy (α.eval x)

/-- `α.eval : T_L → (ℂ →L[ℂ] ℂ)` is `ContMDiff` at every point. -/
private theorem eval_contMDiffAt
    (α : HolomorphicOneForm (ℂ ⧸ L)) (x₀ : ℂ ⧸ L) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun x : ℂ ⧸ L => α.eval x) x₀ := by
  -- The chart-coord representative is ContMDiffAt by the section
  -- smoothness witness threaded through `cotangentSection_contMDiffAt_iff`.
  have h_rep : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun x : ℂ ⧸ L =>
        (cotangentBundleCore 𝓘(ℂ, ℂ) (ℂ ⧸ L)).coordChange
          (achart ℂ x) (achart ℂ x₀) x (α.eval x)) x₀ :=
    (cotangentSection_contMDiffAt_iff (fun x => α.eval x)).mp
      (α.contMDiff x₀)
  -- The chart-coord rep equals α.eval on a nhd of x₀.
  exact h_rep.congr_of_eventuallyEq (chart_rep_eq_eval_eventually L α x₀).symm

/-- **The coefficient function `dzCoeff α` is `ContMDiff ω`** as a
map `T_L → ℂ`. Compose `α.eval` with `ContinuousLinearMap.apply` at
`1 : ℂ`. -/
theorem dzCoeff_contMDiff (α : HolomorphicOneForm (ℂ ⧸ L)) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (dzCoeff L α) := by
  intro x₀
  have h_eval : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun x : ℂ ⧸ L => α.eval x) x₀ :=
    eval_contMDiffAt L α x₀
  -- Apply-at-1 as a CLM, hence `ContMDiff`.
  have h_apply : ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
      (fun φ : ℂ →L[ℂ] ℂ => ContinuousLinearMap.apply ℂ ℂ (1 : ℂ) φ) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiff
  -- Composition.
  have h_comp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : ℂ ⧸ L =>
        ContinuousLinearMap.apply ℂ ℂ (1 : ℂ) (α.eval x)) x₀ :=
    h_apply.contMDiffAt.comp x₀ h_eval
  -- The composition equals `dzCoeff α` definitionally:
  -- `ContinuousLinearMap.apply ℂ ℂ 1 φ = φ 1`.
  exact h_comp

/-! ## Liouville: the coefficient function is constant -/

/-- **`dzCoeff α` is a constant function** by Liouville on the compact
connected complex 1-manifold `T_L`. -/
theorem dzCoeff_isConstant (α : HolomorphicOneForm (ℂ ⧸ L)) :
    IsConstantMap (dzCoeff L α) := by
  -- T_L has all the needed instances: T2, Compact, Connected,
  -- ChartedSpace ℂ, IsManifold 𝓘(ℂ) ω (basic instances).
  exact contMDiff_omega_isConstant (X := ℂ ⧸ L) (dzCoeff L α)
    (dzCoeff_contMDiff L α)

/-! ## Reconstruction: `α = c • dz` -/

/-- **Each `α : HolomorphicOneForm T_L` is a complex scalar multiple
of `dz L`.** The scalar is `dzCoeff α p` for any `p` (it is the same
for all `p` by `dzCoeff_isConstant`). -/
theorem exists_smul_dz (α : HolomorphicOneForm (ℂ ⧸ L)) :
    ∃ c : ℂ, α = c • dz L := by
  obtain ⟨c, hc⟩ := dzCoeff_isConstant L α
  refine ⟨c, ?_⟩
  -- Show α = c • dz L by extensionality of `ContMDiffSection`.
  apply ContMDiffSection.ext
  intro p
  -- Goal: α.toFun p = (c • dz L).toFun p in CotangentSpace 𝓘(ℂ,ℂ) p.
  -- We work with `α.eval p` and `(c • dz L).eval p` (both : ℂ →L[ℂ] ℂ).
  -- (.eval p) and (.toFun p) are definitionally equal.
  have h_eval_eq : α.eval p = (c • dz L).eval p := by
    refine ContinuousLinearMap.ext fun v => ?_
    -- LHS: α.eval p v. By ℂ-linearity: α.eval p v = v • α.eval p 1.
    -- α.eval p 1 = dzCoeff α p = c (from hc).
    -- RHS: (c • dz L).eval p v. By module action: = c • (dz L).eval p v
    --       = c • id v = c • v = c * v. So LHS = v • c = v * c = c * v.
    have h_eval_smul : α.eval p v = v • α.eval p 1 := by
      conv_lhs => rw [show v = v • (1 : ℂ) from (mul_one v).symm]
      exact (α.eval p).map_smul v (1 : ℂ)
    have h_c : α.eval p 1 = c := hc p
    rw [h_eval_smul, h_c]
    -- Goal: v • c = (c • dz L).eval p v.
    -- (c • dz L).eval p v = c • (dz L).eval p v = c • id v = c • v.
    have h_rhs : (c • dz L).eval p v = c * v := by
      -- (c • dz L).eval p = c • (dz L).eval p as ℂ →L[ℂ] ℂ.
      have h_smul_eval : (c • dz L).eval p = c • (dz L).eval p := rfl
      rw [h_smul_eval, ContinuousLinearMap.smul_apply]
      -- (dz L).eval p = id ℂ ℂ.
      show c • ((dz L).eval p v) = c * v
      have h_dz_v : (dz L).eval p v = v := by
        -- (dz L).eval p : ℂ →L[ℂ] ℂ; by `dz_apply L p` it equals `id`.
        have h_eq : (dz L).eval p = (ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ) := by
          -- (dz L).eval p = (dz L).toFun p = id (def-equal via dz_apply).
          exact dz_apply L p
        rw [h_eq]
        rfl
      rw [h_dz_v, smul_eq_mul]
    rw [h_rhs]
    show v • c = c * v
    rw [smul_eq_mul, mul_comm]
  exact h_eval_eq

/-! ## Span = ⊤ and finrank ≤ 1 -/

/-- **The ℂ-span of `dz L` is all of `HolomorphicOneForm (ℂ ⧸ L)`.** -/
theorem holomorphicOneForm_eq_span_dz :
    Submodule.span ℂ ({dz L} : Set (HolomorphicOneForm (ℂ ⧸ L))) = ⊤ := by
  rw [eq_top_iff]
  intro α _
  obtain ⟨c, hc⟩ := exists_smul_dz L α
  rw [hc]
  exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))

/-- **`Module.finrank ℂ (HolomorphicOneForm (ℂ ⧸ L)) ≤ 1`** —
the upper bound. Every element is a `c • dz L`, so by
`Module.finrank_le_one` the dimension is `≤ 1`. -/
theorem finrank_holomorphicOneForm_le_one :
    Module.finrank ℂ (HolomorphicOneForm (ℂ ⧸ L)) ≤ 1 := by
  refine finrank_le_one (R := ℂ) (dz L) ?_
  intro α
  obtain ⟨c, hc⟩ := exists_smul_dz L α
  exact ⟨c, hc.symm⟩

/-! ## Genus bounds -/

/-- **`genus (ℂ ⧸ L) ≤ 1`** — the upper bound for the genus on T_L. -/
theorem genus_le_one :
    JacobianChallenge.genus (ℂ ⧸ L) ≤ 1 :=
  finrank_holomorphicOneForm_le_one L

/-- **`genus (ℂ ⧸ L) = 1`** — combining the lower bound (Forster Riesz
+ `dz_ne_zero`) with the upper bound (Liouville on a compact connected
1-manifold). -/
theorem genus_eq_one :
    JacobianChallenge.genus (ℂ ⧸ L) = 1 := by
  have h_le : JacobianChallenge.genus (ℂ ⧸ L) ≤ 1 := genus_le_one L
  have h_ge : 1 ≤ JacobianChallenge.genus (ℂ ⧸ L) := one_le_genus L
  omega

end ComplexTorus

end JacobianChallenge

end
