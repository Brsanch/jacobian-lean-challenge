/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiouvilleForContMDiffOmega
import JacobianChallenge.Topology.S2ImpliesGenus0FromSimplyConnected
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Subsingleton of `HolomorphicOneForm X` from primitive existence

This file performs the **closing composition** of the
`HolomorphicOneFormSubsingletonOfSimplyConnected` arc. Given the
unconditional Liouville theorem
(`Topology.LiouvilleForContMDiffOmega.contMDiff_omega_isConstant`) for
`ContMDiff … ω` functions on compact connected complex 1-manifolds, and
the hypothesis that every holomorphic 1-form admits a global smooth
primitive (in the manifold-differential sense `om.eval x = mfderiv F x`),
we get `Subsingleton (HolomorphicOneForm X)`.

The primitive-existence hypothesis is the **remaining substantive
mathematical content** of the arc, corresponding to the classical
construction `F x := ∫_γ ω` along a smooth path γ from a basepoint —
well-defined on a simply-connected manifold by path-independence
(homotopy + closedness of holomorphic 1-forms + Stokes on the homotopy
disk). The chart-cover analytic-continuation across overlaps is owed in
`Manifold/AnalyticContinuationGlobalization.lean`; the smooth-Stokes
content on homotopies is owed in `Manifold/StokesCompactSurface.lean`.

What this file ships:

* `HolomorphicOneForm.eq_zero_iff_eval` — pointwise vanishing of
  `om.eval` characterizes the zero form. General-X analog of
  `RiemannSphere.eq_zero_iff_eval_eq_zero`.

* `HolomorphicOneForm.eq_zero_of_primitive_const` — if `om = mfderiv F`
  pointwise and `F` is constant, then `om = 0`. (Pure algebra; no
  topology / analyticity needed.)

* `holomorphicOneForm_eq_zero_of_smooth_primitive` — the main lemma:
  combines the unconditional Liouville with the constant-derivative
  identity to show that any `om : HolomorphicOneForm X` admitting a
  `ContMDiff ω` primitive on a compact connected complex 1-manifold is
  the zero form.

* `subsingleton_of_primitiveExistence` — the headline. From the
  hypothesis that every `om` admits such a primitive, every `om` is
  zero, hence `Subsingleton (HolomorphicOneForm X)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology Bundle ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Extensionality at the eval level -/

/-- A holomorphic 1-form is zero iff its `eval` vanishes at every point.
General-X analog of `RiemannSphere.eq_zero_iff_eval_eq_zero` from
`Manifold/RiemannSphereCoefficientVanishing.lean`. -/
theorem HolomorphicOneForm.eq_zero_iff_eval (om : HolomorphicOneForm X) :
    om = 0 ↔ ∀ x : X, om.eval x = 0 := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · rw [h]; exact HolomorphicOneForm.eval_zero x
  · -- Use DFunLike.ext / ContMDiffSection.ext on the underlying section.
    let s :
        ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
          𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _) := om
    show s = (0 :
        ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
          𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _))
    refine ContMDiffSection.ext (fun x => ?_)
    have hx : s x = om.eval x := rfl
    have h0 :
        ((0 : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
            𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
            (CotangentSpace 𝓘(ℂ) : X → Type _))) x = 0 := by
      rw [ContMDiffSection.coe_zero]
      rfl
    rw [hx, h0]
    exact h x

/-! ## Constant primitive ⇒ zero form -/

/-- If `om = mfderiv F` pointwise on `X` and `F` is a constant function,
then `om` is the zero 1-form. Pure algebra: `mfderiv` of a constant is
zero (mathlib `mfderiv_const`). -/
theorem HolomorphicOneForm.eq_zero_of_primitive_const
    (om : HolomorphicOneForm X)
    (c : ℂ)
    (h_primitive : ∀ x : X,
        om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (fun _ : X => c) x) :
    om = 0 := by
  rw [eq_zero_iff_eval]
  intro x
  rw [h_primitive x]
  exact mfderiv_const

/-! ## Main closing composition -/

/-- **Main lemma.** If `om : HolomorphicOneForm X` admits a smooth
primitive `F : X → ℂ` (with `om.eval = mfderiv F` pointwise, and `F`
`ContMDiff … ω`), then on a compact connected complex 1-manifold, `om`
is the zero 1-form.

Proof: `F` is constant by the unconditional Liouville
(`contMDiff_omega_isConstant`); a constant function has zero `mfderiv`
everywhere (`mfderiv_const`); hence `om.eval x = 0` for all `x`; hence
`om = 0` by `eq_zero_iff_eval`. -/
theorem holomorphicOneForm_eq_zero_of_smooth_primitive
    (om : HolomorphicOneForm X)
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_primitive : ∀ x : X,
        om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x) :
    om = 0 := by
  -- Step 1: F is constant via unconditional Liouville.
  obtain ⟨c, hc⟩ : IsConstantMap F :=
    contMDiff_omega_isConstant F h_smooth
  -- Step 2: F equals the constant function (fun _ => c).
  have hF_const : F = (fun _ : X => c) := funext hc
  -- Step 3: Rewrite the primitive identity using F = const c, then
  -- delegate to eq_zero_of_primitive_const.
  apply HolomorphicOneForm.eq_zero_of_primitive_const om c
  intro x
  have := h_primitive x
  rw [hF_const] at this
  exact this

/-- **Pointwise `eval x 1` criterion.** A continuous ℂ-linear functional
`ℂ →L[ℂ] ℂ` vanishes iff it sends `1` to `0` (it is determined by its
value at `1`). General-X analog of
`RiemannSphere.cotangent_eq_zero_of_apply_one_zero`. -/
private theorem cotangent_eq_zero_of_apply_one_zero
    (L : ℂ →L[ℂ] ℂ) (h : L 1 = 0) : L = 0 := by
  refine ContinuousLinearMap.ext (fun z => ?_)
  have hz : L z = z • L 1 := by
    have : L z = L (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    rw [this, map_smul]
  rw [hz, h, smul_zero]
  rfl

/-- A holomorphic 1-form is zero iff its `eval` applied to `1 : ℂ`
vanishes at every point. General-X analog of
`RiemannSphere.eq_zero_iff_eval_at_one_eq_zero`. -/
theorem HolomorphicOneForm.eq_zero_iff_eval_at_one
    (om : HolomorphicOneForm X) :
    om = 0 ↔ ∀ x : X, om.eval x 1 = 0 := by
  rw [eq_zero_iff_eval]
  refine forall_congr' (fun x => ?_)
  refine ⟨fun h => by rw [h]; rfl, fun h => ?_⟩
  exact cotangent_eq_zero_of_apply_one_zero (om.eval x) h

/-- **Subsingleton from pointwise `eval x 1` vanishing.** If every
holomorphic 1-form satisfies `om.eval x 1 = 0` at every point, then
`HolomorphicOneForm X` is a subsingleton. General-X analog of
`RiemannSphere.subsingleton_of_eval_at_one_eq_zero`. -/
theorem subsingleton_of_eval_at_one_eq_zero
    (h : ∀ (om : HolomorphicOneForm X) (x : X), om.eval x 1 = 0) :
    Subsingleton (HolomorphicOneForm X) := by
  refine subsingleton_of_forall_eq 0 (fun om => ?_)
  rw [HolomorphicOneForm.eq_zero_iff_eval_at_one]
  exact h om

/-- **Headline architectural reduction.** If every `om : HolomorphicOneForm X`
admits a smooth primitive on the compact connected complex 1-manifold,
then `HolomorphicOneForm X` is a `Subsingleton`.

This is the **closing composition** that uses the unconditional Liouville
to discharge the analytic side of the
`HolomorphicOneFormSubsingletonOfSimplyConnected` arc. The remaining
content — the primitive-existence hypothesis — is the smooth-Stokes /
path-integral construction on a simply-connected manifold, owed in
`Manifold/StokesCompactSurface.lean` and
`Manifold/AnalyticContinuationGlobalization.lean`. -/
theorem subsingleton_of_primitiveExistence
    (h_primitive_exists : ∀ om : HolomorphicOneForm X,
        ∃ F : X → ℂ,
          ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
            ∀ x : X, om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x) :
    Subsingleton (HolomorphicOneForm X) := by
  have h_eq_zero : ∀ om : HolomorphicOneForm X, om = 0 := by
    intro om
    obtain ⟨F, hF_smooth, hF_primitive⟩ := h_primitive_exists om
    exact holomorphicOneForm_eq_zero_of_smooth_primitive om F hF_smooth hF_primitive
  refine ⟨fun om₁ om₂ => ?_⟩
  rw [h_eq_zero om₁, h_eq_zero om₂]

/-! ## Bridge to the named `HolomorphicOneFormSubsingletonOfSimplyConnected`
predicate -/

/-- **Bridge.** Discharges
`HolomorphicOneFormSubsingletonOfSimplyConnected X` (the named
hypothesis on the simple-connectedness route to Item 14's reverse leg,
in `Topology/S2ImpliesGenus0FromSimplyConnected.lean`) from a
primitive-existence hypothesis parameterized on simple-connectedness.

After this commit, the simple-connectedness route to Item 14's reverse
leg factors as:

```
S2ImpliesGenus0 X
  ⟸ s2ImpliesGenus0_from_simplyConnected         (existing in repo)
    needs: SimplyConnectedS2 (DISCHARGED unconditionally in
                              `SimplyConnectedS2Unconditional.lean`)
       and: HolomorphicOneFormSubsingletonOfSimplyConnected X
                  ⟸ THIS BRIDGE
                  needs: primitive existence under simple-connectedness
                         (the smooth-Stokes / path-integral content
                          owed in `Manifold/StokesCompactSurface.lean`).
```

So the single owed input to the reverse leg of Item 14 is now the
**primitive-existence** statement parameterized on simple-connectedness.
This is, classically, the construction `F x := ∫_γ ω` along a smooth
path from a chosen basepoint, well-defined on a simply-connected
manifold by the homotopy-Stokes argument (closed 1-form + boundary of
homotopy disk integral = 0). -/
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence
    (h_primitive_exists : SimplyConnectedSpace X →
        ∀ om : HolomorphicOneForm X,
          ∃ F : X → ℂ,
            ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
              ∀ x : X, om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x) :
    HolomorphicOneFormSubsingletonOfSimplyConnected X := fun h_sc =>
  subsingleton_of_primitiveExistence (h_primitive_exists h_sc)

/-- **Full-arc composition: `S2ImpliesGenus0 X` from primitive
existence.** Composes the bridge above with the existing
`s2ImpliesGenus0_from_simplyConnected` reduction (already in
`Topology/S2ImpliesGenus0FromSimplyConnected.lean`) and the
unconditional `simplyConnectedS2_holds` (in
`Topology/SimplyConnectedS2Unconditional.lean`, the 15-chip Phase-3
arc landed 2026-05-15).

Net effect: the reverse leg of Item 14 (`S2ImpliesGenus0 X`) reduces
to **one named classical input**:

* `h_primitive_exists` — for every holomorphic 1-form on a
  simply-connected compact connected complex 1-manifold, a smooth
  primitive exists.

This is the smooth-Stokes / path-integral content, structurally owed
in `Manifold/StokesCompactSurface.lean`. -/
theorem s2ImpliesGenus0_of_primitiveExistence
    (h_S2_sc : SimplyConnectedS2)
    (h_primitive_exists : SimplyConnectedSpace X →
        ∀ om : HolomorphicOneForm X,
          ∃ F : X → ℂ,
            ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
              ∀ x : X, om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_from_simplyConnected X h_S2_sc
    (holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence
      h_primitive_exists)

end JacobianChallenge

end
