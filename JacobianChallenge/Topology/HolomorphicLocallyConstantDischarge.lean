/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiouvilleFromLocalConstancy
import JacobianChallenge.Manifold.HolomorphicFoundational
import JacobianChallenge.Manifold.MaxModLocalConstancy
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Connected.Basic

set_option diagnostics.threshold 100

/-! # `HolomorphicLocallyConstant X` discharged UNCONDITIONALLY

This chip ships the **clopen globalisation** of zz349's chart-level
local constancy at the modulus maximum, closing zz347's
`HolomorphicLocallyConstant X` without further open hypotheses.

## Proof outline

Let `f : MeromorphicNonzero X` be holomorphic (order ≥ 0 everywhere).
1. By compactness (zz348), `‖f.toFun‖` attains its global max at some
   `c : X`.
2. Let `S := {x : X | f.toFun x = f.toFun c}`. We show `S = X`.
3. **`S` is closed** (zz348's `isClosed_eq_value_of_holomorphic`).
4. **`S` is open**: for any `x ∈ S`, `‖f.toFun x‖ = ‖f.toFun c‖ =
   max`, so `x` is also a max. By zz349's
   `eventually_eq_const_at_max` applied at `x`, `f.toFun` is
   eventually equal to `f.toFun x = f.toFun c` near `x`, providing
   a neighbourhood of `x` in `S`.
5. **`S` is nonempty** (`c ∈ S`).
6. By `ConnectedSpace X` (which extends `PreconnectedSpace`), the
   only nonempty clopen subset is `Set.univ`. Hence `S = X`,
   i.e. `f.toFun ≡ f.toFun c`.
7. Globally constant ⇒ locally constant via
   `IsLocallyConstant.of_constant`.

## Net effect on the project

After this chip, the **only remaining open input** for
`RiemannRochGenusZero X` is
`ExistsNonConstantBoundedByDeltaP_GenusZero X` (the Riemann-Roch +
Serre-duality `dim L(δp) ≥ 2` consequence at genus 0). The Liouville
half of zz346's split is fully closed.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MeromorphicNonzero

variable {X}

/-- **Key step: the set where `f.toFun = f.toFun c` is open.** When
`c` is the global max of `‖f.toFun‖`, *any* point `x` in the level
set inherits the max property (`‖f.toFun x‖ = ‖f.toFun c‖`), so
zz349's chart-level local constancy applies at `x` too. -/
lemma isOpen_eq_value_at_max
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    {c : X} (hc_max : IsMaxOn (fun x => ‖f.toFun x‖) Set.univ c) :
    IsOpen {x : X | f.toFun x = f.toFun c} := by
  rw [isOpen_iff_eventually]
  intro x hx
  -- hx : f.toFun x = f.toFun c
  -- ‖f.toFun x‖ = ‖f.toFun c‖, so x is also a max.
  have hx_max : IsMaxOn (fun y => ‖f.toFun y‖) Set.univ x := by
    intro y _
    have h1 : ‖f.toFun y‖ ≤ ‖f.toFun c‖ := hc_max (Set.mem_univ _)
    -- Membership shape: goal is `‖f.toFun y‖ ≤ ‖f.toFun x‖`.
    show ‖f.toFun y‖ ≤ ‖f.toFun x‖
    rw [hx]
    exact h1
  -- Apply zz349 at x.
  have h_local := eventually_eq_const_at_max f h_holo hx_max
  -- h_local : f.toFun =ᶠ[𝓝 x] (fun _ => f.toFun x)
  -- We need f.toFun =ᶠ[𝓝 x] (fun _ => f.toFun c). Use hx.
  filter_upwards [h_local] with y hy
  rw [hy, hx]

/-- **Globalisation: `f.toFun ≡ f.toFun c` on all of `X`** when `c`
is the global maximum of `‖f.toFun‖`. Clopen + nonempty + connected
=> all of `X`. -/
theorem toFun_eq_const_at_max
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    {c : X} (hc_max : IsMaxOn (fun x => ‖f.toFun x‖) Set.univ c) :
    ∀ x : X, f.toFun x = f.toFun c := by
  -- The level set is clopen, nonempty, contained in X.
  set S : Set X := {x | f.toFun x = f.toFun c} with hS_def
  have h_closed : IsClosed S := isClosed_eq_value_of_holomorphic f h_holo c
  have h_open : IsOpen S := isOpen_eq_value_at_max f h_holo hc_max
  have h_clopen : IsClopen S := ⟨h_closed, h_open⟩
  have h_nonempty : S.Nonempty := ⟨c, by simp [hS_def]⟩
  -- Connected ⇒ Preconnected ⇒ only nonempty clopen is univ.
  have h_S_eq_univ : S = Set.univ := by
    have h_disj := isClopen_iff.mp h_clopen
    rcases h_disj with h_empty | h_univ
    · exact absurd h_empty h_nonempty.ne_empty
    · exact h_univ
  intro x
  have : x ∈ S := by rw [h_S_eq_univ]; trivial
  exact this

end MeromorphicNonzero

/-- **`HolomorphicLocallyConstant X` UNCONDITIONALLY.** A holomorphic
`MeromorphicNonzero X` function is constant on `X`, hence (trivially)
locally constant. -/
theorem holomorphicLocallyConstant_holds :
    HolomorphicLocallyConstant X := by
  intro f h_holo
  -- Get the global maximum.
  haveI : Nonempty X := inferInstance
  obtain ⟨c, hc_max⟩ :=
    MeromorphicNonzero.exists_norm_isMaxOn_of_holomorphic f h_holo
  -- f.toFun is globally constant = f.toFun c.
  have h_const : ∀ x : X, f.toFun x = f.toFun c :=
    MeromorphicNonzero.toFun_eq_const_at_max f h_holo hc_max
  -- Constant ⇒ locally constant.
  exact IsLocallyConstant.of_constant _ fun x y => by rw [h_const x, h_const y]

/-- **`LiouvilleOnCompactConnected X` UNCONDITIONALLY.** Direct
consequence of `holomorphicLocallyConstant_holds`. -/
theorem liouvilleOnCompactConnected_holds :
    LiouvilleOnCompactConnected X :=
  liouvilleOnCompactConnected_of_holomorphicLocallyConstant X
    (holomorphicLocallyConstant_holds X)

/-- **`RiemannRochGenusZero X` reduced to exactly ONE remaining named
classical input**: the Riemann-Roch + Serre-duality content. -/
theorem riemannRochGenusZero_from_existsBoundedByDeltaP
    (hA : ExistsNonConstantBoundedByDeltaP_GenusZero X) :
    RiemannRochGenusZero X :=
  riemannRochGenusZero_from_split X hA (liouvilleOnCompactConnected_holds X)

end JacobianChallenge

end
