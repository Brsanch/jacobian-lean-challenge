/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.MeromorphicAt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Compactness.Compact

set_option diagnostics.threshold 100

/-! # Foundational lemmas on holomorphic `MeromorphicNonzero X` functions

For `f : MeromorphicNonzero X` with `∀ x, 0 ≤ mmeromorphicOrderAt
I f.toFun x` (i.e. holomorphic everywhere on a compact complex
1-manifold), this file ships the *elementary* foundational lemmas
needed by the max-modulus closure of zz347's
`HolomorphicLocallyConstant X`:

* `toFun_continuous_of_holomorphic` — `f.toFun : X → ℂ` is continuous
  globally. Direct from `MeromorphicNonzero`'s `regular_continuousAt`
  field applied pointwise.

* `exists_norm_isMaxOn_of_holomorphic` — `‖f.toFun‖` attains its
  global maximum at some `c : X`. Direct from
  `IsCompact.exists_isMaxOn` on `CompactSpace X` with the
  continuous-norm composition.

* `isClosed_norm_eq_max_of_holomorphic` — the set
  `{x | ‖f.toFun x‖ = ‖f.toFun c‖}` is closed in `X`. Continuous
  function + T2 codomain preimage of singleton.

The non-elementary remaining step (chart-level max-mod producing
local constancy at the max) is a separate downstream chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Set Topology

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- **Continuity of `f.toFun` under holomorphy.** If `f :
MeromorphicNonzero X` has order `≥ 0` everywhere, then `f.toFun` is
continuous on `X`.

The proof is a direct point-wise application of `f`'s
`regular_continuousAt` field. -/
theorem toFun_continuous_of_holomorphic
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    Continuous f.toFun := by
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  exact f.regular_continuousAt x (h_holo x)

/-- **Maximum-attainment for `‖f.toFun‖`.** Under the same holomorphy
hypothesis, there exists `c : X` such that `‖f.toFun c‖` is the
global maximum of `‖f.toFun·‖` on `X`.

Uses `IsCompact.exists_isMaxOn` on `CompactSpace X` + continuity of
the norm composition. -/
theorem exists_norm_isMaxOn_of_holomorphic
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    [Nonempty X] :
    ∃ c : X, IsMaxOn (fun x => ‖f.toFun x‖) Set.univ c := by
  -- The norm function is continuous on the universe.
  have h_cts : Continuous (fun x : X => ‖f.toFun x‖) :=
    continuous_norm.comp (toFun_continuous_of_holomorphic f h_holo)
  have h_univ_compact : IsCompact (Set.univ : Set X) := isCompact_univ
  obtain ⟨c, _hc_univ, hc_max⟩ :=
    h_univ_compact.exists_isMaxOn Set.univ_nonempty h_cts.continuousOn
  exact ⟨c, hc_max⟩

/-- **The level set `{x | ‖f.toFun x‖ = ‖f.toFun c‖}` is closed.** -/
theorem isClosed_norm_eq_max_of_holomorphic
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (c : X) :
    IsClosed {x : X | ‖f.toFun x‖ = ‖f.toFun c‖} := by
  have h_cts : Continuous (fun x : X => ‖f.toFun x‖) :=
    continuous_norm.comp (toFun_continuous_of_holomorphic f h_holo)
  exact isClosed_eq h_cts continuous_const

/-- **The level set `{x | f.toFun x = f.toFun c}` is closed.** A
companion to the norm level set, useful in the second half of the
max-modulus argument (after upgrading constant-modulus to constant
value via the open-mapping theorem). -/
theorem isClosed_eq_value_of_holomorphic
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (c : X) :
    IsClosed {x : X | f.toFun x = f.toFun c} :=
  isClosed_eq (toFun_continuous_of_holomorphic f h_holo) continuous_const

end MeromorphicNonzero

end JacobianChallenge

end
