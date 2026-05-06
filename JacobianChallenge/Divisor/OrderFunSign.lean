/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Sign / vanishing helper lemmas for `MMeromorphicOn.orderFun`

The integer-valued `orderFun I f x = (mmeromorphicOrderAt I f x).untop₀` is
positive at zeros, negative at poles, and `0` at regular non-vanishing
points. This file collects a few small algebraic identities that follow
from already-established lemmas in `Divisor/PrincipalDivisor.lean`:

* `orderFun_const_ne_zero` — for any non-zero complex constant `c`,
  the order of `fun _ : X => c` at any point is `0`.
* `orderFun_one` — specialization at `c = 1`.
* `principalDivisorMap_apply_const` — pointwise value of the principal
  divisor of the `MeromorphicNonzero.const c hc` representative is `0`.
* `principalDivisorMap_apply_const_one` — same at `c = 1`.

Every body is one rewrite-step from existing infrastructure. No new
mathematical content is introduced; these are convenience names for
patterns that recur in downstream proofs.

No `axiom`, no `sorry`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

namespace MMeromorphicOn

universe u

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Order of a non-zero constant is zero.** For `c ≠ 0`, the integer
order of the constant function `fun _ : X => c` is `0` at every point. -/
@[simp] lemma orderFun_const_ne_zero
    {x : X} {c : ℂ} (hc : c ≠ 0) :
    orderFun (𝓘(ℂ, ℂ)) (fun _ : X => c) x = 0 := by
  unfold orderFun
  rw [JacobianChallenge.mmeromorphicOrderAt_const_ne_zero hc]
  rfl

/-- **Order of the constant function `1` is zero.** Specialization of
`orderFun_const_ne_zero` at `c = 1`. -/
@[simp] lemma orderFun_one (x : X) :
    orderFun (𝓘(ℂ, ℂ)) (fun _ : X => (1 : ℂ)) x = 0 :=
  orderFun_const_ne_zero (X := X) (x := x) one_ne_zero

end MMeromorphicOn

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Pointwise value of the principal divisor of a non-zero constant is
zero.** The principal divisor of `MeromorphicNonzero.const c hc`
(for `c ≠ 0`) takes the value `0` at every point. Combines
`principalDivisorMap_const` with the divisor-zero unfolding. -/
@[simp] lemma principalDivisorMap_apply_const
    (c : ℂ) (hc : c ≠ 0) (x : X) :
    (principalDivisorMap (MeromorphicNonzero.const (X := X) c hc) : X → ℤ) x = 0 := by
  rw [principalDivisorMap_const c hc]
  rfl

/-- **Pointwise value of the principal divisor of `1` is zero.**
Specialization at `c = 1`. -/
@[simp] lemma principalDivisorMap_apply_const_one (x : X) :
    (principalDivisorMap
        (MeromorphicNonzero.const (X := X) (1 : ℂ) one_ne_zero) : X → ℤ) x = 0 :=
  principalDivisorMap_apply_const (X := X) (1 : ℂ) one_ne_zero x

end JacobianChallenge
