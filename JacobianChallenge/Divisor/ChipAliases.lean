/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Divisor.MeromorphicNonzeroGerm
import JacobianChallenge.Manifold.ResidueTheorem

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chip-named aliases for `principalDivisorMap` / `mmeromorphicOrderAt`
landed lemmas

This file collects short alias lemmas under the "chip-menu" names that
downstream files (and external readers following the chip menu) might reach
for. Every lemma here is an exact restatement (`= rfl`-direction `:=`) of a
fully proved lemma already living elsewhere in the repository — so this
file introduces **no new mathematical content**, only canonical names.

Aliases provided:

* `JacobianChallenge.mmeromorphicOrderAt_const_zero` — restatement of
  `mmeromorphicOrderAt_const_ne_zero`
  (`Divisor/PrincipalDivisor.lean`).
* `JacobianChallenge.principalDivisorMap_neg` — restatement of
  `principalDivisorMap_invMer`
  (`Divisor/MeromorphicNonzeroGerm.lean`).
* `JacobianChallenge.MeromorphicNonzero.const_one` — the constant-`1`
  specialization of `principalDivisorMap_const`, sealing the
  `principalDivisorMap (const 1 one_ne_zero) = 0` form.
* `JacobianChallenge.ResidueTheorem.const` — restatement of
  `residueTheorem_const`
  (`Divisor/PrincipalDivisor.lean`): the residue theorem holds
  unconditionally for non-zero constant functions.

No `axiom`, no `sorry`. Each body is one line.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chip A.** For a non-zero complex constant `c`, the chart-pulled-back
meromorphic order of `fun _ : X => c` at any point is `0`.

This is the chip-menu name for `mmeromorphicOrderAt_const_ne_zero`
(`Divisor/PrincipalDivisor.lean`); recorded here so the literal chip-menu
identifier is referenceable. -/
lemma mmeromorphicOrderAt_const_zero
    {x : X} {c : ℂ} (hc : c ≠ 0) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (fun _ : X => c) x = 0 :=
  mmeromorphicOrderAt_const_ne_zero hc

/-- **Chip B.** The principal-divisor of the representative-level inverse
`MeromorphicNonzero.invMer f` is the negation of the principal-divisor of
`f`.

Chip-menu name for `principalDivisorMap_invMer`
(`Divisor/MeromorphicNonzeroGerm.lean`). -/
lemma principalDivisorMap_neg (f : MeromorphicNonzero X) :
    principalDivisorMap (MeromorphicNonzero.invMer f)
      = -principalDivisorMap f :=
  principalDivisorMap_invMer f

namespace MeromorphicNonzero

/-- **Chip E.** The principal-divisor of the constant function `1` is the
zero divisor.

Specialization of `JacobianChallenge.principalDivisorMap_const`
(`Divisor/PrincipalDivisor.lean`) at `c = 1`. -/
@[simp] lemma const_one :
    JacobianChallenge.principalDivisorMap
        (MeromorphicNonzero.const (X := X) (1 : ℂ) one_ne_zero)
      = (0 : Div X) :=
  JacobianChallenge.principalDivisorMap_const (X := X) (1 : ℂ) one_ne_zero

end MeromorphicNonzero

namespace ResidueTheorem

/-- **Chip F.** The **residue theorem** holds for non-zero constant
functions: the principal divisor of `MeromorphicNonzero.const c hc` has
degree zero.

Chip-menu name for `JacobianChallenge.residueTheorem_const`
(`Divisor/PrincipalDivisor.lean`). Recorded under the
`ResidueTheorem.const` name so the constant-function instance of the
headline residue theorem is reachable through the `ResidueTheorem`
namespace. -/
lemma const (c : ℂ) (hc : c ≠ 0) :
    (JacobianChallenge.principalDivisorMap
        (MeromorphicNonzero.const (X := X) c hc)).degree = 0 :=
  JacobianChallenge.residueTheorem_const (X := X) c hc

end ResidueTheorem

end JacobianChallenge
