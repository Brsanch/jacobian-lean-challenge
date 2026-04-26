/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.FiberSum
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Divisor.PrincipalDivisorRange

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # The fibre-balance form of the residue theorem

This file packages the **R4** named gap of `Manifold/ResidueTheorem.lean`
in its cleanest, divisor-level form: the *signed multiplicity* of a
non-zero meromorphic function `f` on a compact connected Riemann surface
is the integer

  `signedMult f := (principalDivisorMap f).degree`

i.e. `∑_x ord_x f` summed over the (finite) support of the order divisor.
The R4 fibre-balance statement says this integer is zero — equivalently,
the number of zeros (counted with order) equals the number of poles
(counted with absolute order).

## What R4 actually says, abstractly

The classical topological-degree fact is: if `f : X → Y` is a non-constant
proper holomorphic map between compact connected Riemann surfaces, then
for every regular value `y ∈ Y`,

  `∑_{x ∈ f⁻¹{y}} mult_x(f) = deg f`,

a quantity independent of `y`. In the residue-theorem setting, one
canonically extends a non-zero meromorphic `f : X → ℂ` to the proper
holomorphic map `f̃ : X → S² = ℂ ∪ {∞}` (the Route A pole-extension of
`Manifold/ResidueTheorem.lean`'s R1) and applies the equality at the two
regular values `0` and `∞`. The local multiplicity at a zero is
`ord_x f` and at a pole is `-ord_x f`, so

  `(# zeros counted with order) = deg f̃ = (# poles counted with absolute order)`,

i.e. `∑_{ord_x f > 0} ord_x f + ∑_{ord_x f < 0} ord_x f = 0`. Summed over
the *whole* support, that is `(principalDivisorMap f).degree = 0`. This
file's `R4_signedMult_zero_statement` is precisely that.

## The point of `R4_signedMult_zero_iff_residueTheorem`

The lemma `R4_signedMult_zero_iff_residueTheorem` shows that **R4 in this
divisor-level form is *exactly* the residue-theorem statement** already
named as `JacobianChallenge.ResidueTheorem` in
`Divisor/PrincipalDivisorRange.lean`. Both sides unfold to

  `∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0`,

so the equivalence is `Iff.rfl`. We name the lemma anyway, with the
unfolding documented, because:

* it makes the *equality of statements* explicit rather than implicit;
* downstream consumers (and the `Manifold/ResidueTheorem.lean` skeleton)
  can route through either name, and any future change of either side
  immediately produces a compile-time mismatch caught here;
* it pins the structural decomposition: R1+R2+R3 (in `Manifold/ResidueTheorem.lean`)
  set up the topological-degree machinery, and R4 *is* the complete
  remaining content of the residue theorem.

## Anti-overclaim

This file does **not** prove R4. Both sides of
`R4_signedMult_zero_iff_residueTheorem` are *statements*, and the lemma
shows them to be the same statement. The deep classical content remains
`Manifold/ResidueTheorem.lean`'s `residue_theorem` `sorry`, which is
named (R5 in the Route-A decomposition) and which decomposes through
R1+R2+R3+R4 in this file's R4 form.

This file:

* defines `signedMult f := (principalDivisorMap f).degree` (a real `ℤ`,
  not a stub);
* defines `R4_signedMult_zero_statement X : Prop` as the assertion that
  `signedMult f = 0` for every `f` (a real `Prop`-valued `def`, not an
  axiom);
* proves `R4_signedMult_zero_iff_residueTheorem`: this `Prop` is `Iff.rfl`-
  equivalent to `JacobianChallenge.ResidueTheorem X`.

No `sorry`. No `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- For `f : MeromorphicNonzero X` on a compact Riemann surface, the
**net signed multiplicity** of the divisor of `f` is the integer

  `signedMult f := (principalDivisorMap f).degree`.

This is `∑_x ord_x f` summed over the (finite) support of the order
divisor (`Div.degree` packages the support sum, see
`JacobianChallenge.Div.degree` in `Divisor.lean`). The R4 fibre-balance
form of the residue theorem asserts that `signedMult f = 0` for every
non-zero meromorphic `f`. -/
noncomputable def signedMult (f : MeromorphicNonzero X) : ℤ :=
  (principalDivisorMap f).degree

/-- Definitional unfolding of `signedMult` as the divisor degree of the
principal divisor. Useful as a `simp`-friendly entry point. -/
@[simp] lemma signedMult_def (f : MeromorphicNonzero X) :
    signedMult f = (principalDivisorMap f).degree := rfl

/-- **R4 (statement only).** The signed-multiplicity sum is zero —
equivalently, the number of zeros (counted with order) equals the number
of poles (counted with absolute order).

In topological-degree language: `f : MeromorphicNonzero X` extends
canonically to a proper holomorphic map `f̃ : X → S²`, and `0`, `∞ ∈ S²`
are regular values of `f̃` with equal degree, giving
`(# zeros of f) = deg f̃ = (# poles of f)` (counted with multiplicity).

This is a `Prop`-valued `def`, **not an `axiom`**. It records the
statement so that downstream code can take it as a hypothesis. -/
def R4_signedMult_zero_statement (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  ∀ f : MeromorphicNonzero X, signedMult f = 0

/-- **The R4 statement is *exactly* the residue theorem.** Both sides
unfold to `∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0`:

* `R4_signedMult_zero_statement X` unfolds `signedMult` to
  `(principalDivisorMap f).degree`, then asserts this equals `0`.
* `ResidueTheorem X` (from `Divisor/PrincipalDivisorRange.lean`) directly
  asserts `(principalDivisorMap f).degree = 0` for every `f`.

The two `Prop`s are therefore *definitionally* equal, and the `Iff` is
`Iff.rfl`. We state and prove this equivalence anyway: it is the load-
bearing structural fact that R4 is *the entire residue-theorem content*
once R1+R2+R3 (the pole-extension, finite-fibres, and local-multiplicity-
equals-local-order pieces) are in hand.

The proof is `Iff.rfl` because:

* `signedMult f = 0` reduces to `(principalDivisorMap f).degree = 0` by
  `signedMult_def` (which is `rfl`).
* The two universally-quantified `Prop`s are then the same. -/
lemma R4_signedMult_zero_iff_residueTheorem
    [ConnectedSpace X] :
    R4_signedMult_zero_statement X ↔ ResidueTheorem X :=
  Iff.rfl

/-! ### Bonus: divisor-pullback restatement (sketch only)

The `Pic0.divPullback` infrastructure of `Divisor/FiberPullback.lean`
gives an additive divisor pullback `f^* : Div Y →+ Div X` for any
finite-fibre map. In the residue-theorem setting, applied to the
canonical pole-extension `f̃ : X → RiemannSphere` (R1), the divisor

  `D_zeros := f̃^*(Div.single 0)  =  ∑_{x ∈ f̃⁻¹{0}} Div.single x  =  zero-fibre divisor`
  `D_poles := f̃^*(Div.single ∞)  =  ∑_{x ∈ f̃⁻¹{∞}} Div.single x  =  pole-fibre divisor`

are the indicator divisors of the two fibres of interest, and the
fibre-balance equality

  `(# zeros) = (# poles)`        (cardinality)

translates via `Div.degree_fiberSum` (which says the degree of a fibre
sum equals the degree of the original times the fibre size) into the
*cardinality* form of R4. The full R4 (counted with multiplicity)
strengthens this by replacing each `Div.single x` term by
`(local-mult-of-f̃-at-x) • Div.single x`, which is precisely the content
that R3 supplies.

We do **not** assemble this restatement here as a Lean lemma: the
required pole-extension `f̃` is itself the (currently unbuilt) R1
construction, and stating the bonus lemma without it would require
introducing yet another named hypothesis with no compile-time content
beyond `Iff.rfl`. The point is recorded in this docstring as the
intended bridge from the cardinality-level fibre-balance machinery
already in `Divisor/FiberPullback.lean` to the multiplicity-level
fibre-balance R4 stated above. -/

end JacobianChallenge

end
