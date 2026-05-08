# Handoff: ZZ177 `Basic.lean` `Jacobian.pullback` swap blocker

## Status: blocked on multiplicity-weighted fibre sum

ZZ172 + ZZ176 corrected the `RegularValueWitnessReg` type and discharged
the topological residual in `fibre_card_well_defined_at_regular_statement`.
The remaining `h_pkg` is the per-`f` analytic packaging (locally-constant
fibre `ncard` on the regular subset). On its own this is not enough to
close OPEN.md items 8 / 13 / 21 / 22 / 24, all of which involve
`Jacobian.pullback`.

## What is built

- `Divisor/FiberSum.lean` — `Div.fiberSum f hf : Div Y →+ Div X` with
  `fiberSumFun D := ∑ y ∈ supp D, D y • (∑ x ∈ (hf y).toFinset, single x)`.
- `Divisor/FiberPullback.lean`:
  - `Div.degree_fiberSum`: `(fiberSum D).degree = ∑ y ∈ supp D, D y · |f⁻¹{y}|`.
  - `Div.fiberSum_mem_Div0_of_const_card`: with **global** `hN : ∀ y, |f⁻¹{y}| = N`,
    `fiberSum` sends `Div⁰ Y → Div⁰ X`.
  - `Pic0.divPullback f hf N hN : Div0 Y →+ Div0 X` and the descent
    `Pic0.pullback f hf N hN : Pic0 Y →+ Pic0 X`.
  - `Pic0.pullback_id : pullback id _ 1 _ P = P` — proved at line 264.
  - `Pic0.pushforward_pullback : pushforward f (pullback f hf N hN P) = (N:ℤ) • P` —
    proved at line 405.

## What ZZ176 actually delivers

`fibre_card_well_defined_at_regular_holds_of_h_pkg` (post-ZZ172 + ZZ176)
gives, given the analytic packaging:

```
∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card
```

**This is constancy on regular witnesses, not on every fibre.** For non-
constant analytic `f : X → Y` between compact connected Riemann surfaces
with branch points, the fibre cardinality `|f⁻¹{y}|` *drops* at branch
values (multiple sheets coalesce). So
`hN : ∀ y, (hf y).toFinset.card = N` is **genuinely false** for any
branched `f`, and not derivable from ZZ176.

## Why the existing `Pic0.pullback` cannot bridge

`Pic0.pullback` is the unramified-cover construction:

```lean
noncomputable def pullback
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN : ∀ y, (hf y).toFinset.card = N) :
    Pic0 Y →+ Pic0 X
```

It requires global constant card (`hN`) so that `divPullback` preserves
`Div⁰` membership: with `D ∈ Div⁰ Y` (i.e. `∑ supp D, D y = 0`),
`(fiberSum D).degree = ∑ supp D, D y · N(y)` is `0` only when `N(·)` is
constant on `supp D`, and since `D` is arbitrary in `Div⁰`, the constancy
must be global.

Most analytic non-constant `f` between compact connected RS are branched
(e.g. `f(z) = z²` on `RiemannSphere` has branching at 0 and ∞). So this
construction does **not** apply to the generic case.

## What is genuinely owed

The honest classical pullback uses **multiplicity-weighted** fibre sums:

```
f^*(single y) := ∑_{x ∈ f⁻¹{y}} e_x(f) · single x
```

where `e_x(f)` is the local ramification index at `x`. The total weight
`∑_{x ∈ f⁻¹{y}} e_x(f) = deg(f)` is constant in `y` (by the
fundamental theorem of algebra applied to the local normal form
`f = w₀ + ψ^k`), giving degree preservation on `Div⁰` without any global
fibre-cardinality hypothesis.

The repo has the planar piece:
`Manifold/LocalKFoldMultiplicityFullyUnconditional.lean` provides
`localKFoldMultiplicity_preimage_card_fully_unconditional`, the
`g(z) = z^k`-style local k-fold multiplicity statement on `ℂ → ℂ`. What
is **not** built:

1. **Manifold-side ramification index** `e_x(f) : ℕ` for `f : X → Y`
   between complex 1-manifolds, plus `∑_{x ∈ f⁻¹{y}} e_x(f) = N` for
   `N := degreeFiber f hf` on regular values.
2. **Multiplicity-weighted divisor pullback**:
   `Div.fiberSum_weighted f hf e : Div Y →+ Div X` with
   `D ↦ ∑ y ∈ supp D, D y • (∑ x ∈ (hf y).toFinset, e x • single x)`.
3. **Degree-preservation lemma** for the weighted sum.
4. **Descent** through `Div⁰ Y →+ Div⁰ X →+ Pic⁰ Y →+ Pic⁰ X`.
5. **Bridge** to `Basic.lean`: `→+` to `→ₜ+` lift (immediate for the
   discrete topology on `Jacobian = Pic⁰`), and a swap of
   `Jacobian.pullback`'s body in `Jacobian.lean` from the zero stub to
   the weighted construction.

Items 1 and 5.bridge are the largest. Item 2-4 mirror existing
unweighted code (`fiberSum_mem_Div0_of_const_card` etc.) with the cardinality
replaced by a sum over weights.

## Items unblocked vs. still blocked

- **Item 21** (`pullback_id_apply`): unblocked at the `Pic⁰` level
  (`Pic0.pullback_id` exists). Still blocked at the `Basic.lean` level
  because `Jacobian.pullback id P = 0` for the current zero stub. Strict
  closure requires either:
  - (a) Body swap in `Jacobian.lean` so `Jacobian.pullback id` returns
    the honest identity, **plus** generic `f` falls through to the
    weighted construction.
  - (b) A new constructor that handles `f = id` via the singleton-fibre
    witnesses without the weighted construction. Same as (a) modulo
    naming.
- **Item 22** (`pullback_comp_apply`): currently STUB-vacuous (`0 ∘ 0 = 0`).
  Strict closure same as item 21.
- **Item 24** (`pushforward_pullback`): blocked on the swap. The `Pic⁰`-side
  identity `Pic0.pushforward_pullback = N • id` is built; the swap is the
  one-line bridge.
- **Items 8, 13** (object-level pullback `pullback : Jacobian Y →ₜ+ Jacobian X`
  and `pullback_contMDiff`): blocked on the swap.

## Recommended next chip (ZZ179)

Build the manifold-side ramification index `e_x(f) : ℕ` from the planar
`localKFoldMultiplicity_preimage_card_fully_unconditional` via chart
pullback. Then mirror `Divisor/FiberPullback.lean` in a new file
`Divisor/FiberPullbackWeighted.lean` and rebuild the descent chain.

Estimated scope: ~500-800 LOC across 2-3 new files. Items 8/13/21/22/24
all close together when this lands and the body swap in `Jacobian.lean`
goes in.
