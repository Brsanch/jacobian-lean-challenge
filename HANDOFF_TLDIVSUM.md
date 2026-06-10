# `TLDivSumHypothesis L` — handoff (the last named hypothesis for the T_L C3 closure)

**Status 2026-06-09**: OPEN. This is now the ONLY named hypothesis between
the tree and `Nonempty (C3FullInputExtSymp (ℂ ⧸ L))`
(`nonempty_C3FullInputExtSymp_complexTorus_of_TLDivSum` in
`Manifold/TLAbelConverseFromTLDivSum.lean` consumes it alone;
`TLAbelConverseHypothesis` was discharged from it 2026-06-09).

**Statement** (`Manifold/AbelHypothesisReductionComplexTorus.lean:53`):
for every `f : MeromorphicNonzero (ℂ ⧸ L)`,
`∑ x ∈ supp(div f), ord_x(f) • x = 0` in `ℂ ⧸ L` — forward Abel for
elliptic functions.

**Classical proof** (the only known route not needing σ/θ): contour
integration of `z·F'/F` over a fundamental parallelogram `Π` of the lift
`F = f ∘ mkQ`. The 2026-06-09 σ-scaffold branch's
`TLDivSumScaffold.lean` records the strategy skeleton (24 sorries, no
content); treat as a comment, not a base.

## Decomposition with per-piece status

Write `g := F'/F`, `Π = Π(a) := a + [0,1]ω₁ + [0,1]ω₂`
(`ω_i := basisFin2OfL`), `I(a) := ∮_{∂Π(a)} z·g(z) dz` (four interval
integrals).

| # | Piece | Status / cost |
|---|---|---|
| 0 | Lift meromorphy + order correspondence (`F` meromorphic on ℂ, `ord_z F = ord_{mkQ z} f`) | ✅ **DONE 2026-06-09 unconditional** — `Manifold/ComplexTorusLiftedOrderCorrespondence.lean` (`liftedOrderCorrespondence_holds`, `meromorphic_liftedFun`) |
| 1 | Pairing algebra: `I(a) = -ω₁·Δ_v - ω₂·Δ_h` where `Δ_h/Δ_v` are the unweighted `∫ g` along the two generator sides (opposite-side cancellation by periodicity + reparametrization) | elementary, long (~400–800 LOC interval-integral algebra); needs piece 4's regular position for integrability |
| 2 | Winding integrality: `Δ_h, Δ_v ∈ 2πi·ℤ` | ✅ **ENGINE DONE 2026-06-10** — `Analysis/LogDerivWinding.lean`: `exp_integral_logDeriv` (the exp-identity `exp(∫φ'/φ) = φ1/φ0`), `integral_logDeriv_closed_mem` (closed loop ⟹ `2πi·ℤ`), `sum_integral_logDeriv_chain_mem` (cyclic chains). Applying to `Δ_h, Δ_v` needs only piece 4's regular position + the chain rule for `F ∘ side` |
| 3 | **Residue side: `I(a) = 2πi·∑_{x̃ ∈ Π} ord_{x̃}(F)·x̃`** | ⚠️ remaining wall, but **the keystone is DONE** — see below |
| 4 | Regular position: choose `a` with `∂Π(a)` avoiding the zero/pole set of `F` (= `L`-translates of the finite `supp(div f)` lifted) | countable-bad-set avoidance (~200–400 LOC); the bad `a`-set per side is a finite union of `L`-translate line families; a Baire/measure or explicit-perturbation argument |
| 5 | Bookkeeping: zeros in `Π` are a complete set of representatives; `∑ ord·x̃ mod L` = `evalSum (div f)`; assemble 1+2+3 ⟹ `evalSum ∈ L`-image = 0 | mechanical given 0 and 3 (~200–400 LOC) |

## ✅ KEYSTONE DONE (2026-06-10)

`Analysis/ParallelogramWinding.lean` + `Analysis/ArctanLinearIntegral.lean`
+ `Analysis/ParallelogramWindingEval.lean`:

* `ParallelogramWinding.boundaryIntegral a ω₁ ω₂ f` — the four-side
  contour integral over `∂Π(a; ω₁, ω₂)`;
* `parallelogram_winding_integrality` — `∮ (z−x)⁻¹ ∈ 2πi·ℤ` for `x` off
  the boundary (four exp-identities, telescoping corners);
* **`boundaryIntegral_inv_sub_interior`** — for
  `x = a + s·ω₁ + r·ω₂`, `s, r ∈ (0,1)`:
  `∮_{∂Π} (z−x)⁻¹ dz = (sign of ω₁×ω₂)·2πi`, **at every interior point
  simultaneously**. The planned keystone-2 (local constancy) and
  keystone-3 (`Complex.log` evaluation) were never needed: the
  imaginary part is a sum of four swept angles
  (`Im(α/(tα+β)) = c/|tα+β|²`, `c ∈ {rD, (1−s)D, (1−r)D, sD}`), each an
  arctan difference that is sign-definite and `< π` in magnitude, so
  membership in `2πi·ℤ` pins the value to `±2πi`. Pure real analysis —
  no branch cuts, no connectivity.

## The wall (piece 3) at maximum resolution

`I(a) = 2πi ∑ ord·x̃` is a **parallelogram residue theorem**, and the
toolbox has a hole exactly here:

* mathlib (pin `8e3c989`) has **rectangle** Cauchy only
  (`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
  — axis-aligned, and the off-countable version requires continuity on
  the closure, so it cannot see poles), the **disk/circle** Cauchy
  formula, and **no winding numbers, no `Residue.lean`, no polygon/
  triangle Cauchy, no argument principle** (checked 2026-06-09).
* the repo's residue theorem went via **topological degree**, not
  contours; `CircleResidue.lean`/`LogDerivLaurent*.lean` are chart-circle
  local tools; `GlobalResidueSum.lean` is hypothesis-scaffolding from the
  superseded Stokes route. No plane-contour assembly exists in tree.

Standard reduction of piece 3 that needs no new Cauchy theory except one
keystone: subtract principal parts. Near a divisor point `x̃`,
`z·g(z) − ord_{x̃}·x̃/(z − x̃)` is analytic (LogDerivLaurent-style local
form; `g` has simple poles with integer residues `ord`). So with
`H := z·g − ∑_{x̃ near Π̄} ord·x̃/(z − x̃)` analytic on a convex open
`U ⊇ Π̄`:

* `∮_{∂Π} H = 0` — **no Cauchy needed**: `H` analytic on convex `U` has
  a primitive (mathlib has primitives on convex/star-shaped sets for
  `DifferentiableOn`; check `Complex.` primitive lemmas at the pin), and
  a primitive telescopes to `0` around the closed polygon by per-side
  FTC.
* `∮_{∂Π} (z−x̃)ⁿ dz = 0` for `n ≤ −2` — same telescoping (global
  primitive on `ℂ \ {x̃}`).
* ~~**KEYSTONE**~~: `∮_{∂Π(a)} dz/(z − x̃) = ±2πi` for `x̃ ∈ int Π` —
  **DONE 2026-06-10** (`boundaryIntegral_inv_sub_interior`, see above;
  the arctan/swept-angle route replaced the planned `Complex.log`
  branch bookkeeping entirely).

Alternative routes considered and rejected 2026-06-09: (a) deriving
forward Abel from the converse machinery is circular (the chord's third
zero used forward Abel); (b) the addition-theorem route needs the same
transcendental input; (c) Vieta on the cubic ODE constrains `℘`-values,
not point sums mod `L`; (d) torus-side residue-of-1-form theorem is not
in tree and `z·g dz` does not descend anyway (`z` is not periodic).

## Suggested chip order (updated 2026-06-10; engine + keystone done)

Remaining, in order:

1. **Principal-part subtraction** (the rest of piece 3). Infrastructure
   now DONE (2026-06-10):
   * `Analysis/ParallelogramCauchy.lean` —
     `boundaryIntegral_eq_zero_of_primitive` (FTC telescoping; the
     chain rule routed through ℂ + `comp_ofReal`, dodging the
     `IsScalarTower ℝ ℂ ℂ` diamond) and
     `boundaryIntegral_eq_zero_of_differentiableOn_ball` (via mathlib's
     `DifferentiableOn.isExactOn_ball` Morera machinery — primitives on
     disks suffice; subtract ALL principal parts inside one big ball
     `⊇ Π̄`).
   * `Analysis/ParallelogramWindingExterior.lean` —
     `boundaryIntegral_inv_sub_exterior`: separated-exterior winding
     vanishes (rotated-log primitive on the separating half-plane).
   * ✅ (i) DONE 2026-06-10 — `Analysis/LogDerivPrincipalPart.lean`:
     local Laurent form; `z·F'/F − n·x₀/(z−x₀)` agrees near `x₀` with
     an analytic function (`mul_logDeriv_sub_principalPart_eventuallyEq`).
   * ✅ (iii) DONE 2026-06-10 — `Analysis/ParallelogramResidue.lean`:
     **`boundaryIntegral_eq_sum_winding`** — given decomposition data
     `f = H + ∑_{x ∈ P} coeff x/(z−x)` on a ball ⊇ the four sides, `H`
     differentiable on the ball, poles off the boundary:
     `∮_{∂Π} f = ∑ coeff x · ∮_{∂Π} (z−x)⁻¹` (per-segment congruence +
     `integral_add`/`integral_finset_sum`/`integral_const_mul` +
     disk Cauchy kills `H`).
   * ✅ (iv) DONE 2026-06-10 — `Analysis/ParallelogramCoordinates.lean`:
     Cramer coordinates `coordS`/`coordR` (`z = a + s·ω₁ + r·ω₂`),
     reconstruction `interiorPt_coords`, side coordinate values (all in
     `[0,1]`), and the complete winding dichotomy in coordinates:
     **`boundaryIntegral_inv_sub_of_coord_interior`** (coords in
     `(0,1)²` ⟹ `±2πi`) and
     **`boundaryIntegral_inv_sub_of_coord_exterior`** (either coord
     outside `[0,1]` ⟹ `0`, via the coordinate separating functional
     `sepFunctional β = I·conj β` with `Re(u·sepFunctional β) =
     latticeCross u β`, all four cases through one `exterior_core`).
   Remaining for piece 3: (ii) GLUING — produce the decomposition data
   for the actual Abel integrand `f = z·g`: removable-singularity
   extension of `H := z·g − ∑ n_j·x̃_j/(z−x̃_j)` at the finitely many
   `x̃_j` in the big ball (mathlib `Complex.RemovableSingularity` +
   (i)'s local form; note the cross-terms `∑_{k≠j} n_k·x̃_k/(z−x̃_k)`
   are analytic at `x̃_j`, so (i) gives exactly the removability of
   `H` at each `x̃_j`), giving `DifferentiableOn H̃ ball`. Then
   `I(a) = ε·2πi·∑ ord·x̃` follows by feeding (ii) into (iii) and
   evaluating each winding with (iv) (poles off `∂Π` by regular
   position ⟹ coords off the boundary of `[0,1]²`; interior ⟹ `±2πi`,
   exterior ⟹ `0`). ⚠️ note the dichotomy's exterior case needs the
   pole's coords outside `[0,1]` — for a regular-position `a` the
   poles have coords off `∂[0,1]²`, which splits exactly into the
   interior/exterior cases of (iv).
2. **Regular position** (piece 4).
3. **Pairing algebra** (piece 1) + applying the winding engine to
   `Δ_h, Δ_v` (chain rule for `F ∘ side`, using
   `meromorphic_liftedFun` + analyticity off the divisor).
4. **Assembly** (piece 5) ⟹ `TLDivSumHypothesis L` ⟹ (with the
   2026-06-09 chord arc) the full T_L C3 closure from zero named
   hypotheses.
