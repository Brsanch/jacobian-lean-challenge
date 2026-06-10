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
| 2 | Winding integrality: `Δ_h, Δ_v ∈ 2πi·ℤ` | self-contained exp-trick (~200–400 LOC): `h(t) := exp(-∫₀ᵗ q)·F(γ t)` has `h' = 0`, so `exp(∫₀¹ q) = F(γ 1)/F(γ 0) = 1` (periodicity) ⟹ integral `∈ 2πi ℤ` (`Complex.exp_eq_one_iff`). Needs continuity of the integrand on the side (piece 4) + FTC for parameterized complex integrals |
| 3 | **Residue side: `I(a) = 2πi·∑_{x̃ ∈ Π} ord_{x̃}(F)·x̃`** | ⚠️ **THE WALL** — see below |
| 4 | Regular position: choose `a` with `∂Π(a)` avoiding the zero/pole set of `F` (= `L`-translates of the finite `supp(div f)` lifted) | countable-bad-set avoidance (~200–400 LOC); the bad `a`-set per side is a finite union of `L`-translate line families; a Baire/measure or explicit-perturbation argument |
| 5 | Bookkeeping: zeros in `Π` are a complete set of representatives; `∑ ord·x̃ mod L` = `evalSum (div f)`; assemble 1+2+3 ⟹ `evalSum ∈ L`-image = 0 | mechanical given 0 and 3 (~200–400 LOC) |

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
* **KEYSTONE (the actual open problem)**:
  `∮_{∂Π(a)} dz/(z − x̃) = 2πi` for `x̃ ∈ int Π`. Candidate proof, all
  pieces individually plausible but none in mathlib:
  1. integrality: exp-trick on the closed 4-segment path (`h := z − x̃`
     is a closed curve in `ℂ*`) ⟹ value `∈ 2πi ℤ`;
  2. local constancy in `x̃` on `int Π` (parametric continuity of the 4
     interval integrals + ℤ-valued + connected ⟹ constant);
  3. one explicit evaluation, e.g. at the center
     `c = a + (ω₁+ω₂)/2`: each side-integral is
     `∫ ds/(s − ζ)` with `Im ζ ≠ 0` along a real segment, whose
     primitive is `Complex.log (s − ζ)` (valid: the argument never meets
     the branch cut since `Im` is constant ≠ 0) — then a
     `Complex.log`-arithmetic computation sums the four log differences
     to `2πi`. The branch bookkeeping here is the fiddliest single step
     of the whole arc.

Alternative routes considered and rejected 2026-06-09: (a) deriving
forward Abel from the converse machinery is circular (the chord's third
zero used forward Abel); (b) the addition-theorem route needs the same
transcendental input; (c) Vieta on the cubic ODE constrains `℘`-values,
not point sums mod `L`; (d) torus-side residue-of-1-form theorem is not
in tree and `z·g dz` does not descend anyway (`z` is not periodic).

## Suggested chip order

2 (exp-trick winding, self-contained) → keystone-1 (integrality, same
machinery) → keystone-3 (explicit center evaluation) → keystone-2
(parametric continuity) → 4 (regular position) → 1 (pairing) → 5
(assembly). The exp-trick machinery is shared by chip 2 and keystone-1;
build it once as a lemma about `∫₀¹ (deriv (F ∘ γ))/(F ∘ γ)` for `γ`
affine with `F ∘ γ` nonvanishing and `F (γ 0) = F (γ 1)`.
