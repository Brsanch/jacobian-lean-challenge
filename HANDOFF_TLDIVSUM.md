# `TLDivSumHypothesis L` — handoff (the last named hypothesis for the T_L C3 closure)

**Status 2026-06-10: ✅ CLOSED — `TLDivSumHypothesis L` is a THEOREM.**
`Manifold/TLDivSumAssembly.lean`:
* **`tlDivSumHypothesis_holds : TLDivSumHypothesis L`** — Abel's
  theorem on elliptic functions, by the two-evaluation contour
  argument below, no `sorry`, no `axiom`, no named hypotheses;
* **`nonempty_C3FullInputExtSymp_complexTorus_unconditional`** — the
  full T_L C3 input from ZERO named hypotheses (only the
  `PeriodLatticeSymplecticBundle` data argument remains, as in the
  conditional version).
The named-hypothesis pile for T_L is now EMPTY. Everything below is
the historical plan + per-piece inventory of the proof, kept for
maintenance.

**Status 2026-06-09 (historical)**: OPEN. This is now the ONLY named hypothesis between
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
   * ✅ (ii) DONE 2026-06-10 — `Analysis/AbelIntegrandDecomposition.lean`:
     **`abelIntegrand_decomposition`** — for `F` meromorphic of finite
     order `n x` at each point of a finite `Z` and analytic nonvanishing
     elsewhere on a ball, `z·F′/F = H + ∑_{x∈Z} (n x·x)/(z−x)` with `H`
     differentiable on the whole ball. Construction: `glueAcross`
     (punctured limits across `Z`); at each `x ∈ Z` the (i) local form
     plus analyticity of the cross terms gives the removable extension —
     no `Complex.RemovableSingularity` import needed, the eventual
     equality + `limUnder` + `AnalyticAt.congr` suffice.
   **Piece 3 ingredients are now ALL in tree.** The remaining piece-3
   work is pure assembly in the consumer: choose the big ball ⊇ Π̄,
   instantiate `abelIntegrand_decomposition` (Z = divisor-support
   translates in the ball, n = orders via
   `liftedOrderCorrespondence_holds`), feed into
   `boundaryIntegral_eq_sum_winding`, and evaluate each winding with
   the (iv) dichotomy: regular-position `a` puts every pole's coords
   off `∂[0,1]²`, splitting into interior (`±2πi`) and exterior (`0`)
   cases. Result: `I(a) = ε·2πi·∑_{x̃ interior} ord·x̃`.
2. ✅ **Regular position** (piece 4) DONE 2026-06-10 —
   `Analysis/ParallelogramRegularPosition.lean`:
   **`exists_regular_position`** — for every finite `P` there is a base
   point `a` with both Cramer coordinates of every lattice translate
   `p + m₁·ω₁ + m₂·ω₂` off `{0,1}` (bad set = countable union of
   `s_p + ℤ` lines in `(σ,ρ)`-coordinates, `ℝ` uncountable via
   `Cardinal.not_countable_real`). Plus the assembly interface:
   `sideX_ne_of_coord...` (the contour avoids such points) and
   **`boundaryIntegral_inv_sub_of_coord_ne`** — the single winding
   evaluator (`±2πi` if both coords in `(0,1)`, else `0`).
3. ✅ **Pairing algebra** (piece 1, core) DONE 2026-06-10 —
   `Analysis/ParallelogramPairing.lean`:
   **`boundaryIntegral_mul_eq_pairing`** — for doubly periodic `g`
   continuous along the two generator sides,
   `∮_{∂Π(a)} z·g(z) dz = ω₁·Δ_v − ω₂·Δ_h` with
   `Δ_h = ∫₀¹ g(a+t·ω₁)·ω₁ dt`, `Δ_v = ∫₀¹ g(a+t·ω₂)·ω₂ dt`
   (opposite-side cancellation: reversed-side reparametrization
   `integral_comp_sub_left` + periodicity). ⚠️ Lean gotchas hit here,
   for future chips: `∫ t in 0..1, body - X` parses `- X` INTO the
   integral body (parenthesize products of integrals!); `rw ←` with
   `r * ∫ f` / `-∫ f` higher-order patterns fails — state concrete
   `have`s via term-mode `integral_const_mul`/`integral_neg` instead;
   `Continuous (fun t => a + t • ω₁)` needs the `Complex.real_smul`
   reroute (`ContinuousSMul ℝ ℂ` synth fails).
   ✅ Winding-engine application DONE 2026-06-10 —
   `Analysis/PeriodSideWinding.lean`:
   `periodSide_logDeriv_integral_mem` (chain rule through ℂ +
   `comp_ofReal` feeds `integral_logDeriv_closed_mem`:
   `∫₀¹ (F′/F)(a+t·ω)·ω dt ∈ 2πi·ℤ` for `F` analytic nonvanishing on
   the side with `F(a+ω)=F(a)`), `deriv_eq_of_periodic`, and
   **`boundaryIntegral_mul_logDeriv_mem`** — for `F` doubly periodic,
   analytic nonvanishing along both generator sides:
   `∮_{∂Π(a)} z·(F′/F) dz = 2πi·(k₁ω₁ + k₂ω₂)`, `k₁ k₂ : ℤ`. **The
   pairing-side evaluation of `I(a)` is complete.**
4. **Assembly** (piece 5) ⟹ `TLDivSumHypothesis L` ⟹ (with the
   2026-06-09 chord arc) the full T_L C3 closure from zero named
   hypotheses. ALL analysis ingredients are now in tree
   (`ParallelogramResidue`, `ParallelogramCoordinates`,
   `AbelIntegrandDecomposition`, `ParallelogramRegularPosition`,
   `ParallelogramPairing`, `PeriodSideWinding` + the 2026-06-10
   keystones), plus the first torus-side glue
   (`Manifold/LiftedFunRegularPoints.lean`, 2026-06-10:
   `analyticAt_nonzero_of_meromorphicOrderAt_eq_zero` — order 0 +
   continuity ⟹ honestly analytic nonvanishing including the value;
   `liftedFun_analyticAt_nonzero_of_order_zero` — the lift is analytic
   nonvanishing at every `z` with `mmeromorphicOrderAt f (mkQ z) = 0`,
   via `liftedOrderCorrespondence_holds` + `regular_continuousAt` +
   `isOpenQuotientMap_mkQ`), and the second
   (`Manifold/MkQPreimageFinite.lean`, 2026-06-10:
   **`finite_mkQ_preimage_inter_isBounded`** — the `mkQ`-preimage of a
   finite class set meets every bounded subset of ℂ finitely; per
   class the fiber is `x.out + L` and
   `Metric.finite_isBounded_inter_isClosed` + the
   `change`-to-`L.toAddSubgroup` trick from mathlib's ZLattice file
   finishes — this builds the finite `Z` for the decomposition); what
   remains is ONE consumer file on the torus side.
   **Interface inventory verified 2026-06-10 (all in tree, ready):**
   * (c) basis bridge: `basisFin2OfL_isZBasisOfL : IsZBasisOfL L lam₁
     lam₂` (`IsZBasisOfL` = `∀ z ∈ L, ∃ m₁ m₂ : ℤ, z = m₁•lam₁ +
     m₂•lam₂`, `ComplexTorusSmoothHurewiczFromBasis.lean:57`), periods
     `lam₁/₂_complexTorus` with `_mem` lemmas;
   * orientation: `latticeCross_ne_zero_of_linearIndependent`
     (`Analysis/LatticeCrossNeZero.lean`, 2026-06-10) +
     `basisFin2OfL_realLinearIndependent` give the `hD` consumed by
     the whole parallelogram toolbox;
   * (a) off-support ⟹ order 0: `mem_supportFinset` (`Divisor.lean:83`,
     `x ∈ D.supportFinset ↔ D x ≠ 0`) + the divisor's value is
     `orderFun = (mmeromorphicOrderAt …).untop₀`
     (`MeromorphicDivisor.lean:83`) + `orderFun_eq_zero_iff`
     (with `f.nonvanishing_germ`) — two-line connectors;
   * order ⟹ regular: `liftedFun_analyticAt_nonzero_of_order_zero`;
   * orders on lifts: `liftedOrderCorrespondence_holds`,
     `meromorphic_liftedFun`, `liftedFun_periodic`, `mkQ_out`;
   * finite `Z`: `finite_mkQ_preimage_inter_isBounded`.
   **Remaining work in the assembly file:** (d) the complete-set-of-
   representatives count (each `p ∈ supp`-lift has exactly one
   translate with coords in `(0,1)²` — via `coordS/R_translate`:
   `s_p + m₁ − σ ∈ (0,1)` has exactly one integer solution `m₁` given
   coords avoid `{0,1}`), the `Finset` sum re-indexing (interior
   translates ↔ supportFinset), and the equation chain below:
   lift `f` to `F` via `liftedOrderCorrespondence` /
   `meromorphic_liftedFun`, collect the divisor-support lifts (finite;
   lattice translates within a big ball ⊇ Π̄ — needs L-discreteness
   for finiteness of `Z`), choose regular-position `a`
   (`exists_regular_position` — bridge L-elements to `(m₁,m₂) : ℤ²`
   via `basisFin2OfL` repr), then equate the two evaluations of
   `I(a) = ∮ z·(F′/F)`:
   * residue side = `abelIntegrand_decomposition` →
     `boundaryIntegral_eq_sum_winding` →
     `boundaryIntegral_inv_sub_of_coord_ne` per pole:
     `I(a) = ε·2πi·∑_{x̃ interior} ord·x̃`;
   * pairing side = `boundaryIntegral_mul_logDeriv_mem`:
     `I(a) = 2πi·(k₁ω₁ + k₂ω₂) ∈ 2πi·L`.
   Divide by `±2πi` ⟹ `∑_{interior} ord·x̃ ∈ L`; interior translates
   form a complete set of representatives of `supp(div f)` (per-base-
   point uniqueness: exactly one `(m₁,m₂)` puts `p`'s translate in
   `Π(a)°` — coordS/R_translate make this explicit:
   `s_p + m₁ − σ ∈ (0,1)` has exactly one integer solution since the
   coords avoid `{0,1}`) ⟹ `evalSum (div f) = 0` in `ℂ ⧸ L` =
   `TLDivSumHypothesis L`.
