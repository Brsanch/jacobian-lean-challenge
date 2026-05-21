# mrdouglasny axiom inventory → Bryan tree status

Cross-reference between `mrdouglasny/jacobian-challenge`'s axiom-based
closure of Kevin Buzzard's Jacobian Challenge and the corresponding
Bryan-tree atoms / named hypotheses. The mrdouglasny repo closed all 24
items via 14 named `axiom`s; Bryan's no-axiom path needs each of those
14 statements actually *proved* in tree, or sidestepped by a structural
choice (e.g., a different `Jacobian X` definition).

This map is the **single source of truth** for the multi-session arc
closing the remaining open classical content.

**Source:** [mrdouglasny/jacobian-challenge](https://github.com/mrdouglasny/jacobian-challenge), commit as of 2026-05-12.

## Status legend

- ✅ **Discharged** — Bryan tree has an unconditional theorem matching
  the axiom's statement.
- 🟡 **Partial** — Bryan tree has the statement at specific genera /
  manifolds but not in full generality.
- ❌ **Open** — no Bryan-tree progress yet; needs multi-session content.
- 🔀 **Sidestepped** — Bryan's structural choice avoids needing this.

## The 14 axioms

| # | mrdouglasny axiom | Bryan-tree atom(s) | Status | Chip(s) |
|---|---|---|---|---|
| 1 | `AX_AnalyticCycleBasis` (symplectic ℤ-basis of H₁) | `Nonempty (SurfaceClassificationData X)` = `AnalyticCycleBasisHypothesis X` | 🟡 RS ✅, T_L ✅, general ❌ | chips 1, 2, 31 |
| 2 | `AX_PeriodLattice` (period image is full IsZLattice) | `periodLatticeImage_isZLattice_of_bundle` + `..._discreteTopology_of_bundle` | 🟡 — discharged when `PeriodLatticeSymplecticBundle` exists (RS ✅, T_L ✅); reduces to axioms #1 + #3 at general X | chip D, chip 27 |
| 3 | `AX_RiemannBilinear` (τ ∈ SiegelUpperHalfSpace) | `RiemannFirstBilinearRelation` (RFBR, chip 9) + `RiemannSecondRelationPositivity` (RSRP, chip 18) on the standard symplectic J | 🟡 g=0 ✅, g=1 ✅ (chips 24, 25), g≥2 reduces to strict-upper-Q + matrix-PD via chips 16/20p | chips 9-25 |
| 4 | `AX_AbelTheorem` (ker(Abel-Jacobi : Div→Jac) = PrincDiv) | `EvalSumAbelHypothesis X`, `TLDivSumHypothesis L` | ❌ open even on T_L | session 2026-05-19 (AbelHypothesis) |
| 5 | `AX_Uniformization0` (g=0 ⟺ X ≃ₜ S²) | `genus_eq_zero_iff_homeo` (Basic.lean item 14); architectural via `genus_eq_zero_iff_homeo_from_all_conditionals` | ❌ open; handled in `feat/item14-classical-content` worktree | item-14 worktree |
| 6 | `AX_BranchLocus` (proper + discrete fibers + degree) | `ramificationSumEqualsDegree_holds_unconditional`, `degreeFiber_eq_card_of_regular_witness` | ✅ unconditional in tree | (closed pre-chip-1) |
| 7 | `AX_RiemannRoch` (H⁰(D) − H¹(D) = deg D + 1 − g) | (no Bryan analog; sheaf cohomology not in mathlib) | ❌ open | none |
| 8 | `AX_SerreDuality` (H¹(𝒪(D)) ≃ H⁰(Ω(K−D))*) | (no Bryan analog; sheaf cohomology not in mathlib) | ❌ open | none |
| 9 | `AX_IntersectionForm` (alternating non-deg pairing on H₁) | (no Bryan analog; Poincaré duality not in mathlib at pin) | ❌ open; substituted indirectly via the bilinear period matrix at chip 23/24 RSRP | none |
| 10 | `AX_HyperellipticLiouville` (Liouville + hyperelliptic ID) | (no Bryan analog) | ❌ open | none |
| 11 | `AX_PluckerFormula` (plane-curve genus formula) | (no Bryan analog) | ❌ open | none |
| 12 | `AX_pathIntegral_local_antiderivative` (FTC for path integral) | `pathPrimitive ↔ chartLocalPrimitive` bridge + `EventuallyEq` transfer; per-chart FTC chain | 🟡 partial; in `feat/item14-classical-content` worktree | item-14 worktree |
| 13 | `AX_pullbackOneForm`, `AX_pushforward_AmbientLinear` (differential functoriality) | `PullbackHolomorphicOneForm.lean`, `HolomorphicOneFormPullbackLinearMap.lean` | 🟡 partial; pullback in tree, pushforward via dual map | various |
| 14 | Various small mechanical axioms (`AX_pushforward_id_apply`, `AX_pullback_comp_apply`, etc.) | Bryan's `pushforward_id_apply`, `pullback_comp_apply`, etc. in `Basic.lean` (already STRICT-CLOSED items 19, 20, 22, 23, 24) | ✅ | (closed pre-chip-1) |

## Discharge dependency graph (general X)

```
items 5/11/12/13 (Jacobian X manifold structure)
   └── HasJacobianAnalyticStructure X
        └── HasC3FullClassicalContent X
             ├── SurfaceClassificationData X            ← AX #1 (general open)
             ├── RiemannFirstBilinearRelation           ← AX #3 (g≥2 open)
             └── RiemannSecondRelationPositivity        ← AX #3 (g≥2 open)
        └── PeriodLatticeSymplecticBundle X             ← AX #2 (general = #1 + #3)

items 17/18/21 (ofCurve/pushforward/pullback contMDiff)
   └── item 5 + path-integral FTC                       ← AX #12 (general open)
   └── differential pullback/pushforward functoriality  ← AX #13 (partial)

item 14 (genus_eq_zero_iff_homeo)
   └── Uniformization at g=0                            ← AX #5 (open)
        └── one of:
            - Riemann-Roch + Serre duality at g=0       ← AX #7, AX #8
            - Hilbert/elliptic-PDE/harmonic-differentials route
            - Hodge theory at g=0

item 16 (ofCurve_inj)
   └── ALREADY CLOSED in tree (Basic.lean line 143)

item 24 (pushforward_pullback = degree)
   └── ALREADY CLOSED in tree via `Pic0.pushforward_pullbackWeighted`
```

## Bryan-specific structural choice

mrdouglasny uses `Jacobian X := ComplexTorus(period_lattice_of_X)`,
which makes items 5/11/12/13 flow *automatically* from in-tree
`ComplexTorus` mathlib infrastructure once the period lattice is
established. The hard content is then pushed into the Abel-Jacobi map
proofs (`AX_AbelTheorem`, `AX_pathIntegral_local_antiderivative`).

Bryan's tree uses `Jacobian X := Pic⁰ X` (Basic.lean item 2
STRICT-CLOSED). This choice puts items 5/11/12/13 *behind* the
identification `Pic⁰ X ≃ ComplexTorus(period_lattice_of_X)`, which
requires both Abel's theorem (kernel of Abel-Jacobi = PrincDiv) AND
Jacobi inversion (Abel-Jacobi surjective).

So Bryan's path is, if anything, *harder* than mrdouglasny's for items
5/11/12/13. The trade-off: Bryan's `Pic⁰` is the
algebraically-correct definition (matches the actual mathematical
object); mrdouglasny's `ComplexTorus`-based definition is the
manifold-structurally-correct definition (matches the smooth structure
on `Jac(X)`).

To close items 5/11/12/13 unconditionally on Bryan's `Pic⁰` path:
1. Axiom #1 unconditional (smooth Hurewicz at general genus).
2. Axiom #3 unconditional (RFBR + RSRP at general genus).
3. Axiom #4 unconditional (Abel's theorem).
4. Plus: Jacobi inversion = Abel-Jacobi surjective (mrdouglasny notes
   this is implicit in their `Jacobian.Construction.lean` bridge but
   not separately axiomatized).
5. ⇒ Establish `Pic⁰ X ≃ AnalyticJacobian X` smooth diffeomorphism.

The Abel + Jacobi-inversion content is the **smallest-grained
remaining gap** at T_L specifically (see memory entry 2026-05-19 on
"AbelHypothesis + JacobiInversion = two open classical inputs on T_L").

## Multi-session arc plan

Discharge order, in **priority by impact-on-items**:

1. **AX #3 at genus ≥ 2** — closes the g≥2 piece of `HasC3FullClassicalContent X`.
2. **AX #1 at general genus** — closes smooth Hurewicz universally. Route (P3) Morse most tractable.
3. **AX #4 (Abel) on T_L** — `TLDivSumHypothesis` discharge via elliptic-function residue theory.
4. **Jacobi inversion on T_L** — Weierstrass-σ existence.
5. **AX #5 (Uniformization-at-g=0)** — item-14 worktree.
6. **AX #7/#8 (Riemann-Roch / Serre duality)** — sheaf-cohomology multi-month subproject.

After (1)-(2)-(3)-(4) on T_L: every X biholomorphic to T_L has unconditional C3 umbrella + Abel-Jacobi smooth diffeomorphism. Combined with chip 29's transport from RS, the unconditional C3 umbrella class fires on the union {X ≃ RS} ∪ {X ≃ T_L}.

The general-X closure (items 5/11/12/13 *for arbitrary X*) requires either (a) uniformization at every genus (gold standard, very far away in mathlib) or (b) discharging AX #1 + AX #3 + AX #4 at general X directly (still multi-month each).

The realistic Bryan-no-axiom completion timeline: **multi-year** for full general-X discharge. Single-X closure (RS, T_L, X ≃ RS) is feasible in months.
