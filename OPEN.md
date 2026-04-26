# OPEN

The 12 `sorry`s in `JacobianChallenge/Basic.lean`, mapped to Buzzard's challenge
items. Mark each as **CLOSED** with a section reference when discharged. Do
not regenerate this list from context — query this file.

## Definitions (data)

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | OPEN | Anti-hack pair with item 7. Likely route: define via `Module.finrank ℂ` of holomorphic 1-forms once that infrastructure exists, or via `H¹` rank. |
| 2 | `Jacobian X : Type u` | OPEN | Anti-hack pair with item 9. Two main candidate constructions: (a) `Pic⁰(X) = Div⁰(X) / PrincDiv(X)`; (b) `(Fin (genus X) → ℂ) ⧸ PeriodLattice X`. |
| 3 | `instance : AddCommGroup (Jacobian X)` | OPEN | Falls out of (2) in either construction. |
| 4 | `instance : TopologicalSpace (Jacobian X)` | OPEN | Quotient topology under either construction. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | OPEN | Charts inherited from `ℂᵍ`. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | OPEN | Abel–Jacobi map. Under (a): `P ↦ [P] - [base]`. Under (b): integration of the period basis along a base path. |
| 7 | `Jacobian.pushforward f hf` | OPEN | Functorial covariant map. |
| 8 | `Jacobian.pullback f hf` | OPEN | Functorial contravariant map; zero on constant `f`. |
| 9 | `ContMDiff.degree f hf : ℕ` | OPEN | Topological degree of proper holomorphic maps; 0 for constant. |

## Theorems (Prop)

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | OPEN |  |
| 11 | `instance : CompactSpace (Jacobian X)` | OPEN |  |
| 12 | `instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X)` | OPEN |  |
| 13 | `instance : LieAddGroup ... (Jacobian X)` | OPEN |  |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | OPEN | Genus 0 ↔ `X ≃ₜ S²`. Forces a real construction of `genus`. |
| 15 | `ofCurve_self : ofCurve P P = 0` | OPEN |  |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | OPEN | `ofCurve P` injective when `0 < genus X`. Forces the Jacobian to distinguish points. |
| 17 | `Jacobian.ofCurve_contMDiff` | OPEN | `ofCurve` is holomorphic. |
| 18 | `Jacobian.pushforward_contMDiff` | OPEN |  |
| 19 | `pushforward_id_apply` | OPEN | Functoriality (identity). |
| 20 | `pushforward_comp_apply` | OPEN | Functoriality (composition). |
| 21 | `Jacobian.pullback_contMDiff` | OPEN |  |
| 22 | `pullback_id_apply` | OPEN |  |
| 23 | `pullback_comp_apply` | OPEN |  |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | OPEN | The headline degree formula. |

## Mathlib-prerequisite candidates (likely needed before items above)

These are *not* part of the challenge directly, but the constructions for
items 1, 2, 6, 9 will need infrastructure not in mathlib at the pinned commit.
Each is plausibly a standalone mathlib PR.

- `Divisor` on a complex manifold and `principalDivisor` of a meromorphic function
- `OrderOfVanishing` for meromorphic functions at a point
- `HolomorphicOneForm` as a complex vector space; finite-dimensionality on compact Riemann surface
- The period lattice as a `Submodule ℤ` of the dual of `HolomorphicOneForm`
- Topological degree of proper holomorphic maps between Riemann surfaces (currently mathlib only has degree for `S^n → S^n`)
- Connection between `ChartedSpace ℂ X` + `IsManifold 𝓘(ℂ) ω X` and the classical Riemann-surface API in textbooks (Forster, Miranda, Griffiths-Harris)

Track each prereq as it is identified, and prefer landing it as a mathlib PR
rather than carrying a private copy; the PR review process is the validation
mechanism this repo otherwise lacks.
