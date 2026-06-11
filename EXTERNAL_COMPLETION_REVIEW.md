# External completion of the challenge — review record (2026-06-11)

**The Buzzard Jacobians challenge (gist v0.4) has been completed externally** by
[rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude): ~111k Lean
LOC across 309 files, built in 20 working days (2026-04-19 → 2026-06-11) by
Claude (Opus 4.7 → Opus 4.8 → Fable 5) with light human scoping by R. Kirov,
who does not know the mathematics and has not reviewed the content. This file
records the independent statement-level review performed from this repo on the
day of completion (commit `88b113e`).

~3.3k LOC of this repo's degree/fibre/Hurwitz machinery (MIT) survives in
their final tree (22 files under `Jacobians/Discharge/Manifold/`, credited),
including `degreeFiber`, which implements their `ContMDiff.degree`.

## Review scope and method

Statements and definitions only — the kernel already checked the proofs; the
open question for any AI formalization is *misformalization* (definitions or
statements subtly different from the classical meaning). Method: trace every
spec-facing declaration from the conformance file to its definitional leaves;
sweep for every kernel escape hatch; check against the hollow-proof patterns
known from the SQG audit (vacuous `True`-valued fields, named-hypothesis
deferral, rigged definitions).

## Findings — no misformalization found

| Check | Result |
|---|---|
| Spec fidelity | `Jacobian_challenge.lean` **byte-identical** to the live gist (fetched and diffed 2026-06-11) |
| Conformance | `ChallengeConformance.lean` restates all 24 spec items verbatim and discharges each by their declarations; compiles in CI |
| Escape hatches | No `sorry` outside the spec file; no custom `axiom`; no `native_decide`/`ofReduceBool`; `unsafe`/`implemented_by` confined to a non-proof runtime shim |
| Hollow patterns | Absent. One `True`-valued theorem, explicitly named `_unused` |
| CI | Green on HEAD; `lake build` uses `globs := andSubmodules` (orphan modules cannot hide); axiom audit in CI |
| `genus` | `Module.finrank ℂ (HolomorphicOneForms X)`, forms = `ContMDiffSection`s (ω) of `Hom(TX, trivial ℂ)` — the genuine dim H⁰(Ω). Finite-dimensionality is forced honest by `genus_eq_zero_iff_homeo` (junk `finrank = 0` would require proving a positive-genus surface ≃ₜ S²) and is proven via their Montel tower |
| `Jacobian` | `ULift` of `(Fin (genus X) → ℂ) ⧸ truePeriodLattice X`; lattice = ℤ-span of period vectors of closed loops; discreteness + `IsZLattice ℝ` (full rank) **proven** — the instances (compactness, T2, charted, Lie group) are genuine, not rigged |
| `ofCurve` | `Q ↦ [∫_{P→Q} ωᵢ]` for a basis of H⁰(Ω), path from a *proven* smooth-path existence theorem (`exists_smoothPath_family`; `Classical.choice` extraction with basepoint-change proven). `lineIntegral` = classical `∫ f(z(t)) z′(t) dt` with form coefficient and `pathSpeed` in the same canonical chart-at-point frame (coherent) |
| `ContMDiff.degree` | explicit `if IsConstantMap f then 0 else` regular-fibre cardinality with a regularity *certificate* baked into the witness (`RegularValueWitnessReg`); witness existence for non-constant maps proven unconditionally; well-definedness + positivity proven. Matches the spec convention exactly |
| `pushforward`/`pullback` | genuine matrix actions on period coordinates descended through the quotient with **proven** lattice preservation. Notably, the pullback (`ambientPullbackJac` = trace transpose) *replaced* an earlier misformalized version whose preservation rested on a false trace identity — their audits caught it |
| Anti-hack design | Buzzard's spec itself kernel-forces most cheats out: `CompactSpace` + `ChartedSpace (Fin (genus X) → ℂ)` force a full-rank lattice; `ofCurve_contMDiff` in the complex model forces holomorphic Abel–Jacobi; `ofCurve_inj` forces nondegenerate periods (Abel); `genus_eq_zero_iff_homeo` forces honest finiteness of H⁰(Ω) |

**Cosmetic issues only:** several docstrings are stale, referencing
intermediate-state gaps that were later closed (`HasSmoothPaths` described as
an "axiom" — the class no longer exists; a "sorried" `finrank_…_eq_genus` —
now `rfl`-trivial by their genus definition; an "axiomatized"
`HasAmbientDegreeIdentity` — retired; "the single remaining gap
`lineIntegral_pullback`" — closed). The root `AxiomCheck.lean` header comment
predates the endgame; the final headliner audit is
`scripts/axiom_check_final.lean`.

## Honest limits of this review

- Proof *content* (111k LOC) was not read; Lean's kernel is the guarantee
  there. Statement faithfulness was traced to definitional leaves for every
  spec-facing item, but a deeper mechanized check (e.g. the in-chart
  coefficient correspondence for `ContMDiffSection` vs. classical holomorphic
  coefficients) was not re-derived from scratch.
- The build evidence is their green CI + a full source-level escape-hatch
  sweep of the clone; the tree was not rebuilt on this machine.
- Neither this review nor anything else to date constitutes review by a
  research mathematician. Buzzard's own review of the submission is the
  appropriate final arbiter.

## Consequence for this repo

This repo's remaining open items (the two classical walls: RR/Serre via the
Arc 1 L²-Hodge-lite route, and the period-lattice/Abel chain) are **closed in
the external tree** by exactly the classical routes this repo's docs priced
(Miranda Laurent-tail RR + Serre duality; Forster §19–21 dissection-free
Abel/period-lattice; monodromy genus-0⟺sphere). Arc 1 is therefore **frozen**:
re-proving these walls in-repo would duplicate a verified artifact.

This repo remains the source of the ported degree/fibre machinery and a
14/24-strict-closed independent development with its own audit trail.
Possible future work, if any: mathlib upstreaming of either tree's towers
(their repo currently has **no license**; the author publicly offered the
work for continuation — a license request is the first step), or an
adversarial expert review of the external tree's analytic core.
