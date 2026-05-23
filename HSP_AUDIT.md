# HSP / RR-dim sub-tree audit (item 14)

Audit date: 2026-05-23. Methodology mirrors `RESIDUE_AUDIT.md` —
walk every file in tree that names `ExistsSimplePoleGermAtSomePoint`,
`RR_DimGE2_GenusZero_Germ`, `RR_StrictLt_GenusZero_Germ`,
`ExistsNonConstantBoundedByDeltaP_GenusZero`, `RiemannRochGenusZero`,
and `LinearSystemGermDeltaPFiniteDim`, and ask: where is this defined
as a `def Prop`, and where is it actually discharged by a
`theorem`/`instance` (not just consumed as a hypothesis)?

## TL;DR

* **`ExistsSimplePoleGermAtSomePoint RiemannSphere` is UNCONDITIONAL**
  in tree (theorem `existsSimplePoleGermAtSomePoint_RiemannSphere`,
  `JacobianChallenge/Manifold/RiemannSphereSimplePole.lean:223–227`).
* **`ExistsSimplePoleGermAtSomePoint X` for general X is OPEN.**
  It is conditionally discharged from
  `Nonempty (HolomorphicEquiv X RiemannSphere)` (theorem
  `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS`,
  `JacobianChallenge/Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean:172`).
* **`LinearSystemGermDeltaPFiniteDim RiemannSphere` is UNCONDITIONAL**
  (theorem `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional`,
  `JacobianChallenge/Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean:84`).
* So `RR_DimGE2_GenusZero_Germ X`, `RR_StrictLt_GenusZero_Germ X`,
  `ExistsNonConstantBoundedByDeltaP_GenusZero X`, and
  `RiemannRochGenusZero X` are **all conditionally discharged** from
  the single hypothesis
  `h_uniform : genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`.
* **None of these hSP-family hypotheses is hiddenly discharged for
  arbitrary X.** Unlike `ResidueTheorem` (which had an unconditional
  topological-degree route in tree that was named as a hypothesis),
  the hSP family genuinely sits behind one classical input on general
  X — `Nonempty (HolomorphicEquiv X RiemannSphere)` (uniformization
  at genus 0), or equivalently the "`∂̄`-equation solvability" content
  in `SimplePoleGermExtensionHypothesis` (an equivalent named form).
* **Item 14 = `genus_eq_zero_iff_homeo X` is already reduced to TWO
  classical inputs** by the existing in-tree theorem
  `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm`
  (`JacobianChallenge/Topology/Item14ForwardFromCompactConnected.lean:68`):
  `hSP X` and `S2ImpliesGenus0 X`. The `[FiniteDimensional]` typeclass
  is **already discharged unconditionally** internally via
  `DiskChartCover.holomorphicOneFormFiniteDim_holds`.

So the actual hSP-side gap is one classical content statement —
uniformization-at-genus-0 (or, equivalently, `∂̄`-solvability at
genus 0), not multiple. The proof scaffolding is fully in place.

---

## Section 1: Direct discharges per named hypothesis

### 1.1 `ExistsSimplePoleGermAtSomePoint X`

**Definition.** `JacobianChallenge/Topology/RRStrictLtFromSimplePole.lean:119`

```lean
def ExistsSimplePoleGermAtSomePoint : Prop :=
  ∃ (p : X) (φ : MeromorphicFunctionGerm X),
    φ ∈ linearSystemGermDeltaP (X := X) p ∧
    φ.orderAt p = ((-1 : ℤ) : WithTop ℤ)
```

Pure existence — no `genus X = 0` guard.

**Direct unconditional discharges:**

| theorem | file:line | shape |
|---|---|---|
| `existsSimplePoleGermAtSomePoint_RiemannSphere` | `JacobianChallenge/Manifold/RiemannSphereSimplePole.lean:223` | `ExistsSimplePoleGermAtSomePoint RiemannSphere` |

This is fully unconditional. Builds the explicit function `RSSimplePole : RiemannSphere → ℂ` with value `z` on the affine chart and `0` at `∞`, computes the order at `∞` to be `-1` via `meromorphicOrderAt_inv ∘ meromorphicOrderAt_id`, and checks the order at every finite point is `≥ 0`.

**Conditional discharges (general X):**

| theorem | file:line | input |
|---|---|---|
| `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS` | `JacobianChallenge/Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean:172` | `Nonempty (HolomorphicEquiv X RiemannSphere)` |
| `existsSimplePoleGermAtSomePoint_of_extension_at_genus_zero` | `JacobianChallenge/Manifold/SimplePoleConstructionFromChart.lean:122` | `SimplePoleGermExtensionHypothesis X` + `genus X = 0` |

The first transport is unconditional: it pulls `RSSimplePole` back through a biholomorphism `e : X ≃ RS`, sets `p := e.symm ∞`, and proves the order at `p` is `-1` via `mmeromorphicOrderAt_holomorphicEquiv_comp`.

The second is a *renaming* discharge — `SimplePoleGermExtensionHypothesis X` is **definitionally** `genus X = 0 → ExistsSimplePoleGermAtSomePoint X` (see `Manifold/SimplePoleConstructionFromChart.lean:104` and the iff lemma `simplePoleGermExtensionHypothesis_iff_genusConditional_existsSimplePoleGerm` at line 114). This is a *paraphrase*, not new content.

**Forward implications composing with hSP:**

The simple-pole germ supplies `2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` (theorem `rank_linearSystemGermDeltaP_ge_two_of_existsSimplePole`, `Topology/LinearSystemDivisorSimplePoleRank.lean:164`); combined with `LinearSystemGermDeltaPFiniteDim X`, this becomes `2 ≤ finrank`, i.e. `RR_DimGE2_GenusZero_Germ X` (theorem `rr_DimGE2_GenusZero_Germ_of_existsSimplePoleGerm_finiteDim`, same file:209).

### 1.2 `RR_DimGE2_GenusZero_Germ X`

**Definition.** `JacobianChallenge/Topology/RRDimensionFormGerm.lean:122`

```lean
def RR_DimGE2_GenusZero_Germ : Prop :=
  JacobianChallenge.genus X = 0 →
  ∃ p : X, 2 ≤ Module.finrank ℂ (linearSystemGermDeltaP (X := X) p)
```

**Direct unconditional discharges:**

None at the `RR_DimGE2_GenusZero_Germ X` shape for arbitrary X. The only "always-true" content is the in-tree fact that on RS the conclusion holds (and on RS, genus is also 0, so the implication is trivially OK).

**Conditional discharges:**

| theorem | file:line | inputs |
|---|---|---|
| `rr_DimGE2_GenusZero_Germ_of_existsSimplePoleGerm_finiteDim` | `Topology/LinearSystemDivisorSimplePoleRank.lean:209` | `hSP X`, `LinearSystemGermDeltaPFiniteDim X` |
| `rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_finiteDim` | `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean:67` | `Nonempty (HolomorphicEquiv X RS)`, `LinearSystemGermDeltaPFiniteDim X` |
| `rr_DimGE2_GenusZero_Germ_of_uniformization_and_finiteDim` | `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean:78` | genus-conditional uniformization, `LinearSystemGermDeltaPFiniteDim X` |
| `rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_RSFiniteDim` | `Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean:75` | `Nonempty (HolomorphicEquiv X RS)`, `LinearSystemGermDeltaPFiniteDim RiemannSphere` |
| `rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim` | `Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean:89` | genus-conditional uniformization, `LinearSystemGermDeltaPFiniteDim RiemannSphere` |
| `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim` | `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean:98` | genus-conditional uniformization **only** (RS-FiniteDim now unconditional) |

That last one is the punch line: **`RR_DimGE2_GenusZero_Germ X` on arbitrary X reduces to a single classical input — `genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)` — because everything else (existence side via the RS base case + transport; finite-dim side via RS unconditional + transport via the biholomorphism) is already in tree.**

### 1.3 `RR_StrictLt_GenusZero_Germ X`

**Definition.** `JacobianChallenge/Topology/RRStrictLtFromSimplePole.lean:97`

Strictly weaker than `RR_DimGE2_GenusZero_Germ` (no FiniteDim required).

**Conditional discharges:**

| theorem | file:line | inputs |
|---|---|---|
| `RR_StrictLt_of_RR_DimGE2_GenusZero_Germ` | `Topology/RRStrictLtFromSimplePole.lean:103` | `RR_DimGE2_GenusZero_Germ X` |
| `RR_StrictLt_of_existsSimplePoleGerm` | `Topology/RRStrictLtFromSimplePole.lean:168` | `hSP X` only |
| `RR_StrictLt_GenusZero_Germ_of_holomorphicEquiv_RS` | `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean:93` | `Nonempty (HolomorphicEquiv X RS)` |
| `RR_StrictLt_GenusZero_Germ_of_uniformization` | `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean:101` | genus-conditional uniformization |

`RR_StrictLt_of_existsSimplePoleGerm` is the workhorse: it discharges the strict-containment form **unconditionally on FiniteDim** using just linear independence (orders `0` vs `-1` are distinct, so `meromorphicOrderAt_add_of_ne` shows no nontrivial combination of `1` and `ψ` vanishes).

### 1.4 `RR_DimGE2_GenusZero X` (non-germ)

**Definition.** `JacobianChallenge/Topology/RRDimensionForm.lean:55`

Companion to the germ form, on the pointwise `linearSystemDeltaP` ambient. The germ form is the load-bearing one in the item-14 chain; the pointwise form lives only for legacy reasons (`Topology/RRGenusZeroFinrankChain.lean`, `RRGenusZeroFinalComposition.lean`, `ExistenceFromFinrank.lean`). Architecturally superseded by the germ form per the OPEN.md rebuild flag noted in `RRDimensionFormGerm.lean`.

**No unconditional or per-X discharges** of the pointwise form on arbitrary X exist beyond the same uniformization-class routes.

### 1.5 `ExistsNonConstantBoundedByDeltaP_GenusZero X`

**Definition.** `JacobianChallenge/Topology/ExistsMeroSimplePoleSplit.lean:72`

The "(a)-only" RR existence consequence at the level of bundled meromorphic-nonzero functions (not germs).

**Conditional discharges:**

| theorem | file:line | inputs |
|---|---|---|
| `existsNonConstantBoundedByDeltaP_of_RR_StrictLt_Germ` | `Topology/RRStrictLtFromSimplePole.lean:219` | `RR_StrictLt_GenusZero_Germ X` |

Composes the strict-lt form with the lift `MeromorphicFunctionGerm.liftToMeromorphicNonzero` (which depends on the identity theorem in `Manifold/MeromorphicFunctionField.lean`, already in tree). No unconditional discharge on general X.

### 1.6 `RiemannRochGenusZero X`

**Definition.** `JacobianChallenge/Topology/UniformizationFromRiemannRoch.lean:72`

The headline-shape RR consequence: "`genus X = 0 →` there exists a degree-1 holomorphic map `X → RiemannSphere`."

**Conditional discharges:**

| theorem | file:line | inputs |
|---|---|---|
| `riemannRochGenusZero_from_RR_DimGE2_Germ` | `Topology/RRGenusZeroGermComposition.lean:71` (via the dim form route) | `RR_DimGE2_GenusZero_Germ X` |
| `riemannRochGenusZero_from_RR_StrictLt_Germ` | `Topology/RRStrictLtFromSimplePole.lean:232` | `RR_StrictLt_GenusZero_Germ X` |
| `riemannRochGenusZero_from_ExistsSimplePoleGerm` | `Topology/RRStrictLtFromSimplePole.lean:241` | `hSP X` only |
| `riemannRochGenusZero_of_holomorphicEquiv_RS` | `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean:114` | `Nonempty (HolomorphicEquiv X RS)` |
| `riemannRochGenusZero_of_uniformization` | same file:122 | genus-conditional uniformization |
| `riemannRochGenusZero_of_uniformization'` | `Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean:114` | genus-conditional uniformization (RS-FiniteDim discharged internally) |

Same picture: `RiemannRochGenusZero X` is one classical input — uniformization at genus 0 — away from being unconditional.

### 1.7 `LinearSystemGermDeltaPFiniteDim X` (the RR upper-bound hypothesis)

**Definition.** `JacobianChallenge/Topology/LinearSystemDivisorSimplePoleRank.lean:180`

This is the "`L(δp)` is finite-dim" half of RR.

**Direct unconditional discharge on RS:**

| theorem | file:line | shape |
|---|---|---|
| `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional` | `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean:84` | `LinearSystemGermDeltaPFiniteDim RiemannSphere` |

Composes the two earlier named inputs `linearSystemAtInftyRS_boundedBySimplePoleSpan` (chip-A1, polynomial-growth Liouville, in `Topology/LinearSystemAtInftyRSDischarge.lean`) and `existsMobiusToInftyRS_holds` (chip-A2, Möbius transitivity, `Manifold/MobiusTransitivityRS.lean`). Both subordinate discharges land 2026-05-14; the headline is `rfl`-clean.

**Transport:**

`LinearSystemGermDeltaPFiniteDim.of_nonempty_holomorphicEquiv` (`Topology/LinearSystemGermDeltaPFiniteDimTransport.lean`) gives `LinearSystemGermDeltaPFiniteDim Y` + `HolomorphicEquiv X Y → LinearSystemGermDeltaPFiniteDim X`. So `LinearSystemGermDeltaPFiniteDim X` is one biholomorphism away from unconditional.

---

## Section 2: Infrastructure already in tree (general)

This section asks what's in tree beyond the immediate hSP-family. The
goal: catch infrastructure analogous to the topological-degree /
Hurwitz route that closed `ResidueTheorem`.

### 2.1 Genus / `Subsingleton (HolomorphicOneForm X)` machinery

* `JacobianChallenge.finiteDimensional_of_HolomorphicOneFormFiniteDim`
  (`Manifold/HodgeFiniteDimensional.lean:114`).
* `DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X)`
  (`Manifold/DiskChartCoverFiniteDim.lean`) — discharges the
  finite-dim hypothesis on `HolomorphicOneForm X` **unconditionally**
  for arbitrary compact connected complex 1-manifold X. Item 1 of
  the challenge.
* `holomorphicOneForm_subsingleton_of_genus_eq_zero` (`Manifold/HolomorphicOneFormLinear.lean:71`):
  `genus X = 0 → Subsingleton (HolomorphicOneForm X)` given finite-dim.
  Plus `genus_eq_zero_of_holomorphicOneForm_subsingleton`
  (in the same file): the converse.
* `instance : Subsingleton (HolomorphicOneForm RiemannSphere)`
  (`Manifold/RiemannSphereChartSCoeffOverlap.lean:169`) — **unconditional**.

These give: on arbitrary X, `genus X = 0 ↔ Subsingleton (HolomorphicOneForm X)`
once `[FiniteDimensional ℂ (HolomorphicOneForm X)]` is in scope
(which itself is unconditional via item 1).

### 2.2 Linear-equivalence of `HolomorphicOneForm` (Hodge identification)

* `LinearEquiv.ofSubsingletons` (`Manifold/HolomorphicOneFormEquivFromGenus.lean:77`) —
  any two subsingleton modules are `R`-linearly equivalent.
* `holomorphicOneFormEquivRiemannSphere_of_subsingleton` (same file:98) —
  from `[Subsingleton (HolomorphicOneForm X)]` produces
  `HolomorphicOneFormEquivRiemannSphere X` (the named hypothesis at
  `Topology/S2ImpliesGenus0Discharge.lean`).
* `holomorphicOneFormEquivRiemannSphere_of_genus_zero` (same file:107) —
  from `genus X = 0` + finite-dim, get the same.

Consequence: the linear-equivalence hypothesis used by the reverse leg
of `S2ImpliesGenus0Discharge.lean` is **derivable from `genus X = 0`
alone** (since finite-dim is unconditional). This is a tautology when
viewed from the chain `genus X = 0 → Subsingleton (HolomorphicOneForm X)
→ HolomorphicOneFormEquivRS X → S2ImpliesGenus0 X`, but it's important
that *no extra classical content* is needed on top of `genus X = 0` to
get the linear equivalence.

### 2.3 `RiemannSphere` genus

* `RiemannSphere.genus_RiemannSphere_statement_holds`
  (`Manifold/RiemannSphereChartSCoeffOverlap.lean`) — `genus RS = 0`
  unconditionally.

### 2.4 `S2ImpliesGenus0` machinery (the second-half reduction)

* `simplyConnectedS2_holds` (`Topology/SimplyConnectedS2Unconditional.lean:40`) —
  `SimplyConnectedSpace JacobianChallenge.StandardS2` **unconditional**
  (the 15-chip Phase-3 arc, 2026-05-15).
* `subsingleton_of_primitiveExistence` (`Topology/SubsingletonFromPrimitiveExistence.lean:185`) —
  from a smooth primitive on the simply-connected manifold, get
  `Subsingleton (HolomorphicOneForm X)` (composes with the unconditional
  Liouville on compact connected).
* `s2ImpliesGenus0_from_simplyConnected` (`Topology/S2ImpliesGenus0FromSimplyConnected.lean:114`):
  reduces `S2ImpliesGenus0 X` to a named hypothesis
  `HolomorphicOneFormSubsingletonOfSimplyConnected X` (= simply-connected
  ⟹ Subsingleton-holomorphic-1-form).
* `s2ImpliesGenus0_of_basisPathPrimitive`, `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis`,
  `s2ImpliesGenus0_of_BSLB_and_admissibleChartCover`,
  `s2ImpliesGenus0_of_primitiveExistence_uncond` — multiple parallel
  per-basis reductions.
* `s2ImpliesGenus0_of_linearEquiv_unconditional`
  (`Topology/S2ImpliesGenus0Unconditional.lean:58`) — needs
  `HolomorphicOneFormEquivRiemannSphere X`, which (per §2.2) is
  derivable from `genus X = 0` alone.

`S2ImpliesGenus0 X` is **not yet unconditional on arbitrary X**. The
RS case is in tree (`s2ImpliesGenus0_riemannSphere`,
`Topology/HolomorphicOneFormSubsingletonOfSimplyConnectedRS.lean:52`).
The general-X case waits on either (i) the primitive-existence
content on a simply-connected manifold, or (ii) the BSLB +
admissibility content. Neither is item-14-frontier-blocking once
hSP X is discharged via `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm`,
because that theorem **only** consumes `S2ImpliesGenus0 X` on the
reverse leg, not on the forward leg.

### 2.5 Topological-degree / Hurwitz / non-constant analytic maps

* `JacobianChallenge.surjective_of_NonConstant_Analytic_Manifold_holds`
  (`Manifold/SurjectiveOfNonConstantDischarge.lean`, zz382) — unconditional.
* `JacobianChallenge.bijectiveAnalyticIsBiholomorphism_holds`
  (`Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`,
  zz388) — unconditional.
* `JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional`
  (`Manifold/NearbyRegularWitnessUnconditional.lean`) — unconditional.
* `JacobianChallenge.degreeOneIsBiholomorphic_RS_of_conditionals` —
  conditional composition of the three above, used to derive
  `DegreeOneIsBiholomorphic_RS X`.

This is exactly the analytic-degree infrastructure that the residue
audit found. It's the *forward-leg* glue (degree-1 map ⟹
biholomorphism) but it does **not** itself give us `Nonempty
(HolomorphicEquiv X RS)` without a degree-1 holomorphic map to start
with, which is what `RiemannRochGenusZero X` produces (and that needs
hSP X).

### 2.6 Liouville / identity theorem

* `liouvilleOnCompactConnected_holds` (`Topology/HolomorphicLocallyConstantDischarge.lean`) —
  holomorphic on a compact connected complex 1-manifold ⟹ constant.
* Identity-theorem upgrades in `Manifold/MeromorphicFunctionField.lean`.

Important pre-existing infrastructure but does not directly discharge any hSP-family hypothesis.

### 2.7 RR-on-elliptic-curves / Serre duality / Hodge decomposition

Searched. **Not in tree.** No `riemannRochElliptic`, no `serreDuality`,
no `hodgeDecomposition` for general X (or for elliptic curves). The
RS unconditional case is built by direct Laurent/Möbius arguments,
not via a general-RR theorem.

### 2.8 `BasedSmoothLoopsBoundHypothesis` discharges

* `RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds`
  (`Manifold/StokesBoundariesTopRiemannSphere.lean:47`) — unconditional on RS.
* `basedSmoothLoopsBoundHypothesis_C_holds` (`Manifold/BasedSmoothLoopsBoundC.lean:66`) — unconditional on ℂ.

Both are RS-/ℂ-specific. General X is open (the "smooth Hurewicz at genus 0" content from the MEMORY.md handoff).

---

## Section 3: Transport / specialization routes

### 3.1 From `[HasConvexChartAtTarget X]` to admissibility

* `instHasAdmissibleChartCoverOfConvexChartAtTarget`
  (`Manifold/HasAdmissibleChartCoverFromConvexChartAtTarget.lean:93`) — an
  unconditional **instance** from `[HasConvexChartAtTarget X]` to
  `[HasAdmissibleChartCover X]`. Used in
  `Topology/Item14From2InputsUnderConvexChartAt.lean` to auto-discharge
  the smoothness + FTC primitive-side hypotheses.
* `instance : HasConvexChartAtTarget RiemannSphere`
  (`RiemannSphere/HasConvexChartAtTargetRiemannSphere.lean:38`) — RS instance.

Effect: on `X` with `[HasConvexChartAtTarget X]` (RS qualifies), the
4-input form of item 14 collapses to a 2-input form
(`hSP X` + `h_bslb`).

### 3.2 From `Nonempty (HolomorphicEquiv X RS)`

The transport machinery, gathered:

* `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS` (§1.1 above).
* `LinearSystemGermDeltaPFiniteDim.of_nonempty_holomorphicEquiv`
  (`Topology/LinearSystemGermDeltaPFiniteDimTransport.lean`).
* `genus_zero_of_linearEquiv_RiemannSphere_unconditional` and
  `s2ImpliesGenus0_of_linearEquiv_unconditional`
  (`Topology/S2ImpliesGenus0Unconditional.lean`).
* `Manifold/GenusEqZeroFromHolomorphicEquivRS.lean` (`h : Nonempty
  (HolomorphicEquiv X RS) → genus X = 0`).

So a single biholomorphism with RS transports **all** of the
relevant content. The forward direction of item 14 then becomes
"derive `genus X = 0 → Nonempty (HolomorphicEquiv X RS)`."

### 3.3 The cleanest end-to-end in-tree theorems

| theorem | hypotheses | source |
|---|---|---|
| `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm` | `hSP X`, `S2ImpliesGenus0 X` (no `[FiniteDimensional]`, discharged internally) | `Topology/Item14ForwardFromCompactConnected.lean:68` |
| `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton` | `hSP X`, `[Subsingleton (HolomorphicOneForm X)]` | `Topology/HTopFromSubsingleton.lean:125` |
| `genus_eq_zero_iff_homeo_from_RR_DimGE2_Germ_and_top` | `RR_DimGE2_GenusZero_Germ X`, `h_top` | `Topology/Item14FromGermfield.lean:76` |
| `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_top` | `hSP X`, `h_top` | `Topology/RRStrictLtFromSimplePole.lean:251` |
| `genus_eq_zero_iff_homeo_from_2_classical_inputs_under_convexChartAt` | `[HasConvexChartAtTarget X]`, `hSP X`, `h_bslb` | `Topology/Item14From2InputsUnderConvexChartAt.lean:72` |
| `genus_eq_zero_iff_homeo_from_hSP_BSLB_under_subsingleton` | `[Subsingleton (HolomorphicOneForm X)]`, `hSP X`, `h_bslb` | `Topology/Item14FromHSPBSLBAndPathPrimitive.lean:98` |

The first is the strictly cleanest reduction in tree right now.

---

## Section 4: Synthesis

### 4.1 Is `ExistsSimplePoleGermAtSomePoint X` (or `RR_DimGE2_GenusZero_Germ X`) already proven for arbitrary X via a hidden route?

**No.** Unlike the residue-theorem case (which had a hidden
unconditional discharge via the topological-degree / Hurwitz chain),
the hSP family is genuinely open on arbitrary X. The cleanest
non-trivial classical content is in the explicit construction of a
simple-pole meromorphic function on a genus-0 surface — which on RS is
the explicit `RSSimplePole` (unconditional in tree) and on general X
either requires `∂̄`-solvability at genus 0 (Hodge), Forster Thm 16.9,
or transport through uniformization.

What **is** hiddenly already done (and was not obvious from a casual
read) is:

1. `LinearSystemGermDeltaPFiniteDim RiemannSphere` was a named
   hypothesis at one point — but as of 2026-05-14 it has been
   **fully discharged unconditionally** by composing the
   `linearSystemAtInftyRS_boundedBySimplePoleSpan` discharge (chip-A1)
   with `existsMobiusToInftyRS_holds` (chip-A2).
   (`Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`.)
2. `[FiniteDimensional ℂ (HolomorphicOneForm X)]` for arbitrary X is
   unconditional via `DiskChartCover.holomorphicOneFormFiniteDim_holds`.
3. The `[FiniteDimensional]`-conditional forms of `Item14ForwardFromFiniteDim`
   are auto-upgraded by
   `Topology/Item14ForwardFromCompactConnected.lean` to drop the
   typeclass.

So the "hidden discharge" of this sub-tree is not at the hSP-family
level — it's the **two downstream chips that drop FiniteDim and
discharge RS-FiniteDim**. After those, hSP X really is the single
remaining classical input on the forward leg.

### 4.2 If no full discharge, what's the largest partial / conditional discharge in tree?

* **Full unconditional discharge:** `X = RiemannSphere`. Every named
  hSP-family hypothesis is unconditional for X = RS.
* **Generic X with biholomorphism to RS:** `Nonempty (HolomorphicEquiv
  X RiemannSphere)` gives `ExistsSimplePoleGermAtSomePoint X`,
  `RR_DimGE2_GenusZero_Germ X`, `RR_StrictLt_GenusZero_Germ X`,
  `RiemannRochGenusZero X`, `LinearSystemGermDeltaPFiniteDim X`,
  `genus X = 0`, and `S2ImpliesGenus0 X`, all unconditionally. This is
  the "transport through uniformization" content.
* **Generic X with `[Subsingleton (HolomorphicOneForm X)]`:** modulo
  `hSP X`, item 14 is closed
  (`genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`).
  The subsingleton typeclass is itself equivalent (via item 1) to
  `genus X = 0`.

### 4.3 What named hypotheses, if discharged with a one-line wiring lemma, would close item 14?

**None.** I checked carefully. There is no `def Prop`-style hypothesis
in the hSP sub-tree whose Lean content is already proven by a
differently-named theorem. Specifically:

* `ExistsSimplePoleGermAtSomePoint X` (general X) — proved only on
  RS and transported via a biholomorphism. No general-X discharge.
* `LinearSystemGermDeltaPFiniteDim X` (general X) — proved on RS,
  transported via a biholomorphism. No general-X discharge.
* `SimplePoleGermExtensionHypothesis X` — definitionally
  `genus X = 0 → ExistsSimplePoleGermAtSomePoint X`, i.e. a paraphrase.
* `RiemannRochGenusZero X` — composes from hSP X or from
  uniformization.
* `S2ImpliesGenus0 X` (general X) — proved on RS only.
* `Nonempty (HolomorphicEquiv X RiemannSphere)` (general X, genus-0
  conditional) — this is **the** uniformization hypothesis; not
  proven for general X anywhere in tree.

The residue-theorem audit found a one-line wiring lemma because the
content of `ResidueTheorem X` had been independently proved under a
different name. **No analog of that hidden wiring exists in the hSP
sub-tree.** The "wiring lemmas" that exist are all transport lemmas
that route through a biholomorphism with RS — i.e., they require the
uniformization input, not less.

### 4.4 What's the actual size of the remaining classical-content gap?

After this audit, the remaining **classical content gap** for item 14
on arbitrary X consists of exactly two independent items:

1. **`ExistsSimplePoleGermAtSomePoint X`** on arbitrary genus-0 X.
   Classically: Forster Thm 16.9 or `∂̄`-solvability at genus 0
   (= `H¹(X, O) = 0`). This is **the** RR existence content. None of
   this is in mathlib at the pin; would need either L²-Hodge theory
   for compact Riemann surfaces (the `∂̄` chain) or the Cech / sheaf
   `H¹(X, O) = 0` route.

2. **`S2ImpliesGenus0 X`** on arbitrary X (only needed for the reverse
   leg). Reduces (per `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis`,
   `s2ImpliesGenus0_of_primitiveExistence_uncond`, etc.) to one of:
   - `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀` on simply-connected
     X (smooth Hurewicz at genus 0 content), or
   - primitive-existence on simply-connected X (path-integral content).

Both gaps are textbook classical content; neither is fabricated
mathlib-class material. Concrete LOC estimates are not measurable
from comparable prior work in this repo (the MEMORY.md anti-pattern
applies); I will not quote one.

A *single* uniformization-class statement
`genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)` closes
both gaps simultaneously, but it is heavier than either of them
individually.

### 4.5 Recommended next-session deliverable

**ONE concrete recommendation, named exactly:**

Write `JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean`
containing:

```lean
/-- Classical Hodge content: at `genus X = 0`, `H¹(X, O) = 0`, and
the `∂̄`-equation `∂̄ u = α` is solvable for any smooth `(0,1)`-form
`α` on `X`. Named hypothesis. -/
def DBarSolvabilityAtGenusZero (X : Type*) [...] : Prop := ...

/-- Forster Thm 16.9-style: from `∂̄`-solvability at genus 0 + the
explicit chart-local pole `g₀ := 1/φ` + cutoff `χ`, construct the
global simple-pole germ via `f := χ · g₀ - u` with `∂̄ u = ∂̄(χ · g₀)`.
-/
theorem existsSimplePoleGermAtSomePoint_of_dbar_solvability
    (h : DBarSolvabilityAtGenusZero X) (hg : genus X = 0) :
    ExistsSimplePoleGermAtSomePoint X := by ...
```

This is **classical content, not paraphrase**: it discharges hSP X
from a strictly smaller and more concrete named hypothesis
(`DBarSolvabilityAtGenusZero X`), with the chart-local cutoff +
correction argument fully in-Lean. The named hypothesis it leaves
open (`∂̄`-solvability at genus 0) is one mathlib-pin sheaf-cohomology
chip away from full mathlib eligibility, and is the **single most
direct classical statement of `H¹(X, O) = 0` at genus 0**.

This avoids the anti-patterns in MEMORY.md: it does not write a
"from N inputs" reformulation, does not duplicate an existing
discharge route, and does not multiply per-X instances. It is the
**textbook proof** (Forster §16) of one step on the chain. The named
hypothesis it introduces is genuinely smaller than what it discharges
(`DBarSolvabilityAtGenusZero` ⊂ `hSP`-classical content); the
remaining frontier is the same as the "discharge `DBarSolvabilityAtGenusZero`"
goal that would be left.

If preferred over the `∂̄` route, an alternative single-arc deliverable
is the **periods-mapping construction** (Riemann's original: at
genus 0, the period mapping `H^0(Ω^1) → H^1(X, ℤ)` is trivial, hence
the Abel-Jacobi map gives a holomorphic isomorphism with `ℂ⧸0 = ℂ`,
hence with `RiemannSphere`). This deliverable would be:

`JacobianChallenge/Manifold/UniformizationGenusZeroViaPeriods.lean` —
prove `genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)` via
the period-mapping route, which closes both gaps 4.4-(1) and 4.4-(2)
at once. This is bigger but also strictly textbook (Forster §17 +
Griffiths-Harris §2).

**Pick `ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean`** —
it is the **smaller** of the two and gives the cleaner sub-goal
(the `∂̄` content, which is a single sheaf-cohomology statement,
not the full period-mapping arc).
