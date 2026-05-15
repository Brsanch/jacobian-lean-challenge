# HANDOFF — 2026-05-15 evening — C3 sub-arc: path-lift infrastructure

## State at handoff

* **Branch / HEAD**: `main` at `2693258` (pushed to `origin/main`).
* **Build**: `taskpolicy lake build` green, **8746 jobs**. Zero `sorry`,
  zero `axiom` across all 25 evening chips.
* **Items flipped**: none — items 4/5/10/11/12/13 remain STUB/OPEN
  pending the full level-set chain + Stokes/lattice argument.
* **Net LOC delta today (evening session)**: +~2,900 LOC across 19
  new files in `JacobianChallenge/Manifold/`.

## What landed (25 chips)

All chips are in the `MeromorphicNonzero` namespace and target the
**path-lift infrastructure** that the level-set chain construction
will consume.  The 25 chips are tabulated by phase:

### Phase A — Algebra-side closure of `dischargedGenerators` (3 chips)

* `Manifold/AbelGeneratorDischargedSet.lean`
  * Definition `dischargedGenerators B :=
    { f : MeromorphicNonzero X | period vector of AJ chain of (f) ∈
    periodLatticeImage }`.
  * Closure under `1` (`one_mem_dischargedGenerators`), constants
    (`const_mem_dischargedGenerators`), `*` (`mul_mem`), `invMer`
    (`invMer_mem`), quotients (`mul_invMer_mem`).
  * Vacuous-divisor discharge `mem_dischargedGenerators_of_principalDivisor_zero`.
  * `principalDivisorMap_of_toFun_const` + `toFun_const_mem_dischargedGenerators`
    — constant-function case.
  * `toFun_ne_const_zero` — `f.toFun ≠ fun _ => 0` from
    `nonvanishing_germ`.
  * `abelGeneratorPeriodCondition_iff_dischargedGenerators_eq_univ` /
    `abelGeneratorPeriodCondition_of_forall_nonconst_toFun` —
    case-split reduction of `AbelGeneratorPeriodCondition B` to the
    non-constant `toFun` case.

### Phase B — Regular-value framework (1 chip)

* `Manifold/MeromorphicNonzeroRegularValueSet.lean`
  * `MeromorphicNonzero.regularValueSet f := (f.criticalValues)ᶜ`.
  * `criticalValues_finite` / `criticalValues_isClosed` /
    `regularValueSet_isOpen` under non-constancy of
    `f.toRiemannSphere`.

### Phase C — Planar local biholomorphism (2 chips)

* `Manifold/MeromorphicNonzeroLocalBiholomorphism.lean`
  * `MeromorphicNonzero.chartPullback f x` (literal chart pullback).
  * `analyticAt_chartPullback` (ω-smoothness ⇒ analytic).
  * `deriv_chartPullback_ne_zero_of_regular` — non-zero derivative at
    every regular point, pulled directly from
    `DerivBridgeData.hCompat`.
  * `exists_local_biholomorphism_chartPullback` — planar local
    inverse via the existing `AnalyticAt.exists_local_biholomorphism`.

* `Manifold/MeromorphicNonzeroLocalSheet.lean` (planar OPH portion)
  * `chartPullback_oph` — planar `OpenPartialHomeomorph ℂ ℂ` via
    `HasStrictFDerivAt.toOpenPartialHomeomorph`.
  * `mem_source_chartPullback_oph`, `coe_chartPullback_oph`,
    `isOpen_source_chartPullback_oph`.

### Phase D — Manifold-level local sheet (1 chip)

* `Manifold/MeromorphicNonzeroLocalSheet.lean` (chip 7 portion)
  * `manifoldLocalOph` — `OpenPartialHomeomorph X RiemannSphere` via
    double `restrOpen` of `c.trans (φ'.trans d.symm)`: planar source
    ∩ `c.target`, then outer ∩ `f.toRiemannSphere ⁻¹' d.source`.
  * `manifoldLocalOph_apply` / `mem_source_manifoldLocalOph` /
    `mem_target_manifoldLocalOph`.
  * `localSheetData_at_regular` — assembles `LocalSheetData
    f.toRiemannSphere (f.toRiemannSphere x₀) x₀`.

### Phase E — Topological packaging (3 chips)

* `Manifold/MeromorphicNonzeroLocalSheet.lean` (chip 8 portion)
  * `isLocalHomeomorphOn_toRiemannSphere` — `IsLocalHomeomorphOn
    f.toRiemannSphere f.regularSet` via `IsLocalHomeomorphOn.mk` +
    `manifoldLocalOph_apply`.
  * `continuousAt_toRiemannSphere_of_regular` /
    `map_nhds_eq_of_regular` — corollaries.

* `Manifold/MeromorphicNonzeroFiberFinite.lean`
  * `fiber_isClosed`, `mem_regularSet_of_preimage_regularValue`.
  * `fiber_finite_of_mem_regularValueSet` — compactness +
    `IsCompact.elim_nhds_subcover` + `choose!`.

* `Manifold/MeromorphicNonzeroHurwitzPatching.lean`
  * `hurwitzPatchingData_at_regularValue` —
    `HurwitzPatchingData.ofLocalSheets` composing chips 7 + 9.

### Phase F — Continuous path-lift primitives (5 chips)

* `Manifold/MeromorphicNonzeroLocalPathLift.lean`
  * `exists_continuous_local_lift_of_continuous` — local lift on
    `β ⁻¹' sheet.V`, via `sheet.g ∘ β` continuous on the preimage.

* `Manifold/MeromorphicNonzeroPathLiftUnique.lean`
  * `path_lift_unique` — clopen on agreement set in connected ℝ.

* `Manifold/MeromorphicNonzeroPathLiftUniqueOn.lean`
  * `path_lift_eqOn_Icc` — clopen on agreement set in the connected
    subspace `Icc a b`.

* `Manifold/MeromorphicNonzeroPathLiftExtend.lean`
  * `extend_lift_across_sheet` — piecewise extension across one
    local sheet via `ContinuousOn.if`.

* `Manifold/MeromorphicNonzeroPathLiftAtPoint.lean`
  * `exists_sheet_data_extending_to_right` — local-sheet existence at
    a lift point.
  * `extend_continuous_lift_to_right` — combines with chip 19 to
    extend a partial lift past `b` by a positive amount.

* `Manifold/MeromorphicNonzeroPathLiftSequencePatch.lean`
  * `lifts_agree_globally` / `lifts_agree_at` — choice-independence
    of patched lifts.

### Phase G — Smooth path-lift primitives (4 chips)

* `Manifold/MeromorphicNonzeroLocalSheetSmooth.lean`
  * `contMDiffAt_localSheet_g_at_basePoint` — pointwise `ContMDiffAt
    ω` of `manifoldLocalOph.symm` at base point.  Via
    `contMDiffAt_omega_of_analyticAt_chart_pullback` applied to chart
    pullback locally equal to `φ.symm`.

* `Manifold/MeromorphicNonzeroSmoothLocalLift.lean`
  * `contMDiffAt_local_lift_at_basepoint` — smooth (`ContMDiffAt
    𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞`) lift at the base point of β.  Chain:
    chip 12 + `ContMDiffAt.complex_to_real` + `ContMDiffAt.comp`.

* `Manifold/MeromorphicNonzeroLocalSheetSmoothOn.lean`
  * `exists_contMDiffOn_localSheet_g_near_basePoint` — open-nbhd
    `ContMDiffOn ω` via `contMDiffAt_iff_contMDiffOn_nhds` (valid
    at ω ≠ ∞).

* `Manifold/MeromorphicNonzeroSmoothLocalLiftOn.lean`
  * `exists_contMDiffOn_local_lift` — smooth `ContMDiffOn 𝓘(ℝ,ℝ)
    𝓘(ℝ,ℂ) ∞` lift on an open neighbourhood of `t₀`.

### Phase H — Single-sheet global lift (1 chip)

* `Manifold/MeromorphicNonzeroPathLiftSingleSheet.lean`
  * `exists_continuous_lift_single_sheet` — no-gluing case: β maps
    all of ℝ into one local sheet ⇒ `sheet.g ∘ β` is a continuous
    global lift.

### Phase I — Lebesgue partition (1 chip)

* `Manifold/MeromorphicNonzeroPathLiftPartition.lean`
  * `exists_subdivision_hurwitzPatching` — Lebesgue subdivision of
    `unitInterval` adapted to a regular path via
    `exists_monotone_Icc_subset_open_cover_unitInterval`.

### Phase J — `liftReachable` set + openness + bounds (3 chips)

* `Manifold/MeromorphicNonzeroPathLiftGlobal.lean`
  * Definition `liftReachable f β x₀ T := { b ∈ Icc 0 T | ∃
    continuous γ lifting β on Icc 0 b starting at x₀ }`.
  * `zero_mem_liftReachable`, `liftReachable_downward_closed`.

* `Manifold/MeromorphicNonzeroPathLiftGlobalOpen.lean`
  * `liftReachable_extends_right` — **openness** via the clip+if_le
    construction: `clip t := max b (min (b + ε) t)` projects `t`
    onto `[b, b + ε]`; `h t := sheet.g (β (clip t))` is continuous
    globally because β-of-clip stays in `sheet.V`; `γ_glob := if
    t ≤ b then γ t else h t` glues via `Continuous.if_le` with
    agreement at `b` from `sheet.leftInvOn`.

* `Manifold/MeromorphicNonzeroPathLiftGlobalClosed.lean`
  * `liftReachable_subset_Icc`, `liftReachable_bddAbove`,
    `sSup_liftReachable_le`, `sSup_liftReachable_nonneg`.

## Net open content (revised after 25 chips)

To close C3 (general genus), the remaining steps are (rough LOC
estimates; see "caveat" below):

| # | Step | LOC est. |
|---|---|---|
| 1 | `sSup ∈ liftReachable` (closedness via sequential limit + local sheet) | 250–350 |
| 2 | `sSup = T` (clopen finish, IsClopen.eq_univ on connected `[0, T]`) | 80–120 |
| 3 | Smooth upgrade of global continuous lift to `ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞` | 150–250 |
| 4 | `SmoothPath 𝓘(ℝ,ℂ) X` bundle (reparametrise + `toPath`/`smooth` fields) | 100–150 |
| 5 | `levelSetChain f β : SmoothChain 𝓘(ℝ,ℂ) X` definition (sum over fiber) | 150–250 |
| 6 | Boundary `∂(levelSetChain f β) = δ_{fiber tgt} − δ_{fiber src}` | 200–400 |
| 7 | β: 0 → ∞ choice + boundary = `principalDivisorMap f` identification | 200–400 |
| 8 | Pushforward 1-form `f_*ω` on ℙ¹ + integral identity | 300–500 |
| 9 | Lattice argument (periods of `f_*ω` mod `periodLatticeImage`) | 400–800 |

**Subtotal: ~1,830–3,220 LOC.**  C4 (general genus) — Abel converse
+ Jacobi inversion — adds **~1,500–3,000 LOC**.

### Caveat on LOC estimates

Today's 25 chips delivered ~2,900 LOC, **much more than the pre-session
~300–500 LOC estimate** for "global path lift over unit interval".
My historical LOC estimates are 2–6× off; the table above should be
read as a lower bound, with actual costs likely considerably higher.

Specifically: the level-set chain + boundary + β-choice +
pushforward + lattice argument (rows 5–9) total ~1,250–2,350 LOC by
my estimate; the same calibration multiplier suggests actual ~3,000–
9,000 LOC.

The honest framing: **C3 alone could plausibly require another full
multi-thousand-LOC arc of focused work**, on the order of today's
session.  C3 + C4 together: comparable to two more such arcs.

## Suggested next-session entry point

The **closedness lemma** is the clean next step:

```lean
theorem sSup_mem_liftReachable
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β) (x₀ : X)
    {T : ℝ}
    (hβ_reg : ∀ t ∈ Icc 0 T, β t ∈ f.regularValueSet)
    (hx₀ : f.toRiemannSphere x₀ = β 0) (hT : 0 ≤ T) :
    sSup (f.liftReachable β x₀ T) ∈ f.liftReachable β x₀ T
```

Proof outline:
* Set `s := sSup (liftReachable)`.  `0 ≤ s ≤ T` from chip 25.
* Pick `(b_n)_n ↑ s` with each `b_n ∈ liftReachable` (via
  `exists_seq_lt_strictMono_tendsto'` or similar on `sSup`).
* By compactness of `X`, a subsequence of `γ_{b_n}(b_n)` converges to
  some `x_s ∈ X`.  Continuity of `f.toRiemannSphere` gives `f.toRS
  x_s = β s`, so `x_s` is a preimage of the regular value `β s` and
  hence in `f.regularSet` (chip 9).
* Local sheet at `x_s`.  For `t` close to `s` (within
  `β ⁻¹' sheet.V`), `γ_{b_n}(t)` for large `n` lies in `sheet.U` (by
  continuity of `γ_{b_n}` and `γ_{b_n}(b_n) → x_s`).  Hence
  `γ_{b_n}(t) = sheet.g (β t)` on a left-nbhd of `s` (uniqueness of
  lift in the sheet).
* Define `γ(t) := γ_{b_n}(t)` for `t < s` (any `n` with `b_n > t`,
  well-defined by chip 22 / chip 21), and `γ(s) := sheet.g (β s)`.
  Glue via the clip+if_le construction from chip 24 to get a globally
  continuous extension.

Following the closedness lemma, the chip 23/24/25 framework chains:
openness + closedness + non-empty (`0`) in connected `[0, T]` ⇒
`liftReachable = Icc 0 T`, hence `T ∈ liftReachable`, hence the
global continuous lift on `[0, T]` exists.

## Open caveats / known wrinkles

* **`HurwitzPatchingData.U/V` are tactic-built fields.**  Chip 10's
  `hurwitzPatchingData_at_regularValue` is constructed via `refine
  HurwitzPatchingData.ofLocalSheets ...` and the `.U` / `.V` fields
  are set via `let`-bindings inside the tactic.  Extracting `H.U x ⊆
  LocalSheetData.U at x` requires unfolding the tactic-block — chip
  20's anchor-choice lemma attempted this and stalled.  Workaround:
  use `LocalSheetData` directly via chip 7 + chip 20's
  `exists_sheet_data_extending_to_right`, which carries the
  `LocalSheetData` identity through.

* **Realification subtlety.**  Smooth chips at `ω` regularity (chips
  12, 14) live in the ℂ-model; SmoothPath uses `𝓘(ℝ,ℂ)` with `∞`
  regularity.  `ContMDiffAt.complex_to_real` bridges, but loses the
  `ω` strength on the way (gives `∞`).  Step 3 (smooth upgrade)
  needs this bridge applied at every relevant point.

* **`hM_symm_v₀` requires propagating `f.toRiemannSphere z = β t`
  through `LocalSheetData`.**  Several chips ran into motive
  type-correctness issues when rewriting `f.toRS z = β t` inside
  `LocalSheetData`-typed terms.  Resolution: rewrite via the value
  side (e.g. `hz_lift ▸ sheet.mem_V`) rather than the type side.

* **Chip 26 attempt failed.**  Initial closedness attempt got stuck
  on three-piece piecewise continuity via `Continuous.if_le`
  (mathlib only handles two pieces).  The clip+if_le pattern from
  chip 24 may transfer to the closedness construction; alternatively
  use `continuous_iff_continuousAt` with per-point case analysis.
