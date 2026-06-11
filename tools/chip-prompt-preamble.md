# Chip prompt preamble (paste at top of every chip dispatch)

You are agent ZZ`<N>` working on the Jacobian Lean Challenge.

## Setup (work directly in the canonical checkout — local verification is the source of truth)

Work in `/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge` on a feature
branch off `main`:

```
cd "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge"
git checkout main && git pull
git checkout -b feat/zz<N>-chip
```

Independent `/tmp/agent-X-jacobian` clones are only needed when dispatching
*parallel* sub-agents whose changes would otherwise entangle the parent
checkout. For serial work, edit `main`-tracking branches directly.

## Anti-bloat gates (PROJECT-CRITICAL — added 2026-05-23 after audit showed the
repo ballooned from a ~130k LOC budget toward 200k+ via paraphrase chips)

Before writing ANY new code, the chip must pass ALL of the following gates. If
it fails any, REJECT the chip and report `✗ REJECTED` with the failing gate.

0. **Discharge-map gate (added 2026-06-10 after the second duplicate-work
   incident).** Before chipping toward ANY named Prop, search
   `DISCHARGE_MAP.md` (repo root) for the target. It is auto-generated
   from the compiled environment — for every repo-defined Prop/structure
   it lists every declaration concluding it, with the repo-named Props
   each one still consumes (`needs: []` ⟹ heuristically unconditional).
   If the target already has a discharge whose `needs` you can supply,
   the chip is a DUPLICATE — REJECT. If the map looks stale relative to
   recent commits, regenerate first (warm `.olean`s, ~1 min, panic-safe):
   `LEAN_NUM_THREADS=1 lake env lean tools/DischargeMap.lean`.
   Hand-maintained docs (HANDOFF_*, OPEN.md, in-file docstrings saying
   "left as a future chip") are NOT trustworthy for open/closed status —
   two incidents (2026-05-24 reverse-leg, 2026-06-10 bilinear ℝ-LI) came
   from exactly that staleness. The discharge map is the ground truth;
   prose docs are for routes and rationale only.
   At session END, regenerate the map and commit it with your chip so
   the next session inherits fresh state.

1. **Paraphrase gate.** A chip that takes an existing theorem `T_old (h₁ ... hₙ)` and
   ships `T_new (h₁ ... hₖ)` for `k < n` by auto-discharging the dropped
   hypotheses via a NEW named hypothesis (typeclass, structural Prop, etc.)
   is **a paraphrase, not progress**. The net sorry-pile is unchanged: each
   hypothesis named is a deferred classical theorem with a different
   docstring. REJECT unless the chip also discharges at least one named
   hypothesis on a non-trivial X (i.e. NOT under `Subsingleton ω` and NOT
   on a specific X you also ship the instance for in the same session).

2. **Parallel-route gate.** If there already exists a route to the same
   conclusion in tree (e.g. `Item14ForRiemannSphereVia2InputChip.lean` already
   closes item 14 on RS), a new chip that produces a *parallel* route via
   different intermediate machinery is **net negative** — it adds
   maintenance surface, instance-search collisions, and zero new
   closure. REJECT unless the new route closes something the existing
   route does NOT close (and document precisely what).

3. **Named-hypothesis gate.** A chip that introduces a new `class` /
   `structure` / `def Prop` whose discharge is "left as an exercise"
   (i.e. an instance is shipped only for `RiemannSphere` and `ℂ ⧸ L`, or
   only under `Subsingleton ω`) is a renamed sorry. REJECT unless either:
   (a) the new name discharges an EXISTING named hypothesis on arbitrary
   X by classical proof, or (b) the chip's same-session companion discharges
   the new name on arbitrary X.

4. **Per-X instance gate.** Concrete `RiemannSphere` / `ℂ ⧸ L` instance
   chips are fine for end-to-end smoke tests, but each one is +50-150 LOC
   that doesn't move the general-X frontier. CAP: at most ONE per-X
   instance chip per session, and only if explicitly needed for a
   downstream theorem you're proving the same session.

5. **Minimum substantive content.** A chip's `proven:` field in the final
   report should be a SUBSTANTIVE CLASSICAL STATEMENT (in plain math), not
   a Lean-level rephrasing. Examples of substantive:
   "Every holomorphic 1-form on a compact connected complex 1-manifold with
   `H¹(X, 𝒪) = 0` is exact" / "Riemann-Roch dim bound on the Riemann
   sphere". Examples of NOT substantive: "Combines chip C and chip D into
   typeclass instance" / "Bridges named hypothesis A to named hypothesis
   B" / "Item 14 reduced from 3 inputs to 2 inputs". REJECT the latter.

6. **mathlib-first gate.** Before writing ANY new infrastructure, grep
   mathlib for the closest existing lemma (`grep -rn "$concept" .lake/packages/mathlib/`).
   The repo has been re-inventing manifold theory; this stops. If a
   mathlib lemma is within ~50 LOC of glue away, use it. If not, document
   the gap in the chip's `proven:` field as "uses mathlib X, bridges to
   our Y" and keep the new infrastructure to <300 LOC.

7. **Item-14-progress gate.** If your chip is on item 14 (in any
   formulation), it must either (a) remove a `sorry` from
   `Basic.lean`, (b) discharge a classical hypothesis on arbitrary X
   (NOT just RS/T_L/Subsingleton), or (c) prove a substantive lemma
   from mathlib that is one of the named open hypotheses (`hSP`,
   `h_bslb`, `FiniteDimensional ℂ (HolomorphicOneForm X)`). Anything
   else is REJECT.

## Discipline rules (non-negotiable)

- **NEVER push until locally verified green.** This is the merge-gate
  invariant. Specifically:
  - **If your chip introduces new top-level declarations** (new `def`,
    `lemma`, `theorem`, `instance`), the merge gate is a successful
    full-project `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake
    build` (NOT just `lake env lean`). The single-file `lake env lean`
    check does **not** detect duplicate `namespace.declName`
    registrations between your new file and other files in the project
    — it elaborates one file at a time against cached `.olean`s and
    misses the kernel-level uniqueness check that CI enforces. Two real
    incidents in 2026-05-12 (zzMER, zz264/267) shipped duplicates that
    every single-file check passed but full-build and CI rejected.
    Allow ~5-30 min for the full build depending on `.lake` warmth.
  - **If your chip is iterating on the proof body of a name already in
    main**, `LEAN_NUM_THREADS=1 lake env lean <file>` is sufficient and
    is the fast loop (~3-30s warm).
  - Either way: pushing un-verified code wastes parent-session merge
    work, pollutes the branch with broken commits, and is exactly the
    "iterate on CI" anti-pattern the local-verify policy was set up to
    eliminate. If your local verification cannot run (cold clone,
    bootstrap not finished), DO NOT PUSH. Report `✗ STUCK` instead.
  - The corollary: once the appropriate verification IS green, push and
    immediately return your `✓ DONE` report. CI watching is explicitly
    removed from the discipline.
- **No `sorry`, no `axiom`** anywhere in the code you write.
- **Do not use `ω` as a binder name.** Lean 4.30 reserves `ω` as the omega-tactic token; `(ω : ...)` produces "unexpected token 'ω'; expected '_' or identifier" errors. Use `om`, `form`, `oneform`, or any ASCII identifier instead. (`ω` is fine inside docstrings or as `open scoped` notation; just not as a `def`/`theorem`/`fun`/`have` binder.)
- **No signature changes** to anything outside the new file you create.
- **Local verification = `taskpolicy lake build <target>`** for cold clones,
  or `LEAN_NUM_THREADS=1 lake env lean FILE.lean` for warm-cache iteration.
  - On a **warm-cache** checkout (canonical, or a /tmp clone after first
    full build): `LEAN_NUM_THREADS=1 lake env lean
    JacobianChallenge/Manifold/YOUR_FILE.lean` returns in ~3-30s per file.
    Reads existing `.olean`s, no writes, no panic. Use this for fast
    chip iteration **on existing declaration bodies only**. Before any
    push that introduces a new top-level name, follow with a full
    `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build` —
    `lake env lean` does NOT detect cross-file duplicate names.
  - On a **cold /tmp clone**: do NOT try `lake env lean` first — it errors
    on missing `.olean`s for transitive imports. Instead, bootstrap and
    verify in one step:
    ```
    taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build \
      JacobianChallenge.Manifold.YOUR_FILE 2>&1 | tail -5
    ```
    First run takes ~10-15 min (mathlib `.olean` cache compile from
    source). Subsequent runs in the same clone are incremental and fast.
    **`lake build` IS the verification** — if it completes "Build
    completed successfully", the file is verified. No need for a separate
    `lake env lean` step.
  - What's still banned: `lake build` *without* `taskpolicy`-throttle,
    `lake exe cache get`, multi-threaded `lake env lean`, and `du`/`find`
    on `.lake`. The previous version of this preamble said "NEVER run
    `lake env lean` locally" — that's the pre-2026-05-10 policy and is
    stale.
- **After the new file is locally green**, single-file-check the top-level
  manifest `JacobianChallenge.lean` (or `lake build` the manifest target)
  to catch import-ordering / namespace issues.
- **No CI watching.** Once local verification is green, push and return.
  The parent session does not wait for repo CI; merging is unblocked
  the moment your local build succeeds.
- **On any local error:** read the message inline (single-file elaboration
  prints it at the bottom of stdout), fix the specific issue, re-run the
  single-file check. There is no per-cycle cap on local iteration —
  cycles are free.
- **Do NOT merge to main.** Just push the branch and report.

## Required final-message format

Every chip ends with EXACTLY ONE of these two responses:

```
✓ DONE
branch: feat/zz<N>-chip
HEAD: <sha>
local-verify: success (new file + manifest both single-file-green)
file: <path>
proven: <one-line summary>
residuals: <one-line summary or "none">
```

OR

```
✗ STUCK
branch: feat/zz<N>-chip
HEAD: <sha>
last local error: <verbatim final lines from `lake env lean` stdout>
blocker: <one specific concrete reason — missing mathlib lemma name, type mismatch we can't unify, etc.>
```

Do NOT end with: "I'll wait for the monitor", "Waiting for CI", or any other
terminator that doesn't carry the structured fields above. The dispatcher
will read your final message — make it informative.

## Goal (chip-specific, fill in below the preamble)
