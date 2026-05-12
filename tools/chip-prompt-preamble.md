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
