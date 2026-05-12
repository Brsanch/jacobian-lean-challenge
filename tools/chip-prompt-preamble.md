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

- **No `sorry`, no `axiom`** anywhere in the code you write.
- **Do not use `ω` as a binder name.** Lean 4.30 reserves `ω` as the omega-tactic token; `(ω : ...)` produces "unexpected token 'ω'; expected '_' or identifier" errors. Use `om`, `form`, `oneform`, or any ASCII identifier instead. (`ω` is fine inside docstrings or as `open scoped` notation; just not as a `def`/`theorem`/`fun`/`have` binder.)
- **No signature changes** to anything outside the new file you create.
- **Local single-file verification is the primary check.** Iterate with:
  ```
  LEAN_NUM_THREADS=1 lake env lean JacobianChallenge/YOUR_NEW_FILE.lean
  ```
  Returns in ~3-30s per file against a warm `.lake` cache, no panic. Lake
  reads existing `.olean`s and elaborates the file in memory without
  writing artifacts, so this is safe on M3 Ultra. Iterate until the file
  compiles green locally before any push. (The previous version of this
  preamble said "NEVER run `lake env lean` locally — Apple Silicon
  kernel-panics"; that was the pre-2026-05-10 policy and is now stale.
  Single-file `LEAN_NUM_THREADS=1` is safe. What's still banned: `lake
  build` without `taskpolicy`-throttle, `lake exe cache get`,
  multi-threaded `lake env lean`, and `du`/`find` on `.lake`.)
- **After the new file is locally green**, also single-file-check the
  top-level manifest `JacobianChallenge.lean` (which imports your module)
  to catch import-ordering / namespace issues that single-file-checking
  the new file alone misses.
- **CI is now optional final verification, not the merge gate.** If you
  want one for confidence after the local checks pass, push and
  `gh run watch --exit-status`. Otherwise just push and report.
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
