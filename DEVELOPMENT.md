# Development guide

Inherited from sister projects `sqg-lean-proofs` and `ns-lean-proofs`. This
file is the **primary reference** for anyone contributing Lean code to this
repo on a local workstation.

---

## ⚠️ CRITICAL — READ FIRST — Prevents kernel panic on Apple Silicon ⚠️

This project is developed primarily on an M2 Ultra Mac, which has a
known **SoC watchdog kernel-panic mode** when the APFS daemon (`apfsd`)
saturates. Every panic forces a full system restart and loses unsaved
work. The triggers are predictable and avoidable.

### NEVER run these locally

- ❌ `du -sh` / `du -h` on `.lake/`, `.lake/packages/mathlib/`, or any
  directory with tens of thousands of `.olean` files → **instant panic**.
- ❌ `find` with heavy predicates or `-exec` on big trees (`~`, `/Volumes/`).
- ❌ `lake build` *without* `taskpolicy` throttle — the **finalization
  phase** (flushing `.olean`, `.ilean`, `.c`, trace files across the dep
  graph) is many small writes in a narrow window and saturates apfsd.
  Throttled form `taskpolicy -b nice -n 19 lake build` is safe.
- ❌ `lake exe cache get` — leantar decompresses ~8,000 small files in a
  burst. Every time.
- ❌ Multi-threaded `lake env lean FILE.lean` — parallel `.olean` writes
  same pattern as `lake build`. Stick to `LEAN_NUM_THREADS=1`.
- ❌ `sed -i` on multi-thousand-line files (use the Edit tool instead).
- ❌ `cp -r` or `mv` of large trees (`.lake` is ~7 GB).
- ❌ Back-to-back heavy file operations without pause.

### Always do these

- ✅ **For single-file verification (primary loop):**
  `LEAN_NUM_THREADS=1 lake env lean JacobianChallenge/YOUR_FILE.lean`.
  Reads existing `.olean`s and elaborates the file in memory without
  writing artifacts. Warm cache: ~3-30s per check, no panic. Iterate as
  many times as needed — local cycles are free. This is the primary
  verification, not CI.
- ✅ **For full-graph build (when really needed):**
  `taskpolicy -b nice -n 19 lake build`. Throttled background priority
  keeps apfsd under saturation threshold. Only run this when you need
  fresh `.olean`s for many files (e.g. after a mathlib bump) — for
  per-file chip iteration, the single-file `lake env lean` is enough.
- ✅ For size info: `ls -ldh /path` (directory itself, no recursion)
  or `df -h .` (free space only).
- ✅ For finding files: use `Glob` / file browser, not `find`.
- ✅ For big copies: `rsync --bwlimit=30M`.

### If you forget and the machine panics

Symptom in `/Library/Logs/DiagnosticReports/`:
- `panic-base-*.panic`: `"Unexpected SoC (system) watchdog reset occurred"`
- `apfsd_*.cpu_resource.diag`: `apfsd` at ~70-80% CPU for 100+ seconds

Restart the machine. Any unsaved Lean work is gone.

---

## Local-verify-primary workflow

**Policy (post-2026-05-10):** single-file `LEAN_NUM_THREADS=1 lake env
lean FILE.lean` is the primary verification for **iterating on the body**
of an already-named declaration. It type-checks against the existing
`.olean` cache without writing artifacts, returns in ~3-30s on a warm
cache, and does not panic the M3 Ultra. CI is now **optional** final
verification, not the merge gate. (The previous version of this file
enforced CI-as-default because `lake env lean` was assumed unsafe;
that turned out to be only the multi-threaded form. `LEAN_NUM_THREADS=1`
is safe.)

### ⚠️ Critical: pre-push merge gate for new top-level declarations

`lake env lean FILE.lean` and the manifest single-file check **do not
detect duplicate `namespace.declName` registrations across files** —
they elaborate one file at a time against pre-built `.olean`s, where
the kernel has already cached both names without re-checking
uniqueness. Two real incidents on 2026-05-12 (zzMER, zz264/267) added
declarations that collided with names already in
`Divisor/PrincipalDivisor.lean`; every local single-file check passed,
yet CI rejected the merge with
`environment already contains 'JacobianChallenge.foo' from <other file>`.

**Therefore: any chip that introduces a new top-level `def` / `lemma` /
`theorem` / `instance` must be gated by a full
`taskpolicy -b nice -n 19 lake build` (or a `lake build <new-target>` +
`lake build JacobianChallenge` pair) on the canonical checkout before
push.** The full build elaborates every file fresh, so it surfaces
duplicate-name conflicts at module-load time the way CI does. Allow
~5-15 min on a warm `.lake`, ~30 min if the chip touches a heavily
imported module.

`lake env lean` remains fine for *iterating on the proof body of an
existing declaration* (whose name already lives in main). It is
insufficient for *adding new names*.

### Editing main-tracking branches directly

For one chip at a time, work directly in the canonical checkout on a
feature branch:

```
cd path/to/jacobian-lean-challenge
git checkout main && git pull
git checkout -b feat/<chip-name>
```

Then the per-iteration loop is:

1. Edit the new file (or the manifest, for the import line).
2. `LEAN_NUM_THREADS=1 lake env lean JacobianChallenge/YOUR_FILE.lean`.
3. Read the inline error (printed at the bottom of stdout); fix; repeat.
4. When the new file is green, also single-file-verify
   `JacobianChallenge.lean` (the top-level manifest) to catch
   import-ordering / namespace issues.
5. **Pre-push gate for chips with new top-level declarations:**
   run `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build`
   (full project) and confirm "Build completed successfully". This is
   the only way to surface duplicate-name conflicts with declarations
   already living in other files. Skip this step only if the chip is
   pure proof-body iteration on names already in main.
6. Commit.
7. Push the branch. CI is then optional — only watch it if you want a
   final confidence check after local-green.


### When to fall back to CI

The single-file local check is sufficient for type-checking the new
file plus its imports. Use CI only when:

- You're touching a cross-cutting import (something in
  `JacobianChallenge.lean` or a heavily-imported module) and want a
  smoke-test that no downstream file breaks under cumulative
  elaboration. The local check verifies *your file*'s imports, but not
  every consumer of a definition you renamed.
- The mathlib pin changed (`lean-toolchain` or `lake-manifest.json`)
  and your `.lake` cache is from before the bump.
- You want a final independent confirmation before declaring a chip
  done.

In those cases, push the branch and watch the `build` job:

```sh
gh run watch --exit-status
```

`docgen` and `dedupe-caches` jobs are allowed to fail / hang and do not
gate correctness.

### The typical loop

1. Write code in modular blocks, **≤ 150 lines per commit** ideally.
2. After each significant change:
   ```
   LEAN_NUM_THREADS=1 lake env lean JacobianChallenge/Manifold/YOUR_FILE.lean
   ```
   Read the error inline, fix, re-run. ~3-30s per cycle.
3. Once green locally, also single-file-check the manifest:
   ```
   LEAN_NUM_THREADS=1 lake env lean JacobianChallenge.lean
   ```
4. `git add`, `git commit`, `git push`. If you want CI confirmation,
   `gh run watch --exit-status`; otherwise the local check is enough.

### Cache hygiene

The workflow includes a `dedupe-caches` job after build that keeps only
the newest cache per key. This prevents the 10 GB per-repo Actions
cache quota from filling up from duplicate `lean-action` cache saves.
No manual action needed.

### Expected cold-build time

First CI run on a new mathlib rev fetches ~8,000 files and decompresses
them — takes ~2-3 min for cache fetch alone, plus 1-2 min actual build.
Subsequent runs against the same mathlib rev hit the cache and complete
in ~2 min.

### Known benign failures

- **`Create Release` workflow fails on the very first push of a branch.**
  The action's `create-tags.sh` tries to diff between `0000...0000` (no
  parent) and the first commit, which is not a valid git range on an
  orphan branch. Subsequent pushes with a real parent work fine. The
  release workflow only re-fires on `lean-toolchain` changes anyway.
- **`docgen-action` hangs or times out.** It's `continue-on-error: true`
  with a 10-minute timeout. Safe to ignore for correctness; the
  `leanprover/lean-action@v1` step status is what determines build
  success.

---

## Diagnostic workflow for Lean timeouts and loops

**When you see `(deterministic) timeout at whnf, maximum number of
heartbeats (N) has been reached`:**

**DO NOT** iteratively bump `maxHeartbeats` from 200k → 400k → 800k.
Nine times out of ten it's a reducibility loop on a definitionally-
computable term applied to symbolic arguments, not a "just slow"
budget problem. Each bump wastes ~4 minutes of CI time and teaches
you nothing.

### Step 1: Run the built-in diagnostic

Add these three `set_option` lines directly above the failing `theorem`:

```lean
set_option maxHeartbeats 400000 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
theorem your_failing_theorem ... := ...
```

Then run `LEAN_NUM_THREADS=1 lake env lean <file>` locally. The stdout
will contain output like:

```
info: File.lean:L:0: [diag] Diagnostics
  [reduction] unfolded declarations (max: N, num: K):
    [reduction] Int.rec ↦ 3573405
    [reduction] Multiset.ofList ↦ 80553
    [reduction] Add.add ↦ 1949293
    ...
```

**Read it literally.** Declarations unfolded 100k+ times ARE the loop.
Don't architect-guess; patch the specific declarations named.

### Step 2: Common root causes + fixes

| Pattern in diagnostic | Root cause | Fix |
|---|---|---|
| `Int.rec`, `Nat.rec`, `List.range` in millions | Finset/Multiset-valued definition with symbolic index | `attribute [local irreducible] yourDef` scoped to the slow section |
| `HAdd.hAdd`, `Add.add`, `NatCast.natCast` in millions | Arithmetic inside symbolic index computation | Same — find the def being unfolded |
| `Quot.lift`, `Multiset.ofList`, `Multiset.map` | Finset/Multiset normalization | Same |
| `dite`, `decidable_of_iff`, `Int.decEq`, `Multiset.decidableForallMultiset` | DecidableEq instance-synthesis loop | **See Step 3 below** |
| One specific instance showing 50k+ uses | Instance-search loop | Mark the class/def irreducible, or provide the instance explicitly |

### Step 3: `DecidableEq` instance-mismatch (structure-field gotcha)

**Telltale signature:**

```
h_bound has type   ... @yourStruct inst✝ A B cf cg ...
but is expected to have type   ... @yourStruct
  (fun a b ↦ Fintype.decidablePiFintype a b) A B cf cg ...
```

**Root cause.** The structure's field was elaborated at
structure-declaration time with the *default* `DecidableEq` instance
auto-synthesized by mathlib. But the consuming theorem has
`[DecidableEq ...]` as an *explicit class parameter*, which introduces
a fresh `inst✝`. The two instances are propositionally equal (it's a
Prop) but not definitionally equal, and structure-field unification
hits `isDefEq`.

**Fix (apply by default):**

1. **Remove `[DecidableEq ...]` from the theorem's signature.**
2. Add `classical` in the body if the proof genuinely needs it
   (e.g., calling a helper that takes `[DecidableEq]`).
3. Lean's default instance synthesis then picks the same instance at
   every use site, and field assignment matches.

**Pre-`lake env lean` checklist:**

1. Does this theorem call `.bound` or `.something` on a structure whose
   field type involves `DecidableEq`-parametrised terms?
2. If yes, is `[DecidableEq ...]` in MY signature?
3. If yes to both → remove it, use `classical` in the body.

### Step 4: `convert` instead of `exact` for instance mismatches

If a helper auto-synthesizes e.g. `Fintype.decidablePiFintype` but the
theorem's `[DecidableEq]` parameter is `inst✝`, they are subsingleton-
equal but not definitionally equal under irreducibility.

**Bridge with `convert`**, not `exact`:

```lean
-- failed: exact myHelper (params...)
convert myHelper (params...)
```

`convert` falls back to subsingleton reasoning for instance arguments
where `exact` requires strict definitional equality. Use `convert`
only at leaf instance-mismatch spots — never at an Lp-valued top-level
goal, which triggers `.default` transparency.

### Step 5: What NOT to do

- **Don't** iterate heartbeat bumps. Wastes CI time, diagnoses nothing.
- **Don't** restructure the proof ("split into smaller theorems",
  "unbundle structure projections") without diagnostic data. You're
  guessing. One v0.4.38-era session in a sister project hit 10+ CI
  failures trying architectural fixes before the 1-minute diagnostic
  run pinpointed the actual loop. Cost comparison:

  | Approach | Cycles | Wall time (CI era) | Wall time (local-verify era) |
  |---|---|---|---|
  | Architectural guesses without diagnostics | 9 | ~40 min | ~5 min |
  | Run `set_option diagnostics true` once | 1 | ~4 min | ~15s |
  | Apply fix from diagnostic output | 1 | ~4 min | ~15s |

  Local single-file verification compressed this loop ~10×, but the
  lesson is unchanged: **diagnostic first, architectural guesses never.**

---

## Lean 4 / mathlib gotchas (reference)

Collected from sister-project experience. Not exhaustive; add new ones
here as they come up.

### Imports must precede all other content

```lean
-- copyright comment (plain -- lines, OK above imports)
import Mathlib

/-!
# Module doc-comment goes HERE, after imports.
-/

namespace ...
```

Putting a `/-! ... -/` module doc-comment before `import Mathlib` gives
`invalid 'import' command, it must be used at the beginning of the file`.
**Common first-time mistake.** Always: copyright `--` comment, then
imports, then `/-! ... -/` doc, then `namespace`.

### `ENNReal` over `ℝ≥0∞`

Prefer the ASCII form `ENNReal` in type annotations. The Unicode
`ℝ≥0∞` has caused "expected token" + instance-synthesis cascade at
tokenization time in past work.

### Useful diagnostic `set_option`s

- `set_option diagnostics true` + `set_option diagnostics.threshold 100`
  — primary tool, prints unfold/use counts at declaration close.
- `#defeq_abuse in theorem Foo ...` — identifies definitional abuse
  where implicit arguments force `.default` transparency.
- `count_heartbeats in <decl>` (from `Mathlib.Util.CountHeartbeats`) —
  auto-suggests a heartbeat budget or reveals loops.
- `set_option trace.Meta.isDefEq true` — verbose defeq trace, use on
  a minimal reproducer only (CI logs truncate).
- `set_option trace.Meta.synthInstance true` — trace instance
  resolution specifically.
- `set_option backward.isDefEq.respectTransparency false` — restore
  pre-4.29 transparency behavior if needed.

### Mathlib name lookups can be wrong

The model and tactics will sometimes invent plausible-sounding mathlib
names that don't exist. Examples from sister projects:
`memℓp_two_iff_summable_sq_norm` (real name: `memℓp_gen_iff`),
`Real.exp_log_sum` (real name: doesn't exist, you want
`Real.exp_log` + `Real.exp_add`).

When CI says `unknown identifier 'X'`, do not assume the name is wrong
in mathlib. First search for the actual mathlib name with `loogle` /
`exact?` / `apply?`. Bad lemma-name guesses are a characteristic AI
failure mode and the only filter is build failure or human review.

---

## Pre-commit checklist

Before every `git push`:

1. **Single-file green?** `LEAN_NUM_THREADS=1 lake env lean
   JacobianChallenge/Manifold/YOUR_FILE.lean` exits 0 with no error
   output.
2. **Manifest single-file green?** `LEAN_NUM_THREADS=1 lake env lean
   JacobianChallenge.lean` exits 0 (catches import-ordering /
   namespace issues that the new-file check alone misses).
3. **Imports at top?** All `.lean` files must have `import` statements
   at the very top (above any `/-! ... -/` doc-comment).
4. **Tiny commit?** Ideally ≤ 150 lines changed per commit.
5. **No banned ops?** Verified you didn't run `lake build` without
   `taskpolicy`, `lake exe cache get`, or `du` on `.lake`.
6. **If consuming a structure field**: check for the `DecidableEq`
   class-parameter pattern (Step 3 above). If your theorem takes
   `[DecidableEq ...]` and calls `.field` on a structure, remove the
   parameter and use `classical`.
7. **No `sorry` / `axiom`?** `grep -nE "sorry|axiom\s" <new file>` is
   empty (and matches your honest intent).
8. **No upstream signature changes?** `git diff main -- <listed
   upstream files>` is empty for any file outside the new one.
9. **Commit message descriptive?** Reference the lemma name or item
   number from `OPEN.md` that landed. Ex.: `"Close OPEN item 15:
   ofCurve_self"`.

---

## Repository structure

See [`README.md`](./README.md) and [`OPEN.md`](./OPEN.md) for the
mathematical structure and roadmap.

In brief:

```
JacobianChallenge/
  Basic.lean              -- Buzzard's challenge signature, verbatim
  ...                     -- additional modules added on demand
```

Each new file must be added to the top-level `JacobianChallenge.lean`
import list for it to be included in the library build.

## Validation note

This repo's authors are not Riemann-surface specialists. AI-orchestrated
formalization has characteristic error modes that compilation alone does
not catch:

- Wrong sign / normalization conventions when the source uses a different one
- Hallucinated lemma names that look plausible but don't exist in mathlib
- Citing a "standard result" for a theorem that actually requires real work
- Conflating two related but inequivalent definitions (e.g., topological vs.
  holomorphic genus)
- Hypothesis ordering or vacuity that makes the theorem trivially true

The intended validation mechanism is mathlib PR review for prerequisites
that are independently useful (`Divisor`, `HolomorphicOneForm`, etc.) —
see `OPEN.md` "Mathlib-prerequisite candidates" — and Buzzard's own
review of the final challenge submission. CI-green is necessary but not
sufficient for correctness.
