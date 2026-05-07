# Chip prompt preamble (paste at top of every chip dispatch)

You are agent ZZ`<N>` working on the Jacobian Lean Challenge.

## Setup (independent clone, never local lake build)

```
cd /tmp && rm -rf agent-ZZ<N>-jacobian
gh repo clone Brsanch/jacobian-lean-challenge agent-ZZ<N>-jacobian
cd /tmp/agent-ZZ<N>-jacobian
git checkout -b feat/zz<N>-chip origin/main
```

## Discipline rules (non-negotiable)

- **No `sorry`, no `axiom`** anywhere in the code you write.
- **No signature changes** to anything outside the new file you create.
- **CI-only verification.** NEVER run `lake build` or `lake env lean` locally — Apple Silicon kernel-panics under those.
- **After every push:** poll ONLY the `build` job. Do NOT wait for docgen / dedupe-caches / any other job — they take 5-10 extra minutes and the build job alone determines correctness. Use this exact polling command (copy-paste, replace `<N>`):
  ```bash
  RUN_ID=$(gh run list --branch feat/zz<N>-chip --limit 1 --json databaseId --jq '.[0].databaseId')
  while true; do
    STATUS=$(gh run view "$RUN_ID" --json jobs --jq '.jobs[] | select(.name=="build") | if .conclusion then .conclusion else .status end')
    case "$STATUS" in
      success|failure|cancelled|timed_out|action_required) echo "BUILD $STATUS"; break ;;
      *) sleep 30 ;;
    esac
  done
  ```
  Once you see `BUILD success` or `BUILD failure`, stop polling immediately. Do not wait for the run-level conclusion.
- **Verify CI green explicitly** by capturing `BUILD success` from the loop above.
- **On CI failure:** read the log (`gh run view <id> --log-failed | grep error`), fix the specific error in your clone, commit, push, re-poll. 6-cycle cap.
- **Do NOT merge to main.** Just push the branch and report.

## Required final-message format

Every chip ends with EXACTLY ONE of these two responses:

```
✓ DONE
branch: feat/zz<N>-chip
HEAD: <sha>
build: success (run <id>)
file: <path>
proven: <one-line summary>
residuals: <one-line summary or "none">
```

OR

```
✗ STUCK after <K> cycles
branch: feat/zz<N>-chip
HEAD: <sha>
last-build: <conclusion> (run <id>)
blocker: <one specific concrete reason — missing mathlib lemma name, type mismatch we can't unify, etc.>
```

Do NOT end with: "I'll wait for the monitor", "Waiting for CI", "jq exited", or any other terminator
that doesn't carry the structured fields above. The dispatcher will read your final message — make
it informative.

## Goal (chip-specific, fill in below the preamble)
