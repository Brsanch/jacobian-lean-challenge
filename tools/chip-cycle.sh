#!/usr/bin/env bash
# chip-cycle.sh — orchestrator for parallel feat/zz*-chip branches.
#
# Operates from the main checkout of the jacobian-lean-challenge repo.
# Produces a status table of all in-flight chip branches, then attempts
# to merge any branch whose CI `build` job is green. Conflicts in
# `JacobianChallenge.lean` (always import-line only) are auto-resolved
# by accepting both sides.
#
# Usage:
#   ./tools/chip-cycle.sh status     # just show table, no actions
#   ./tools/chip-cycle.sh merge      # status + auto-merge green branches
#   ./tools/chip-cycle.sh errors <branch>  # print build errors for one branch
#
# Exit codes:
#   0 — clean
#   1 — at least one branch failed; see output

set -euo pipefail

cmd="${1:-status}"
cd "$(git rev-parse --show-toplevel)"

git fetch origin --quiet

list_chip_branches() {
  git for-each-ref --format='%(refname:short)' refs/remotes/origin/feat/zz*-chip \
    | sed 's|^origin/||'
}

build_conclusion() {
  # Args: branch
  # Honors GH API rate limits: if `gh` returns 403, surface "rate-limited"
  # so the caller can back off rather than retrying tightly.
  local branch="$1"
  local list_out
  list_out=$(gh run list --branch "$branch" --limit 1 --json databaseId 2>&1) || true
  if [[ "$list_out" == *"rate limit exceeded"* ]]; then
    echo "rate-limited"; return
  fi
  local run_id
  run_id=$(echo "$list_out" | python3 -c "import sys,json; data=json.load(sys.stdin); print(data[0]['databaseId'] if data else '')" 2>/dev/null || echo "")
  if [[ -z "$run_id" ]]; then echo "no-ci"; return; fi
  local view_out
  view_out=$(gh run view "$run_id" --json jobs 2>&1) || true
  if [[ "$view_out" == *"rate limit exceeded"* ]]; then
    echo "rate-limited"; return
  fi
  echo "$view_out" \
    | python3 -c "import sys,json
try:
  jobs = json.load(sys.stdin).get('jobs', [])
  b = [j for j in jobs if j['name']=='build']
  if b:
    print(b[0]['status'] if not b[0]['conclusion'] else b[0]['conclusion'])
  else:
    print('no-build')
except Exception:
  print('parse-err')" 2>/dev/null
}

ahead_of_main() {
  local branch="$1"
  git log --oneline "origin/main..origin/$branch" 2>/dev/null | wc -l | tr -d ' '
}

behind_main() {
  local branch="$1"
  git log --oneline "origin/$branch..origin/main" 2>/dev/null | wc -l | tr -d ' '
}

resolve_manifest_conflict() {
  # JacobianChallenge.lean conflict resolver: accept BOTH sides of every
  # <<<<<<< / ======= / >>>>>>> block (additive imports never collide
  # semantically; we just keep both lines).
  local file="JacobianChallenge.lean"
  if ! grep -q '^<<<<<<< ' "$file"; then return 0; fi
  python3 <<'PY'
import re
fn = "JacobianChallenge.lean"
with open(fn) as f: lines = f.readlines()
out, i = [], 0
while i < len(lines):
    if lines[i].startswith('<<<<<<<'):
        head = []
        i += 1
        while not lines[i].startswith('======='):
            head.append(lines[i]); i += 1
        i += 1
        their = []
        while not lines[i].startswith('>>>>>>>'):
            their.append(lines[i]); i += 1
        i += 1
        out.extend(head)
        out.extend(their)
    else:
        out.append(lines[i]); i += 1
with open(fn, 'w') as f: f.writelines(out)
PY
  git add "$file"
  echo "  resolved import-line conflict (kept both sides)" >&2
}

attempt_merge() {
  local branch="$1"
  echo "--- merging $branch ---"
  # Belt-and-suspenders: abort any in-progress merge from a prior chip
  # whose conflict resolution didn't complete cleanly. Otherwise `git pull`
  # below errors with "Pulling is not possible because you have unmerged
  # files" and every subsequent merge in this run is wedged.
  if [[ -f .git/MERGE_HEAD ]]; then
    git merge --abort 2>/dev/null || true
  fi
  git checkout main --quiet
  git pull origin main --quiet
  if git merge --no-ff "origin/$branch" --no-edit 2>&1 | grep -q 'CONFLICT'; then
    resolve_manifest_conflict
    if git ls-files -u | grep -q .; then
      echo "  ! non-import conflict remains; aborting merge"
      git merge --abort
      return 1
    fi
    git commit --no-edit
  fi
  if ! git push origin main; then
    echo "  ! git push failed; merge not landed"
    return 1
  fi
  echo "  merged"
}

case "$cmd" in
  watch)
    # Loop until all in-flight chips reach terminal status, then run merge.
    # Backs off on GH API rate-limit (sleeps 5 min instead of 60s).
    while true; do
      any_pending=0
      rate_limited=0
      for branch in $(list_chip_branches); do
        ahead=$(ahead_of_main "$branch")
        if [[ "$ahead" == "0" ]]; then continue; fi
        behind=$(behind_main "$branch")
        if [[ "$behind" -gt 50 ]]; then continue; fi
        conclusion=$(build_conclusion "$branch")
        if [[ "$conclusion" == "rate-limited" ]]; then
          rate_limited=1; any_pending=1; break
        fi
        if [[ "$conclusion" == "in_progress" || "$conclusion" == "queued" ]]; then
          any_pending=1
          break
        fi
      done
      if [[ "$any_pending" == "0" ]]; then break; fi
      if [[ "$rate_limited" == "1" ]]; then
        echo "$(date +%H:%M:%S) rate-limited; backing off 5 min..."
        sleep 300
      else
        echo "$(date +%H:%M:%S) waiting for chips to settle..."
        sleep 60
      fi
    done
    exec "$0" merge
    ;;
  status|merge)
    printf "%-40s %-7s %-7s %-12s %s\n" BRANCH AHEAD BEHIND BUILD ACTION
    failed=0
    for branch in $(list_chip_branches); do
      ahead=$(ahead_of_main "$branch")
      if [[ "$ahead" == "0" ]]; then continue; fi
      behind=$(behind_main "$branch")
      conclusion=$(build_conclusion "$branch")
      action="-"
      # Stale branches (>50 commits behind) are likely dead; refuse auto-merge.
      if [[ "$behind" -gt 50 ]]; then
        action="STALE-skip"
      elif [[ "$cmd" == "merge" && "$conclusion" == "success" ]]; then
        if attempt_merge "$branch" >&2; then
          action="merged"
        else
          action="merge-failed"
          failed=1
        fi
      elif [[ "$conclusion" == "failure" ]]; then
        action="run: errors $branch"
        failed=1
      fi
      printf "%-40s %-7s %-7s %-12s %s\n" "$branch" "$ahead" "$behind" "$conclusion" "$action"
    done
    exit $failed
    ;;
  errors)
    branch="${2:-}"
    if [[ -z "$branch" ]]; then echo "usage: $0 errors <branch>"; exit 2; fi
    run_id=$(gh run list --branch "$branch" --limit 1 --json databaseId --jq '.[0].databaseId')
    echo "Build errors for $branch (run $run_id):"
    gh run view "$run_id" --log-failed 2>/dev/null | grep -E "error" | head -15 \
      | sed 's/^[^	]*	/  /'
    ;;
  *)
    echo "usage: $0 {status|merge|errors <branch>}" >&2
    exit 2
    ;;
esac
