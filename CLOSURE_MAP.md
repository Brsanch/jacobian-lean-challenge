# Closure Map — DEPRECATED 2026-05-23

This file was a per-item closure-prediction map from an earlier era of
the repo (HEAD `1fa030a`, Phase 0/1 plan). Its item statuses are now
**STALE** — multiple items it listed as OPEN/STUB are STRICT-CLOSED in
current `main`, and at least one (item 16) was specifically predicted
as "OPEN under Phase 1 — needs Abel's theorem" but was closed
unconditionally via a different route (`JacobianChallenge.ofCurve_inj_holds`)
that the prediction didn't anticipate.

Rather than maintain a stale parallel item table, this file has been
gutted. Authoritative current state lives in:

- **[`OPEN.md`](OPEN.md)** — per-item status table (the source of truth).
- **[`REPO_AUDIT.md`](REPO_AUDIT.md)** — full-repo deep audit (2026-05-23)
  with per-item chain-trace from `Basic.lean` sorries to their leaf
  named hypotheses.
- **[`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md)** — item-14 specific
  status (2 named hypotheses away).
- **[`C3_AUDIT.md`](C3_AUDIT.md)** — Jacobian-side / C3 cluster
  status (1 typeclass bundle away from 6+ item flips).

For older closure-prediction history, see `git log --oneline CLOSURE_MAP.md`.
