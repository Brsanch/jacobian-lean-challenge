/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez

# Discharge-map generator

Mechanical ground truth against doc staleness: walks the compiled
environment and, for EVERY repo-defined Prop / structure (a potential
"named hypothesis"), lists EVERY repo declaration whose conclusion is
that Prop (directly or under `Nonempty`), together with the repo-named
Props it still consumes as hypotheses.

Run (reads warm .oleans, ~seconds — panic-safe):

  LEAN_NUM_THREADS=1 lake env lean tools/DischargeMap.lean

Output: regenerates `DISCHARGE_MAP.md` at the repo root.

DO NOT import this file from the library manifest.

Motivation: two duplicate-work incidents (2026-05-24 reverse-leg,
2026-06-10 bilinear ℝ-LI) were caused by stale handoff docs claiming
work was open when theorems concluding the target Prop already existed
in tree. The compiled environment cannot go stale.
-/
import Lean
import JacobianChallenge

open Lean Meta

namespace DischargeMap

def isRepoModule (m : Name) : Bool :=
  (`JacobianChallenge).isPrefixOf m

/-- Names that are clearly auto-generated implementation details. -/
def isNoise (n : Name) : Bool :=
  n.isInternalDetail
    || n.components.any (fun c =>
        match c with
        | .str _ s =>
          s == "mk" || s == "rec" || s == "recOn" || s == "casesOn"
            || s == "brecOn" || s == "below" || s == "noConfusion"
            || s == "noConfusionType" || s == "injEq" || s == "sizeOf_spec"
            || s == "ofNat" || s == "ibelow" || s == "binductionOn"
            || s.startsWith "proof_" || s.startsWith "match_"
            || s.startsWith "eq_" || s.startsWith "_"
        | _ => false)

/-- Head constant of the conclusion of a (possibly ∀-quantified) type;
unwraps a `Nonempty` wrapper. -/
def conclusionHead (ty : Expr) : MetaM (Option Name) :=
  forallTelescope ty fun _ body => do
    let fn := body.getAppFn
    match fn.constName? with
    | some `Nonempty =>
      match body.getAppArgs[0]? with
      | some a =>
        -- the wrapped type may itself be ∀-quantified
        forallTelescope a fun _ inner => pure inner.getAppFn.constName?
      | none => pure none
    | other => pure other

/-- Repo-Prop heads appearing among the hypotheses of `ty`. -/
def hypothesisHeads (ty : Expr) (targets : NameSet) : MetaM (List Name) :=
  forallTelescope ty fun fvars _ => do
    let mut acc : List Name := []
    for fv in fvars do
      let bty ← inferType fv
      let h ← conclusionHead bty
      if let some hn := h then
        if targets.contains hn && !acc.contains hn then
          acc := acc.concat hn
    pure acc

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  pure env.header.moduleNames[idx.toNat]!

def run : MetaM Unit := do
  let env ← getEnv
  -- Pass 1: collect targets — repo-defined Props (defs) and inductives/structures.
  let mut targets : NameSet := {}
  let mut targetList : Array (Name × Name) := #[]  -- (name, module)
  for (n, ci) in env.constants.toList do
    if isNoise n then continue
    let some m := moduleOf env n | continue
    unless isRepoModule m do continue
    match ci with
    | .defnInfo v =>
      let isProp ← forallTelescope v.type fun _ b => pure b.isProp
      if isProp then
        targets := targets.insert n
        targetList := targetList.push (n, m)
    | .inductInfo _ =>
      targets := targets.insert n
      targetList := targetList.push (n, m)
    | _ => pure ()
  -- Pass 2: collect discharges — repo decls whose conclusion head is a target.
  let mut discharges : Std.HashMap Name (Array (Name × Name × List Name)) := {}
  for (n, ci) in env.constants.toList do
    if isNoise n then continue
    let some m := moduleOf env n | continue
    unless isRepoModule m do continue
    match ci with
    | .thmInfo _ | .defnInfo _ =>
      let some head ← conclusionHead ci.type | pure ()
      if targets.contains head && head != n && !head.isPrefixOf n then
        let needs ← hypothesisHeads ci.type targets
        let needs := needs.filter (· != head)
        let arr := discharges.getD head #[]
        discharges := discharges.insert head (arr.push (n, m, needs))
    | _ => pure ()
  -- Emit markdown.
  let mut out := ""
  out := out ++ "# DISCHARGE MAP (auto-generated — do NOT edit)\n\n"
  out := out ++ "Regenerate: `LEAN_NUM_THREADS=1 lake env lean tools/DischargeMap.lean`\n\n"
  out := out ++ "For every repo-defined Prop/structure: every repo declaration whose\n"
  out := out ++ "conclusion is that Prop (directly or under `Nonempty`). `[needs: …]`\n"
  out := out ++ "lists repo-named Props consumed as hypotheses — empty brackets mean\n"
  out := out ++ "no repo-named-Prop hypothesis (heuristically unconditional; check\n"
  out := out ++ "instance arguments and per-X specialization by eye).\n\n"
  out := out ++ "**BEFORE writing any chip: search this file for the target Prop.**\n\n"
  let sorted := targetList.qsort (fun a b => a.1.toString < b.1.toString)
  -- Section 1: zero-discharge targets (the honest open pile).
  out := out ++ "## Targets with ZERO in-tree discharges\n\n"
  for (t, m) in sorted do
    if (discharges.getD t #[]).isEmpty then
      out := out ++ s!"- `{t}` ({m})\n"
  -- Section 2: full map.
  out := out ++ "\n## Full map (targets with at least one discharge)\n\n"
  for (t, m) in sorted do
    let ds := discharges.getD t #[]
    unless ds.isEmpty do
      out := out ++ s!"### `{t}` ({m})\n\n"
      for (d, dm, needs) in ds.qsort (fun a b => a.1.toString < b.1.toString) do
        let needsStr := if needs.isEmpty then "[]"
          else "[" ++ ", ".intercalate (needs.map (s!"`{·}`")) ++ "]"
        out := out ++ s!"- `{d}` ({dm}) — needs: {needsStr}\n"
      out := out ++ "\n"
  IO.FS.writeFile "DISCHARGE_MAP.md" out
  IO.println s!"DISCHARGE_MAP.md written: {targetList.size} targets."

end DischargeMap

#eval DischargeMap.run
