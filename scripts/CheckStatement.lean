import JacobianChallenge
import Lean

/-!
# Statement-integrity check (modelled on anthropics/formal-math)

For every user-facing declaration of the challenge spec module
`JacobianChallenge.Basic` this prints
  * `STMT <name> :: <fully elaborated type>` (pp.all-style, so notation/coercion
    changes cannot hide a statement change), and
  * `AXIOMS <name> :: <axioms the declaration transitively depends on>`.

`scripts/check_statement.sh` diffs the STMT lines against the frozen copy in
`scripts/frozen/statements.txt` and fails on any axiom outside
`propext`, `Classical.choice`, `Quot.sound`.
-/

open Lean Meta Elab Command

elab "#statement_audit" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `JacobianChallenge.Basic
    | throwError "module JacobianChallenge.Basic not found"
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx && !n.isInternalDetail then
      names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let ci ← getConstInfo n
    let fmt ← liftTermElabM <| withOptions (fun o => o
        |>.setBool `pp.all true
        |>.setBool `pp.proofs true) <| ppExpr ci.type
    let s := (toString fmt).replace "\n" " "
    let s := " ".intercalate ((s.splitOn " ").filter (· ≠ ""))
    logInfo m!"STMT {n} :: {s}"
    let axs ← collectAxioms n
    let axs := (axs.map toString).qsort (· < ·)
    logInfo m!"AXIOMS {n} :: {", ".intercalate axs.toList}"

#statement_audit
