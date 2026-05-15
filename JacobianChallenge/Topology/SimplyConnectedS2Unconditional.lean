/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2EveryLoopHomotopicNonSurjective

/-! # `SimplyConnectedS2` is unconditional

Capstone composition: closes
`SimplyConnectedS2 = SimplyConnectedSpace JacobianChallenge.StandardS2`
unconditionally at the mathlib pin `8e3c989…`.

## Composition chain

```
everyS2LoopHomotopicToNonSurjective_holds       [chip 4j]
    ⇒  s2LoopHomotopicToAvoidingLoop_of_homotopicToNonSurjective ⇒ S2LoopHomotopicToAvoidingLoop   [chip 4e]
    ⇒  s2LoopsNullHomotopic_of_homotopicToAvoidingLoop ⇒ S2LoopsNullHomotopic                       [chip 3]
    ⇒  simplyConnectedS2_of_loops_nullhomotopic ⇒ SimplyConnectedS2                                 [chip 1]
```

## What is proved

* `simplyConnectedS2_holds` — `SimplyConnectedS2` is true, unconditionally.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace JacobianChallenge

/-- **`SimplyConnectedS2` is unconditional at this mathlib pin.**
Composes:
1. `everyS2LoopHomotopicToNonSurjective_holds` (chip 4j) — discharges
   the polygonal-approximation hypothesis.
2. `simplyConnectedS2_of_homotopicToNonSurjective` (chip 4e) — connects
   that hypothesis to `SimplyConnectedS2` via chips 1 + 3. -/
theorem simplyConnectedS2_holds : SimplyConnectedS2 :=
  simplyConnectedS2_of_homotopicToNonSurjective
    everyS2LoopHomotopicToNonSurjective_holds

end JacobianChallenge

end
