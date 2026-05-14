/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SimplyConnectedS2Reduction
import JacobianChallenge.Topology.S2PuncturedSimplyConnected

/-! # `S2LoopsNullHomotopic` reduced to the smoothing / general-position step

Combining:

* `Topology/SimplyConnectedS2Reduction.lean` — peels off the
  path-connectedness conjunct, leaving `S2LoopsNullHomotopic` as the
  remaining content of `SimplyConnectedS2`.
* `Topology/S2PuncturedSimplyConnected.lean` — proves
  `s2LoopAvoidingNullHomotopic` unconditionally for loops whose image
  misses some chosen `⟨v, hv⟩`.

This file glues the two: it pins the *only* remaining classical content
into a single named hypothesis, then proves the reduction.

## What remains named

`S2LoopHomotopicToAvoidingLoop : Prop` — for every basepoint `x` and
every loop `γ : Path x x` in `StandardS2`, there exists a unit vector
`v ∈ EuclideanSpace ℝ (Fin 3)` and a loop `γ'` such that

* `x` belongs to `(stereographic hv).source` (i.e. `x ≠ ⟨v, hv⟩`),
* `γ` is `Path.Homotopic` to `γ'`,
* every `γ' t` belongs to `(stereographic hv).source`.

This is the classical *general-position / smoothing* fact: any
continuous loop in `S²` is path-homotopic to one whose image misses at
least one point.

Standard proofs all need infrastructure not at this mathlib pin:

* **Polygonal approximation via Lebesgue number.** Cover `S²` by
  finitely many open sets each homeomorphic to `ℝ²` (e.g. complements
  of single points). Mathlib's `lebesgue_number_lemma` gives a
  partition of `[0,1]` such that each sub-interval maps into one such
  open set. On each sub-interval, replace `γ` by the geodesic between
  its endpoints — this gives `γ'` whose image is a finite union of
  geodesic arcs (one-dimensional in a two-dimensional sphere), hence
  not all of `S²`. The homotopy `γ ≃ γ'` is the small-hemisphere
  convex combination.
* **Simplicial / general position** approximation of `S²`. Requires
  CW / simplicial approximation, not at the pin.
* **Smooth approximation + Sard's theorem.** Requires smooth manifold
  approximation machinery, not at the pin.

The polygonal-approximation route is the most tractable continuation
chip after this reduction.

## What is proved

* `S2LoopHomotopicToAvoidingLoop` — the named hypothesis above.
* `s2LoopsNullHomotopic_of_homotopicToAvoidingLoop` — composition:
  given `S2LoopHomotopicToAvoidingLoop`, deduce
  `S2LoopsNullHomotopic` (and hence `SimplyConnectedS2` via
  `simplyConnectedS2_of_loops_nullhomotopic`).

After this chip, `SimplyConnectedS2` reduces to exactly one classical
content fact at this mathlib pin: `S2LoopHomotopicToAvoidingLoop`. All
intermediate steps (path-connectedness, stereographic projection,
contractibility of `(ℝ ∙ v)ᗮ`, path lifting through subtype inclusion,
homotopy transport) are discharged unconditionally.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace JacobianChallenge

/-- **Strict smoothing hypothesis (Phase-3 remainder).** Every loop in
`StandardS2` is path-homotopic to a loop whose image misses at least
one point. This is the general-position step that the polygonal /
simplicial / smooth-approximation arguments all converge on. It is the
only remaining classical content blocking
`SimplyConnectedS2` at this mathlib pin. -/
def S2LoopHomotopicToAvoidingLoop : Prop :=
  ∀ (x : JacobianChallenge.StandardS2) (γ : Path x x),
    ∃ (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1),
      x ∈ (stereographic hv).source ∧
        ∃ γ' : Path x x,
          Path.Homotopic γ γ' ∧
            ∀ t : unitInterval, γ' t ∈ (stereographic hv).source

/-- **Final composition theorem.** Given the smoothing hypothesis
`S2LoopHomotopicToAvoidingLoop`, every loop in `StandardS2` is
null-homotopic (`S2LoopsNullHomotopic`). The proof picks the witness
`γ'` and unit vector `v` provided by the hypothesis, applies
`s2LoopAvoidingNullHomotopic` to conclude `γ' ≃ Path.refl x`, and
transitively chains the homotopies `γ ≃ γ' ≃ Path.refl x`. -/
theorem s2LoopsNullHomotopic_of_homotopicToAvoidingLoop
    (h : S2LoopHomotopicToAvoidingLoop) : S2LoopsNullHomotopic := by
  intro x γ
  obtain ⟨v, hv, hx, γ', hγγ', h_avoid⟩ := h x γ
  have h_null : Path.Homotopic γ' (Path.refl x) :=
    s2LoopAvoidingNullHomotopic hv x hx γ' h_avoid
  exact hγγ'.trans h_null

/-- **`SimplyConnectedS2` from the smoothing hypothesis alone.**
Combines `s2LoopsNullHomotopic_of_homotopicToAvoidingLoop` with
`simplyConnectedS2_of_loops_nullhomotopic` (path-connectedness already
unconditional). This is the complete reduction of `SimplyConnectedS2`
to a single named classical fact at this pin. -/
theorem simplyConnectedS2_of_homotopicToAvoidingLoop
    (h : S2LoopHomotopicToAvoidingLoop) : SimplyConnectedS2 :=
  simplyConnectedS2_of_loops_nullhomotopic
    (s2LoopsNullHomotopic_of_homotopicToAvoidingLoop h)

end JacobianChallenge

end
