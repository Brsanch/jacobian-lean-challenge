/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2LoopsNullHomotopicReduction

/-! # `S2LoopHomotopicToAvoidingLoop` from "every loop is homotopic to a
non-surjective loop"

Final reduction in the Phase-3 smoothing arc. Replaces the
slightly chart-flavoured `S2LoopHomotopicToAvoidingLoop` with the
cleaner pure-topology statement `EveryS2LoopHomotopicToNonSurjective`:
every continuous loop in `StandardS2` is path-homotopic to a loop whose
image is not all of the sphere.

The reduction is short: if `image γ' ≠ univ`, pick `q ∉ image γ'`,
let `v := q.val`. Then `q = ⟨v, hv⟩` where `hv := mem_sphere_iff_norm`,
and `(stereographic hv).source = {q}ᶜ` so `γ'` avoids the chart pole.
The basepoint condition `x ∈ source` follows from `x ≠ q` (otherwise
`x = q` would be in `image γ'`, contradicting `q ∉ image γ'`).

After this chip, the *only* remaining classical content of
`SimplyConnectedS2` is the named hypothesis
`EveryS2LoopHomotopicToNonSurjective` — equivalent to the textbook
fact "continuous loops in `S²` can be approximated by polygonal /
simplicial / smooth loops, all of which have nowhere-dense image".

## What is proved

* `EveryS2LoopHomotopicToNonSurjective : Prop` — every loop in
  `StandardS2` is path-homotopic to a loop with proper image.
* `s2LoopHomotopicToAvoidingLoop_of_homotopicToNonSurjective` —
  this implies `S2LoopHomotopicToAvoidingLoop`.
* `simplyConnectedS2_of_homotopicToNonSurjective` — corollary:
  `SimplyConnectedS2` follows from the same hypothesis.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

/-- **Polygonal-approximation-style hypothesis.** Every continuous loop
in `StandardS2` is `Path.Homotopic` to a loop whose image is not all
of the sphere. -/
def EveryS2LoopHomotopicToNonSurjective : Prop :=
  ∀ (x : JacobianChallenge.StandardS2) (γ : Path x x),
    ∃ γ' : Path x x,
      Path.Homotopic γ γ' ∧ Set.range γ' ≠ (Set.univ : Set _)

/-- **Reduction theorem.** Given the polygonal-approximation-style
hypothesis, the chart-flavoured `S2LoopHomotopicToAvoidingLoop` holds:
any missed point on the sphere is the pole of a stereographic chart
whose source contains both the basepoint and the entire image of `γ'`.

Proof:
* Get `γ'` ≃ γ with `range γ' ≠ univ`.
* Pick `q ∈ univ ∖ range γ'`. Let `v := q.val`. Then `‖v‖ = 1` since
  `q ∈ sphere 0 1`, and `q = ⟨v, hv⟩` by `Subtype.ext`.
* `(stereographic hv).source = {q}ᶜ` (after `stereographic_source`).
* `x ≠ q`: otherwise `x = q = γ' 0 ∈ range γ'`, contradicting `q ∉ range γ'`.
* For every `t : unitInterval`, `γ' t ∈ range γ'`, so `γ' t ≠ q`, so
  `γ' t ∈ (stereographic hv).source`. -/
theorem s2LoopHomotopicToAvoidingLoop_of_homotopicToNonSurjective
    (h : EveryS2LoopHomotopicToNonSurjective) :
    S2LoopHomotopicToAvoidingLoop := by
  intro x γ
  obtain ⟨γ', hγγ', h_range_ne_univ⟩ := h x γ
  -- Pick q ∉ range γ'.
  obtain ⟨q, hq_notMem⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp h_range_ne_univ
  -- v := q.val, hv := q.property reinterpreted.
  have hv_norm : ‖q.val‖ = 1 := by
    have h := q.property
    rw [mem_sphere_iff_norm, sub_zero] at h
    exact h
  have h_q_eq : q = (⟨q.val, by rw [mem_sphere_iff_norm, sub_zero]; exact hv_norm⟩
      : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := Subtype.ext rfl
  refine ⟨q.val, hv_norm, ?_, γ', hγγ', ?_⟩
  · -- x ∈ (stereographic _).source, i.e. x ≠ ⟨q.val, _⟩ = q.
    rw [stereographic_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx_eq
    have hx_q : x = q := hx_eq.trans h_q_eq.symm
    apply hq_notMem
    exact ⟨0, γ'.source.trans hx_q⟩
  · -- ∀ t, γ' t ∈ (stereographic _).source.
    intro t
    rw [stereographic_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h_eq
    apply hq_notMem
    rw [← h_q_eq] at h_eq
    exact ⟨t, h_eq⟩

/-- **`SimplyConnectedS2` from the polygonal-approximation hypothesis.**
Composes `s2LoopHomotopicToAvoidingLoop_of_homotopicToNonSurjective`
with `simplyConnectedS2_of_homotopicToAvoidingLoop`. This is the
cleanest end-to-end reduction of `SimplyConnectedS2` to a single
pure-topology classical fact. -/
theorem simplyConnectedS2_of_homotopicToNonSurjective
    (h : EveryS2LoopHomotopicToNonSurjective) : SimplyConnectedS2 :=
  simplyConnectedS2_of_homotopicToAvoidingLoop
    (s2LoopHomotopicToAvoidingLoop_of_homotopicToNonSurjective h)

end JacobianChallenge

end
