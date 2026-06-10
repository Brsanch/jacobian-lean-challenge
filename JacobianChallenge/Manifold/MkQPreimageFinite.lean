/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDescendPeriodic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Finiteness of divisor lifts in a bounded region

Pre-assembly glue for piece 5 of the forward-Abel contour argument
(`HANDOFF_TLDIVSUM.md`): the preimage under `mkQ : ℂ → ℂ ⧸ L` of a
finite set of classes, intersected with any bounded region, is finite
(`finite_mkQ_preimage_inter_isBounded`).

Per class `x` the preimage is the lattice translate family
`x.out + L`, and a discrete closed subgroup meets every bounded set in
finitely many points (`Metric.finite_isBounded_inter_isClosed`); the
finite union over `S` finishes.

This produces the finite exceptional set `Z` for
`abelIntegrand_decomposition` (the lifts of `supp (div f)` inside the
big ball ⊇ Π̄).

No `sorry`, no `axiom`. -/

noncomputable section

open Set

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Divisor lifts in a bounded region are finite**: the `mkQ`-preimage
of a finite set of classes meets every bounded subset of `ℂ` in a
finite set. -/
theorem finite_mkQ_preimage_inter_isBounded
    (S : Finset (ℂ ⧸ L)) {s : Set ℂ} (hs : Bornology.IsBounded s) :
    {z : ℂ | L.mkQ z ∈ S ∧ z ∈ s}.Finite := by
  classical
  -- Per class: the fiber over `x` inside `s` is a translate of the
  -- lattice points in a bounded set.
  have key : ∀ x : ℂ ⧸ L, {z : ℂ | L.mkQ z = x ∧ z ∈ s}.Finite := by
    intro x
    -- The shifted parameter region is bounded.
    have hbd : Bornology.IsBounded {w : ℂ | Quotient.out x + w ∈ s} := by
      obtain ⟨R, hR⟩ := hs.subset_closedBall (Quotient.out x)
      apply Bornology.IsBounded.subset (Metric.isBounded_closedBall
        (x := (0 : ℂ)) (r := R))
      intro w hw
      have h2 := hR hw
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa using h2
    -- The lattice meets the bounded region finitely.
    have hbase : ({w : ℂ | Quotient.out x + w ∈ s}
        ∩ (L : Set ℂ)).Finite := by
      change ({w : ℂ | Quotient.out x + w ∈ s}
        ∩ (L.toAddSubgroup : Set ℂ)).Finite
      haveI : DiscreteTopology L.toAddSubgroup :=
        (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed
        DiscreteTopology.isDiscrete hbd inferInstance
    -- The fiber embeds into the translate of that finite set.
    have himg : {z : ℂ | L.mkQ z = x ∧ z ∈ s}
        ⊆ (fun w : ℂ => Quotient.out x + w) ''
          ({w : ℂ | Quotient.out x + w ∈ s} ∩ (L : Set ℂ)) := by
      rintro z ⟨hzx, hzs⟩
      refine ⟨z - Quotient.out x, ⟨?_, ?_⟩, by ring⟩
      · show Quotient.out x + (z - Quotient.out x) ∈ s
        simpa using hzs
      · -- `z − x.out ∈ L`
        have h1 : L.mkQ (z - Quotient.out x) = 0 := by
          rw [map_sub, hzx, mkQ_out, sub_self]
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact (hbase.image _).subset himg
  -- Finite union over the classes of `S`.
  have hcover : {z : ℂ | L.mkQ z ∈ S ∧ z ∈ s}
      = ⋃ x ∈ S, {z : ℂ | L.mkQ z = x ∧ z ∈ s} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hmem, hzs⟩
      exact ⟨L.mkQ z, hmem, rfl, hzs⟩
    · rintro ⟨x, hx, hzx, hzs⟩
      exact ⟨hzx ▸ hx, hzs⟩
  rw [hcover]
  exact Set.Finite.biUnion S.finite_toSet (fun x _ => key x)

end ComplexTorus

end JacobianChallenge

end
