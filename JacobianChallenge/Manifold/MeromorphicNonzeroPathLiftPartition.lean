/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroHurwitzPatching
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import Mathlib.Topology.UnitInterval

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Lebesgue-subdivision of the unit interval into Hurwitz-patching pieces

For `f : MeromorphicNonzero X` non-constant and a continuous path
`β : ℝ → RiemannSphere` whose unit-interval image lies in
`f.regularValueSet`, there is a finite monotone subdivision
`0 = t_0 ≤ t_1 ≤ ... ≤ t_n = 1` of `unitInterval` such that on each
subinterval `[t_i, t_{i+1}]`, `β` maps into the `W`-set of a
`HurwitzPatchingData` at a regular value.

This is the **first half** of the global path-lift argument: it
reduces the global lift to finitely many local lifts (chip 11), each
on a closed subinterval where `β` is contained in one Hurwitz base
neighbourhood.

## What ships

* `MeromorphicNonzero.exists_subdivision_hurwitzPatching` — the
  subdivision data.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Topology Manifold ContDiff unitInterval

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Lebesgue subdivision of `unitInterval` adapted to a regular path.**

For continuous `β` whose unit-interval image lies in `f.regularValueSet`,
the open cover `c (s : I) := β ⁻¹' (hurwitzPatchingData_at_regularValue
hnc (hβ_reg s)).W` of `I` admits, by
`exists_monotone_Icc_subset_open_cover_unitInterval`, a finite monotone
subdivision into closed subintervals each contained in one cover element. -/
theorem exists_subdivision_hurwitzPatching
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β)
    (hβ_reg : ∀ s : unitInterval, β s ∈ f.regularValueSet) :
    ∃ (t : ℕ → unitInterval), t 0 = 0 ∧ Monotone t ∧
      (∃ N, ∀ m ≥ N, t m = 1) ∧
      ∀ n : ℕ, ∃ s : unitInterval,
        ∀ r : unitInterval, r ∈ Icc (t n) (t (n+1)) →
          β r ∈ (f.hurwitzPatchingData_at_regularValue hnc (hβ_reg s)).W := by
  classical
  -- Open cover of unitInterval indexed by s ∈ unitInterval.
  set c : unitInterval → Set unitInterval := fun s =>
    (fun r : unitInterval => β r) ⁻¹' (f.hurwitzPatchingData_at_regularValue hnc (hβ_reg s)).W
    with hc_def
  -- Each c s is open: β restricted to unitInterval is continuous;
  -- preimage of open base set.
  have hc_open : ∀ s, IsOpen (c s) := by
    intro s
    have h_base_open : IsOpen
        (f.hurwitzPatchingData_at_regularValue hnc (hβ_reg s)).W :=
      (f.hurwitzPatchingData_at_regularValue hnc (hβ_reg s)).W_open
    -- Restrict β to unitInterval.
    have hβ_restrict_cont : Continuous (fun r : unitInterval => β r) :=
      hβ_cont.comp continuous_subtype_val
    exact h_base_open.preimage hβ_restrict_cont
  -- The cover covers univ.
  have hc_cover : (Set.univ : Set unitInterval) ⊆ ⋃ s, c s := by
    intro r _
    refine mem_iUnion.mpr ⟨r, ?_⟩
    show β r ∈ (f.hurwitzPatchingData_at_regularValue hnc (hβ_reg r)).W
    exact (f.hurwitzPatchingData_at_regularValue hnc (hβ_reg r)).y₀_mem_W
  -- Apply Lebesgue-subdivision lemma.
  obtain ⟨t, ht0, ht_mono, ⟨N, ht_eq1⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  refine ⟨t, ht0, ht_mono, ⟨N, ht_eq1⟩, ?_⟩
  intro n
  obtain ⟨s, hs_sub⟩ := ht_sub n
  refine ⟨s, ?_⟩
  intro r hr_mem
  have : r ∈ c s := hs_sub hr_mem
  exact this

end MeromorphicNonzero

end JacobianChallenge

end
