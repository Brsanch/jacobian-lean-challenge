/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.FiberPullback

set_option diagnostics.threshold 100

/-! # Fibre cardinality and finiteness through composition -/

namespace JacobianChallenge

namespace Div

variable {X Y Z : Type*}

/-- **Fibre of a composition decomposes by intermediate fibre.** -/
lemma comp_fibre_eq_biUnion (f : X → Y) (g : Y → Z) (z : Z) :
    (g ∘ f) ⁻¹' {z} = ⋃ y ∈ g ⁻¹' {z}, f ⁻¹' {y} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp,
             Set.mem_iUnion, exists_prop]
  exact ⟨fun h => ⟨f x, h, rfl⟩, fun ⟨y, hy, hxy⟩ => hxy ▸ hy⟩

/-- **Composition of finite fibres is finite.** -/
lemma comp_fibre_finite
    {f : X → Y} {g : Y → Z}
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite) (z : Z) :
    ((g ∘ f) ⁻¹' {z}).Finite := by
  rw [comp_fibre_eq_biUnion]
  exact Set.Finite.biUnion (hg z) (fun y _ => hf y)

end Div

end JacobianChallenge
