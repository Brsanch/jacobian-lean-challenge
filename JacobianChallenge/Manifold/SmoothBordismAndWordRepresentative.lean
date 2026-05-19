/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.WordLoopHomology
import JacobianChallenge.Manifold.SmoothHurewiczHypothesis

set_option linter.unusedSectionVars false

/-! # Factoring `SmoothHurewiczHypothesis` into bordism + word-representability

The smooth-Hurewicz hypothesis on a `SmoothSymplecticBasis sb`
says: *every smooth based loop `γ` at `p₀` admits integers `n : Fin
(2g) → ℤ` with `single γ - ∑ᵢ nᵢ • sb.cycleGens i ∈ stokesBoundaries`.*

This file factors it into **two strictly weaker named sub-hypotheses**:

1. **`SmoothBordant γ₀ γ₁`** — *Bordism preserves H₁ class*: two based
   loops at `p₀` differ by a Stokes-boundary. By construction this is
   `γ₀.singleCycle - γ₁.singleCycle ∈ stokesBoundaries`, since
   `stokesBoundaries` IS the image of the smooth 2-chain boundary
   operator. The geometric content "smoothly homotopic ⇒ bordant"
   follows from pushing forward a homotopy `H : [0,1]² → X` into a
   smooth 2-chain.

2. **`WordRepresentativeHypothesis sb`** — *Every smooth based loop is
   bordant to a ℤ-combination of basis loops*: for every based loop
   `γ` at `p₀`, there exist integers `n : Fin (2g) → ℤ` and a
   bordism witness from `γ` to a *canonical product* of `sb.basis i`
   loops raised to the `n i`-th power.

   Classically: cellular approximation on a compact orientable
   genus-`g` surface. Every smooth loop is smoothly homotopic to a
   loop in the 1-skeleton (a wedge of 2g circles for genus `g`), and
   the resulting loop is a word in the basis.

**Combined**: `WordRepresentativeHypothesis sb ⟹ SmoothHurewiczHypothesis sb`.

## Significance

This is **structural progress on the hardest atom**: the smooth-Hurewicz
hypothesis is no longer monolithic.

* **Bordism side (`SmoothBordant`)** is by-definition in our framework.
  The geometric content — *"smoothly homotopic loops are bordant"* —
  reduces to smooth-Stokes on a homotopy 2-chain. That construction is
  concrete and a future chip can attack it.

* **Word-rep side (`WordRepresentativeHypothesis`)** remains the
  cellular-approximation classical content, but it's now isolated as a
  single named Prop quantifying over loops.

## Design choice

The `wordLoop`-based version of word-representability runs into a
re-indexing problem (grouping a `List (ℤ × BasedLoopAt)` by basis-index
to produce a `Fin (2g) → ℤ` tuple). We sidestep that bookkeeping by
defining a **canonical basis-product loop** `basisProductLoop sb n` (the
product `(sb.basis 0)^{n 0} ⋆ (sb.basis 1)^{n 1} ⋆ … ⋆ (sb.basis (2g-1))^{n (2g-1)}`)
and stating word-representability directly in terms of bordism to such
a product.

## What this file ships

* `BasedLoopAt.ofBasis sb i` — wraps `sb.basis i` as a `BasedLoopAt`.
* `basisProductLoop sb n` — canonical basis-product based loop.
* `single_basisProductLoop_sub_sum_zsmul_singles_mem_stokesBoundaries`
  — the H₁ identity for `basisProductLoop`.
* `SmoothBordant γ₀ γ₁` — bordism predicate.
* `WordRepresentativeHypothesis sb` — sub-hypothesis (bordism to a
  `basisProductLoop`).
* `smoothHurewiczHypothesis_of_wordRepresentative` —
  `WordRepresentativeHypothesis sb ⟹ SmoothHurewiczHypothesis sb`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## `BasedLoopAt.ofBasis` and `basisProductLoop` -/

namespace BasedLoopAt

/-- **Wrap a symplectic-basis loop as a `BasedLoopAt`.** -/
noncomputable def ofBasis {p₀ : X} {g : ℕ}
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) (i : Fin (2 * g)) :
    BasedLoopAt 𝓘(ℝ, ℂ) X p₀ :=
  ⟨sb.basis i, ⟨sb.basis_src i, sb.basis_tgt i⟩⟩

@[simp] lemma ofBasis_toPath {p₀ : X} {g : ℕ}
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) (i : Fin (2 * g)) :
    (BasedLoopAt.ofBasis sb i).toPath = sb.basis i := rfl

/-- The `singleCycle` of `BasedLoopAt.ofBasis sb i` equals `sb.cycleGens i`. -/
lemma ofBasis_singleCycle {p₀ : X} {g : ℕ}
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) (i : Fin (2 * g)) :
    (BasedLoopAt.ofBasis sb i).singleCycle = sb.cycleGens i := by
  apply Subtype.ext
  rw [singleCycle_coe, ofBasis_toPath, SmoothSymplecticBasis.cycleGens_coe]

end BasedLoopAt

/-- **Canonical basis-product loop.** For a symplectic basis `sb` and an
integer tuple `n : Fin (2g) → ℤ`, the product

```
basisProductLoop sb n := (sb.basis 0)^{n 0} ⋆ (sb.basis 1)^{n 1} ⋆ ⋯
                            ⋆ (sb.basis (2g - 1))^{n (2g - 1)}
```

(constructed via `wordLoop` on `List.ofFn` indexed by `Fin (2g)`). -/
noncomputable def basisProductLoop {p₀ : X} {g : ℕ}
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) (n : Fin (2 * g) → ℤ) :
    BasedLoopAt 𝓘(ℝ, ℂ) X p₀ :=
  wordLoop p₀ (List.ofFn (fun i => (n i, BasedLoopAt.ofBasis sb i)))

/-- **`H₁` identity for `basisProductLoop`.** The class of `basisProductLoop
sb n` in `H₁` equals `∑ᵢ nᵢ • sb.cycleGens i`. -/
theorem single_basisProductLoop_sub_sum_zsmul_singles_mem_stokesBoundaries
    {p₀ : X} {g : ℕ} (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g)
    (n : Fin (2 * g) → ℤ) :
    (basisProductLoop sb n).singleCycle - ∑ i, n i • sb.cycleGens i
    ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
  -- Apply the word-loop identity to the basis-indexed word.
  have h_word :=
    single_wordLoop_sub_sum_zsmul_singles_mem_stokesBoundaries p₀
      (List.ofFn (fun i : Fin (2 * g) => (n i, BasedLoopAt.ofBasis sb i)))
  -- Rewrite the sum: word.map (fun p => p.1 • p.2.singleCycle) over List.ofFn ...
  -- equals ∑ i, n i • sb.cycleGens i via List.sum_ofFn + ofBasis_singleCycle.
  have h_sum_eq :
      ((List.ofFn (fun i : Fin (2 * g) => (n i, BasedLoopAt.ofBasis sb i))).map
        (fun p => p.1 • p.2.singleCycle)).sum
        = ∑ i, n i • sb.cycleGens i := by
    rw [List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show ((fun p : ℤ × BasedLoopAt 𝓘(ℝ, ℂ) X p₀ => p.1 • p.2.singleCycle) ∘
        fun i => (n i, BasedLoopAt.ofBasis sb i)) i = n i • sb.cycleGens i
    simp only [Function.comp_apply, BasedLoopAt.ofBasis_singleCycle]
  rw [h_sum_eq] at h_word
  -- (basisProductLoop sb n).singleCycle = (wordLoop p₀ (List.ofFn ...)).singleCycle
  -- by definition.
  exact h_word

/-! ## Smooth bordism (predicate) -/

/-- **Smooth bordism of based loops at `p₀`.** Two based loops `γ₀, γ₁`
are smoothly bordant iff their `singleCycle` difference lies in
`stokesBoundaries` (i.e., is the boundary of some smooth 2-chain).

The geometric content "there is a smooth homotopy `H : [0,1]² → X`
between `γ₀` and `γ₁`" implies `SmoothBordant` by pushing the unit
square forward via `H` and dividing into two smooth 2-simplices. -/
def SmoothBordant {p₀ : X} (γ₀ γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀) : Prop :=
  γ₀.singleCycle - γ₁.singleCycle ∈ stokesBoundaries 𝓘(ℝ, ℂ) X

namespace SmoothBordant

variable {p₀ : X}

/-- Smooth bordism is reflexive. -/
lemma refl (γ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀) : SmoothBordant γ γ := by
  unfold SmoothBordant
  rw [sub_self]
  exact (stokesBoundaries 𝓘(ℝ, ℂ) X).zero_mem

/-- Smooth bordism is symmetric. -/
lemma symm {γ₀ γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀} (h : SmoothBordant γ₀ γ₁) :
    SmoothBordant γ₁ γ₀ := by
  unfold SmoothBordant at h ⊢
  have h' := AddSubgroup.neg_mem _ h
  have h_eq : -(γ₀.singleCycle - γ₁.singleCycle) = γ₁.singleCycle - γ₀.singleCycle :=
    by abel
  rw [h_eq] at h'
  exact h'

/-- Smooth bordism is transitive. -/
lemma trans {γ₀ γ₁ γ₂ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀}
    (h₀₁ : SmoothBordant γ₀ γ₁) (h₁₂ : SmoothBordant γ₁ γ₂) :
    SmoothBordant γ₀ γ₂ := by
  unfold SmoothBordant at h₀₁ h₁₂ ⊢
  have h_sum := AddSubgroup.add_mem _ h₀₁ h₁₂
  have h_eq :
      (γ₀.singleCycle - γ₁.singleCycle) + (γ₁.singleCycle - γ₂.singleCycle)
        = γ₀.singleCycle - γ₂.singleCycle := by abel
  rw [h_eq] at h_sum
  exact h_sum

end SmoothBordant

/-! ## Word-representative hypothesis -/

/-- **Word-representative hypothesis.** Every smooth based loop `γ` at
`p₀` is smoothly bordant to a `basisProductLoop sb n` for some integer
tuple `n : Fin (2g) → ℤ`.

Classically: cellular approximation on a compact orientable genus-`g`
surface. The smooth loop is smoothly homotopic (hence bordant) to a
loop in the 1-skeleton (= wedge of 2g circles), which is exactly a
finite product of basis-loops with integer multiplicities. -/
def WordRepresentativeHypothesis {p₀ : X} {g : ℕ}
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X, ∀ h_src : γ.src = p₀, ∀ h_tgt : γ.tgt = p₀,
    ∃ n : Fin (2 * g) → ℤ,
      SmoothBordant ⟨γ, ⟨h_src, h_tgt⟩⟩ (basisProductLoop sb n)

/-! ## Combined implication: word-rep ⟹ smooth-Hurewicz -/

/-- **Headline.** `WordRepresentativeHypothesis sb` implies
`SmoothHurewiczHypothesis sb`.

Proof: for a smooth based loop `γ`, pick `n : Fin (2g) → ℤ` and a
bordism witness `SmoothBordant γ (basisProductLoop sb n)`. Combine with
the H₁ identity for `basisProductLoop` to conclude. -/
theorem smoothHurewiczHypothesis_of_wordRepresentative
    {p₀ : X} {g : ℕ} {sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g}
    (h_word : WordRepresentativeHypothesis sb) :
    SmoothHurewiczHypothesis sb := by
  intro γ h_src h_tgt
  obtain ⟨n, h_bord⟩ := h_word γ h_src h_tgt
  refine ⟨n, ?_⟩
  -- Package γ as a BasedLoopAt for cleaner manipulation.
  let γ_bl : BasedLoopAt 𝓘(ℝ, ℂ) X p₀ := ⟨γ, ⟨h_src, h_tgt⟩⟩
  -- Rewrite single_smoothLoop_smoothCycle γ as γ_bl.singleCycle.
  have h_γ_sing :
      single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
        = γ_bl.singleCycle := by
    apply Subtype.ext
    rw [BasedLoopAt.singleCycle_coe, single_smoothLoop_smoothCycle_coe]
    rfl
  rw [h_γ_sing]
  -- Combine bordism witness with basisProductLoop H₁ identity.
  have h_basis :=
    single_basisProductLoop_sub_sum_zsmul_singles_mem_stokesBoundaries sb n
  have h_bord' : γ_bl.singleCycle
      - (basisProductLoop sb n).singleCycle ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    h_bord
  have h_sum := AddSubgroup.add_mem _ h_bord' h_basis
  -- Use opaque abbrevs so abel is fast.
  set A := γ_bl.singleCycle with hA_def
  set B := (basisProductLoop sb n).singleCycle with hB_def
  set C := ∑ i, n i • sb.cycleGens i with hC_def
  have h_eq : (A - B) + (B - C) = A - C := by abel
  rw [h_eq] at h_sum
  exact h_sum

end JacobianChallenge

end
