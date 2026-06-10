/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.Single
import JacobianChallenge.Divisor.EvalSum

set_option linter.unusedSectionVars false

/-! # Effective extraction: divisors with a single pole decompose into points

The divisor-counting workhorse for the chord-and-tangent proof of Abel's
converse on the complex torus.

* `Div.exists_effective_decomposition` — an **effective** divisor (all
  values `≥ 0`) of degree `k` is a sum of `k` single-point divisors.
* `Div.exists_singles_decomposition` — a degree-`0` divisor with value
  `-k` at a point `x₀` and `≥ 0` elsewhere equals
  `∑ i, single (g i) - k • single x₀` for some `g : Fin k → X` avoiding
  `x₀`.
* `Div.singles_decomposition_apply` — the pointwise value of such a
  decomposition is a fiber count, whence
  `Div.exists_index_of_one_le_apply` (a point of value `≥ 1` appears
  among the `g i`).
* `Div.evalSum_singles_decomposition` — the support-weighted sum of the
  decomposition in an ambient topological abelian group.

Applied downstream with `D := principalDivisorMap f` for `f` one of the
descended Weierstrass functions: the pole order at `0` pins `k`
(`2` for `℘ − c`, `3` for the chord function), the residue theorem
supplies `degree = 0`, and off-pole effectivity comes from analyticity.

No `sorry`, no `axiom`. -/

noncomputable section

namespace JacobianChallenge

namespace Div

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [DecidableEq X]

/-! ## Effective divisors of degree `k` are sums of `k` points -/

/-- **Effective decomposition.** An effective divisor of degree `k` is a sum
of `k` single-point divisors, each placed at a point of the support. -/
lemma exists_effective_decomposition (k : ℕ) :
    ∀ E : Div X, (∀ q : X, 0 ≤ (E : X → ℤ) q) → E.degree = (k : ℤ) →
      ∃ g : Fin k → X, (∀ i, (E : X → ℤ) (g i) ≠ 0)
        ∧ E = ∑ i, Div.single (g i) := by
  induction k with
  | zero =>
    intro E hnn hdeg
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    -- Degree-0 effective divisor is zero.
    have hall : ∀ x ∈ E.supportFinset, (E : X → ℤ) x = 0 := by
      have hsum : ∑ x ∈ E.supportFinset, (E : X → ℤ) x = 0 := hdeg
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => hnn x)).mp hsum
    have hzero : ∀ x : X, (E : X → ℤ) x = 0 := by
      intro x
      by_cases hx : x ∈ E.supportFinset
      · exact hall x hx
      · exact apply_eq_zero_of_notMem_supportFinset hx
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    ext x
    simpa using hzero x
  | succ k ih =>
    intro E hnn hdeg
    -- There is a point of value ≥ 1.
    have hex : ∃ q₀ : X, 1 ≤ (E : X → ℤ) q₀ := by
      by_contra hcon
      push Not at hcon
      have hall0 : ∀ q : X, (E : X → ℤ) q = 0 := fun q =>
        le_antisymm (by have := hcon q; omega) (hnn q)
      have hdeg0 : E.degree = 0 := by
        unfold degree
        exact Finset.sum_eq_zero (fun x _ => hall0 x)
      rw [hdeg0] at hdeg
      omega
    obtain ⟨q₀, hq₀⟩ := hex
    -- Subtract a point and recurse.
    set E' : Div X := E - Div.single q₀ with hE'
    have hE'_apply : ∀ q : X,
        (E' : X → ℤ) q = (E : X → ℤ) q - (if q = q₀ then 1 else 0) := by
      intro q
      rw [hE']
      simp
    have hnn' : ∀ q : X, 0 ≤ (E' : X → ℤ) q := by
      intro q
      rw [hE'_apply q]
      by_cases hq : q = q₀
      · rw [if_pos hq, hq]
        omega
      · rw [if_neg hq]
        have := hnn q
        omega
    have hdeg' : E'.degree = (k : ℤ) := by
      have h1 : degreeHom E' = degreeHom E - degreeHom (Div.single q₀) :=
        map_sub degreeHom E (Div.single q₀)
      have h2 : (degreeHom (Div.single q₀) : ℤ) = 1 := degree_single q₀
      have h3 : (degreeHom E : ℤ) = ((k : ℤ) + 1) := by
        rw [degreeHom_apply, hdeg]
        push_cast
        ring
      rw [degreeHom_apply] at h1
      rw [h1, h2, h3]
      ring
    obtain ⟨g', hg'ne, hg'sum⟩ := ih E' hnn' hdeg'
    refine ⟨Fin.cons q₀ g', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · -- i = 0: value at q₀ is ≥ 1.
        rw [Fin.cons_zero]
        omega
      · -- i = j+1: value at g' j is ≥ E' (g' j) ≥ 1.
        intro j
        rw [Fin.cons_succ]
        have h1 : (E' : X → ℤ) (g' j) ≠ 0 := hg'ne j
        have h2 : 0 ≤ (E' : X → ℤ) (g' j) := hnn' (g' j)
        have h3 := hE'_apply (g' j)
        by_cases hq : g' j = q₀
        · rw [if_pos hq] at h3
          omega
        · rw [if_neg hq] at h3
          omega
    · -- E = single q₀ + ∑ single (g' j) = single q₀ + E' = E.
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hg'sum, hE']
      abel

/-! ## Divisors with one pole of order `k` -/

/-- **Singles decomposition.** A degree-`0` divisor with value `-k` at `x₀`
and effective elsewhere is `∑ i, single (g i) - k • single x₀` with all
`g i ≠ x₀`. -/
lemma exists_singles_decomposition (D : Div X) (x₀ : X) (k : ℕ)
    (h0 : (D : X → ℤ) x₀ = -(k : ℤ)) (hdeg : D.degree = 0)
    (hpos : ∀ q : X, q ≠ x₀ → 0 ≤ (D : X → ℤ) q) :
    ∃ g : Fin k → X, (∀ i, g i ≠ x₀) ∧
      D = (∑ i, Div.single (g i)) - (k : ℤ) • Div.single x₀ := by
  set E : Div X := D + (k : ℤ) • Div.single x₀ with hE
  have hE_apply : ∀ q : X,
      (E : X → ℤ) q = (D : X → ℤ) q + (k : ℤ) * (if q = x₀ then 1 else 0) := by
    intro q
    rw [hE]
    simp [mul_comm]
  have hE_x₀ : (E : X → ℤ) x₀ = 0 := by
    rw [hE_apply x₀, if_pos rfl, h0]
    ring
  have hnn : ∀ q : X, 0 ≤ (E : X → ℤ) q := by
    intro q
    by_cases hq : q = x₀
    · rw [hq, hE_x₀]
    · rw [hE_apply q, if_neg hq]
      have := hpos q hq
      omega
  have hdegE : E.degree = (k : ℤ) := by
    have h1 : degreeHom E
        = degreeHom D + (k : ℤ) • degreeHom (Div.single x₀) := by
      rw [hE]
      rw [map_add, map_zsmul]
    have h2 : (degreeHom (Div.single x₀) : ℤ) = 1 := degree_single x₀
    rw [degreeHom_apply] at h1
    rw [h1, h2, degreeHom_apply, hdeg]
    simp
  obtain ⟨g, hgne, hgsum⟩ := exists_effective_decomposition k E hnn hdegE
  refine ⟨g, ?_, ?_⟩
  · intro i hgi
    apply hgne i
    rw [hgi]
    exact hE_x₀
  · rw [← hgsum, hE]
    abel

/-! ## Pointwise values of a singles decomposition -/

/-- The pointwise value of `∑ i, single (g i) - k • single x₀` is a fiber
count minus the pole indicator. -/
lemma singles_decomposition_apply {k : ℕ} (g : Fin k → X) (x₀ q : X) :
    (((∑ i, Div.single (g i)) - (k : ℤ) • Div.single x₀ : Div X) : X → ℤ) q
      = (({i | g i = q} : Finset (Fin k)).card : ℤ)
        - (k : ℤ) * (if q = x₀ then 1 else 0) := by
  classical
  have hsum : ((∑ i, Div.single (g i) : Div X) : X → ℤ) q
      = ∑ i : Fin k, (if q = g i then 1 else 0 : ℤ) := by
    rw [Function.locallyFinsuppWithin.coe_sum]
    simp
  have hcard : (∑ i : Fin k, (if q = g i then 1 else 0 : ℤ))
      = (({i | g i = q} : Finset (Fin k)).card : ℤ) := by
    rw [Finset.card_filter]
    push_cast
    congr 1
    ext i
    by_cases h : g i = q
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  simp only [Function.locallyFinsuppWithin.coe_sub,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [hsum, hcard]
  simp

/-- A point of value `≥ 1` (off the pole) appears among the decomposition
points. -/
lemma exists_index_of_one_le_apply {k : ℕ} {g : Fin k → X} {x₀ : X}
    {D : Div X}
    (hdecomp : D = (∑ i, Div.single (g i)) - (k : ℤ) • Div.single x₀)
    {u : X} (hu : u ≠ x₀) (h1 : 1 ≤ (D : X → ℤ) u) :
    ∃ i, g i = u := by
  classical
  rw [hdecomp, singles_decomposition_apply g x₀ u, if_neg hu] at h1
  have hcard : 1 ≤ (({i | g i = u} : Finset (Fin k)).card : ℤ) := by omega
  have hne : ({i | g i = u} : Finset (Fin k)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨i, hi⟩ := hne
  exact ⟨i, by simpa using hi⟩

/-! ## Evaluation sum of a singles decomposition -/

variable [AddCommGroup X]

/-- The support-weighted evaluation sum of
`∑ i, single (g i) - k • single x₀` is `∑ i, g i - k • x₀`. -/
lemma evalSum_singles_decomposition {k : ℕ} (g : Fin k → X) (x₀ : X) :
    evalSum ((∑ i, Div.single (g i)) - (k : ℤ) • Div.single x₀ : Div X)
      = (∑ i, g i) - (k : ℤ) • x₀ := by
  have h1 : evalSumHom ((∑ i, Div.single (g i))
        - (k : ℤ) • Div.single x₀ : Div X)
      = evalSumHom (∑ i, (Div.single (g i) : Div X))
        - (k : ℤ) • evalSumHom (Div.single x₀ : Div X) := by
    rw [map_sub, map_zsmul]
  rw [evalSumHom_apply] at h1
  rw [h1, map_sum]
  simp

end Div

end JacobianChallenge

end
