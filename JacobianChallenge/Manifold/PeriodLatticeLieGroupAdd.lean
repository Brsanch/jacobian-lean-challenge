/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeMkQContMDiff
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! # `LieAddGroup 𝓘(ℂ, Fin g → ℂ) ω ((Fin g → ℂ) ⧸ Λ)`

Discharges OPEN.md item 13 on the lattice-quotient construction
`G := (Fin g → ℂ) ⧸ L` for a discrete full-rank `ℤ`-lattice `L`.

## Proof structure

The atlas on `G` consists of local right-inverses of `L.mkQ`. For
`q : G`, `chartAt H q : G → E` (where `E := Fin g → ℂ`) is one such
right-inverse: on its source it sends a quotient class back to its
unique representative in `Metric.ball q.out (r/2)`.

For addition `+ : G × G → G`: on the open neighbourhood
`source(q₁) × source(q₂)` of `(q₁, q₂)`, we have

  `(a, b) ↦ a + b = mkQ (chartAt q₁ a + chartAt q₂ b)`

because `mkQ ∘ chartAt q = id` on `source(q)`, and `mkQ` is an additive
homomorphism. The RHS factors through smooth maps:

  * `chartAt q₁ , chartAt q₂` are `ContMDiffOn` on their sources
    (`contMDiffOn_chart`);
  * `+_E : E × E → E` is `ContDiff ℂ ω`, hence `ContMDiff` on the
    `chartedSpaceSelf E` structure;
  * `L.mkQ : E → G` is `ContMDiff` by
    `mkQ_contMDiff_complex` (companion file).

Combining yields `ContMDiffOn` of `+` on the open product source, hence
`ContMDiffAt` at every `(q₁, q₂)`, hence `ContMDiff`.

The proof for negation is identical with `E × E → E` replaced by
`E → E` and `q₁ + q₂` by `-q`.

The resulting `LieAddGroup` instance closes OPEN.md item 13 on the
quotient-by-lattice construction.
-/

open Set Metric

open scoped Manifold ContDiff

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable {g : ℕ}
variable (L : Submodule ℤ (Fin g → ℂ))
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ### Local agreement of `+` with the lifted form -/

/-- `chartAt _ q` is a local right-inverse of `L.mkQ`: on its source, the
quotient class of the chart's image equals the original class. -/
private lemma mkQ_chartAt_apply
    (q : (Fin g → ℂ) ⧸ L) {a : (Fin g → ℂ) ⧸ L}
    (ha : a ∈ (chartAt (Fin g → ℂ) q).source) :
    (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
        ((chartAt (Fin g → ℂ) q) a) = a := by
  -- The chart `chartAt _ q := (localChart L _ q.out).symm`, so the
  -- composition with `(localChart L _ q.out)` is the identity on its
  -- source.
  have h := (chartAt (Fin g → ℂ) q).left_inv ha
  -- `((chartAt _ q).symm).symm = chartAt _ q` on the partial-equiv level,
  -- and the `.symm` of `(localChart L _ q.out).symm` is
  -- `localChart L _ q.out`, whose forward is `L.mkQ`.
  -- So `h : (chartAt _ q).symm ((chartAt _ q) a) = a`.
  -- Now `(chartAt _ q).symm = (localChart L _ q.out).symm.symm =
  -- localChart L _ q.out`, and the latter agrees with `L.mkQ` on its
  -- source.
  show L.mkQ ((chartAt (Fin g → ℂ) q) a) = a
  -- The chart forward `(chartAt _ q) a` lies in `(chartAt _ q).target =
  -- (localChart L _ q.out).source = ball q.out (r/2)`. Inside that ball,
  -- `(localChart L _ q.out)` equals `L.mkQ` by definition.
  have h1 : (chartAt (Fin g → ℂ) q) a ∈ (chartAt (Fin g → ℂ) q).target :=
    (chartAt (Fin g → ℂ) q).map_source ha
  -- The chart at `q` is `(localChart L _ q.out).symm`, whose `.target` is
  -- the source of `localChart L _ q.out`.
  have h2 :
      (chartAt (Fin g → ℂ) q).target =
        (localChart L (discRadius_separates L) q.out).source := by
    -- `(localChart L _ q.out).symm.target = (localChart L _ q.out).source`
    rfl
  rw [h2] at h1
  -- The chart's symm sends `(chartAt _ q) a` to `a`, by `left_inv`.
  -- And the chart's symm equals `localChart L _ q.out`, which agrees with
  -- `L.mkQ` on its source.
  have h3 :
      (chartAt (Fin g → ℂ) q).symm =
        localChart L (discRadius_separates L) q.out := by
    -- `((localChart L _ q.out).symm).symm = localChart L _ q.out`.
    exact OpenPartialHomeomorph.symm_symm _
  rw [h3] at h
  -- On the source of `localChart`, the forward equals `L.mkQ` by
  -- definition.
  exact h

/-- Local agreement for addition: on `source(q₁) × source(q₂)`, the
addition `(a, b) ↦ a + b` equals the lifted form
`(a, b) ↦ mkQ (chartAt q₁ a + chartAt q₂ b)`. -/
private lemma add_eqOn_local
    (q₁ q₂ : (Fin g → ℂ) ⧸ L) :
    Set.EqOn (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) => p.1 + p.2)
      (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) =>
        (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
          ((chartAt (Fin g → ℂ) q₁) p.1 + (chartAt (Fin g → ℂ) q₂) p.2))
      ((chartAt (Fin g → ℂ) q₁).source ×ˢ (chartAt (Fin g → ℂ) q₂).source) := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  show p.1 + p.2 =
    (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
      ((chartAt (Fin g → ℂ) q₁) p.1 + (chartAt (Fin g → ℂ) q₂) p.2)
  -- `mkQ` is an additive homomorphism.
  rw [map_add L.mkQ, mkQ_chartAt_apply L q₁ hp1, mkQ_chartAt_apply L q₂ hp2]

/-- Local agreement for negation: on `source(q)`, the negation
`a ↦ -a` equals the lifted form `a ↦ mkQ (-(chartAt q a))`. -/
private lemma neg_eqOn_local
    (q : (Fin g → ℂ) ⧸ L) :
    Set.EqOn (fun a : (Fin g → ℂ) ⧸ L => -a)
      (fun a : (Fin g → ℂ) ⧸ L =>
        (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
          (-(chartAt (Fin g → ℂ) q) a))
      (chartAt (Fin g → ℂ) q).source := by
  intro a ha
  show -a = (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L) (-(chartAt (Fin g → ℂ) q) a)
  rw [map_neg L.mkQ, mkQ_chartAt_apply L q ha]

/-! ### Smoothness of the lifted forms -/

/-- The lifted addition form
`(a, b) ↦ mkQ (chartAt q₁ a + chartAt q₂ b)`
is `ContMDiffOn` on `source(q₁) × source(q₂)`. -/
private lemma contMDiffOn_lifted_add
    (n : WithTop ℕ∞) (q₁ q₂ : (Fin g → ℂ) ⧸ L) :
    ContMDiffOn ((𝓘(ℂ, Fin g → ℂ)).prod (𝓘(ℂ, Fin g → ℂ)))
        (𝓘(ℂ, Fin g → ℂ)) n
      (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) =>
        (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
          ((chartAt (Fin g → ℂ) q₁) p.1 + (chartAt (Fin g → ℂ) q₂) p.2))
      ((chartAt (Fin g → ℂ) q₁).source ×ˢ (chartAt (Fin g → ℂ) q₂).source) := by
  -- Compose: chart fst & chart snd → add on E × E → mkQ.
  have h_chart1 :
      ContMDiffOn ((𝓘(ℂ, Fin g → ℂ)).prod (𝓘(ℂ, Fin g → ℂ)))
          (𝓘(ℂ, Fin g → ℂ)) n
        (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) =>
          (chartAt (Fin g → ℂ) q₁) p.1)
        ((chartAt (Fin g → ℂ) q₁).source ×ˢ (chartAt (Fin g → ℂ) q₂).source) := by
    have h := contMDiffOn_chart (I := 𝓘(ℂ, Fin g → ℂ)) (n := n) (x := q₁)
    exact (h.comp contMDiffOn_fst (fun p hp => hp.1))
  have h_chart2 :
      ContMDiffOn ((𝓘(ℂ, Fin g → ℂ)).prod (𝓘(ℂ, Fin g → ℂ)))
          (𝓘(ℂ, Fin g → ℂ)) n
        (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) =>
          (chartAt (Fin g → ℂ) q₂) p.2)
        ((chartAt (Fin g → ℂ) q₁).source ×ˢ (chartAt (Fin g → ℂ) q₂).source) := by
    have h := contMDiffOn_chart (I := 𝓘(ℂ, Fin g → ℂ)) (n := n) (x := q₂)
    exact (h.comp contMDiffOn_snd (fun p hp => hp.2))
  -- Sum on E.
  have h_sum :
      ContMDiffOn ((𝓘(ℂ, Fin g → ℂ)).prod (𝓘(ℂ, Fin g → ℂ)))
          (𝓘(ℂ, Fin g → ℂ)) n
        (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) =>
          (chartAt (Fin g → ℂ) q₁) p.1 + (chartAt (Fin g → ℂ) q₂) p.2)
        ((chartAt (Fin g → ℂ) q₁).source ×ˢ (chartAt (Fin g → ℂ) q₂).source) :=
    h_chart1.add h_chart2
  -- Apply mkQ.
  have h_mkQ :
      ContMDiff (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
        (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L) :=
    mkQ_contMDiff_complex L n
  exact h_mkQ.comp_contMDiffOn h_sum

/-- The lifted negation form `a ↦ mkQ (-(chartAt q a))` is `ContMDiffOn`
on `source(q)`. -/
private lemma contMDiffOn_lifted_neg
    (n : WithTop ℕ∞) (q : (Fin g → ℂ) ⧸ L) :
    ContMDiffOn (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
      (fun a : (Fin g → ℂ) ⧸ L =>
        (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
          (-(chartAt (Fin g → ℂ) q) a))
      (chartAt (Fin g → ℂ) q).source := by
  -- chart → neg on E → mkQ.
  have h_chart :
      ContMDiffOn (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
        ((chartAt (Fin g → ℂ) q) : ((Fin g → ℂ) ⧸ L) → (Fin g → ℂ))
        (chartAt (Fin g → ℂ) q).source :=
    contMDiffOn_chart (I := 𝓘(ℂ, Fin g → ℂ)) (n := n) (x := q)
  have h_neg :
      ContMDiffOn (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
        (fun a : (Fin g → ℂ) ⧸ L => -(chartAt (Fin g → ℂ) q) a)
        (chartAt (Fin g → ℂ) q).source :=
    h_chart.neg
  have h_mkQ :
      ContMDiff (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
        (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L) :=
    mkQ_contMDiff_complex L n
  exact h_mkQ.comp_contMDiffOn h_neg

/-! ### Smoothness of `+` and `Neg.neg` on `G` -/

/-- The addition `+ : G × G → G` is `ContMDiff` for the complex model. -/
theorem add_contMDiff_complex (n : WithTop ℕ∞) :
    ContMDiff ((𝓘(ℂ, Fin g → ℂ)).prod (𝓘(ℂ, Fin g → ℂ)))
        (𝓘(ℂ, Fin g → ℂ)) n
      (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) => p.1 + p.2) := by
  intro ⟨q₁, q₂⟩
  -- The product source is open and contains `(q₁, q₂)`.
  have hopen :
      IsOpen
        ((chartAt (Fin g → ℂ) q₁).source ×ˢ (chartAt (Fin g → ℂ) q₂).source) :=
    (chartAt (Fin g → ℂ) q₁).open_source.prod (chartAt (Fin g → ℂ) q₂).open_source
  have hmem :
      (q₁, q₂) ∈ ((chartAt (Fin g → ℂ) q₁).source ×ˢ
        (chartAt (Fin g → ℂ) q₂).source) :=
    ⟨mem_chart_source _ _, mem_chart_source _ _⟩
  -- Transfer smoothness of the lifted form via `congr`.
  have h_lifted := contMDiffOn_lifted_add L n q₁ q₂
  have h_eq := add_eqOn_local L q₁ q₂
  have h_add :
      ContMDiffOn ((𝓘(ℂ, Fin g → ℂ)).prod (𝓘(ℂ, Fin g → ℂ)))
          (𝓘(ℂ, Fin g → ℂ)) n
        (fun p : ((Fin g → ℂ) ⧸ L) × ((Fin g → ℂ) ⧸ L) => p.1 + p.2)
        ((chartAt (Fin g → ℂ) q₁).source ×ˢ (chartAt (Fin g → ℂ) q₂).source) :=
    h_lifted.congr h_eq
  exact h_add.contMDiffAt (hopen.mem_nhds hmem)

/-- The negation `Neg.neg : G → G` is `ContMDiff` for the complex model. -/
theorem neg_contMDiff_complex (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
      (fun a : (Fin g → ℂ) ⧸ L => -a) := by
  intro q
  have hopen : IsOpen (chartAt (Fin g → ℂ) q).source :=
    (chartAt (Fin g → ℂ) q).open_source
  have hmem : q ∈ (chartAt (Fin g → ℂ) q).source := mem_chart_source _ _
  have h_lifted := contMDiffOn_lifted_neg L n q
  have h_eq := neg_eqOn_local L q
  have h_neg :
      ContMDiffOn (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
        (fun a : (Fin g → ℂ) ⧸ L => -a)
        (chartAt (Fin g → ℂ) q).source :=
    h_lifted.congr h_eq
  exact h_neg.contMDiffAt (hopen.mem_nhds hmem)

/-! ### `ContMDiffAdd` and `LieAddGroup` instances -/

/-- `(Fin g → ℂ) ⧸ L` is a `ContMDiffAdd` for the complex model. -/
noncomputable instance contMDiffAdd_quotient_of_zlattice (n : WithTop ℕ∞) :
    ContMDiffAdd (𝓘(ℂ, Fin g → ℂ)) n ((Fin g → ℂ) ⧸ L) where
  contMDiff_add := add_contMDiff_complex L n

/-- `(Fin g → ℂ) ⧸ L` is an additive Lie group for the complex model. -/
noncomputable instance lieAddGroup_quotient_of_zlattice (n : WithTop ℕ∞) :
    LieAddGroup (𝓘(ℂ, Fin g → ℂ)) n ((Fin g → ℂ) ⧸ L) where
  contMDiff_neg := neg_contMDiff_complex L n

end JacobianChallenge
