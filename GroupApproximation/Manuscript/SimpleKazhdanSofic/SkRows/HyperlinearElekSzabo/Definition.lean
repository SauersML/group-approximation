import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.Norm
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyperlinearity in the Elek–Szabó normalization, tex 345–348

`simple_kazhdan_sofic_group.tex`, l.345–348:

> It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} and
> hyperlinear~\cite[Theorem~2]{ElekSzabo}, ...

`IsHyperlinearElekSzabo G`: for every finite `F ⊆ G` and `ε > 0` there are `n > 0` and a map
`φ : G → U(n)` with

* `‖φ(gh) − φ(g)φ(h)‖₂ < ε` for all `g, h ∈ F`, and
* `‖φ(g) − 1‖₂ ≥ √2 − ε` for all `g ∈ F`, `g ≠ 1`,

where `‖A‖₂ = (tr(A* A) / n)^{1/2}` is `esNorm n A` (`Norm.lean`).  This is the printed
normalization of Elek–Szabó (unitaries, normalized trace norm, constant `√2`), as opposed to the
corpus `IsHyperlinear` (`Sofic/Hyperlinear.lean`), which works with the squared distance on a
bundled finite model and separates all pairs of distinct elements by `2 − ε`.

Proof route: this module only states the definition; `OfCorpus.lean` and `ToCorpus.lean` prove it
equivalent to the corpus notion.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace HyperlinearElekSzabo

/-- Hyperlinearity with unitary matrices `U(n)`, the normalized Hilbert–Schmidt norm
`‖A‖₂ = (tr(A* A) / n)^{1/2}`, almost-multiplicativity on `F` and `‖φ g − 1‖₂ ≥ √2 − ε` for the
nontrivial elements of `F`. -/
def IsHyperlinearElekSzabo (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (φ : G → Matrix (Fin n) (Fin n) ℂ), 0 < n ∧
      (∀ g, φ g ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, esNorm n (φ (g * h) - φ g * φ h) < ε) ∧
      (∀ g ∈ F, g ≠ 1 → Real.sqrt 2 - ε ≤ esNorm n (φ g - 1))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.IsHyperlinearElekSzabo

end HyperlinearElekSzabo
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
