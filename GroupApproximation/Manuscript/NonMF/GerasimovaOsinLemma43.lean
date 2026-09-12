import GroupApproximation.Manuscript.NonMF.GerasimovaOsinAlternatingWord
import GroupApproximation.GGT.DGOLemma421Proof

/-!
# Gerasimova–Osin, Lemma 4.3, and the choice (16)

Gerasimova–Osin (arXiv:1910.14524v3), §4:

> Let `C` denote the constant provided by Proposition 3.6.  We fix any `t ∈ H`
> satisfying `d̂(1,t) > 5C` (16); such an element exists by condition (b) of
> Definition 3.2.

> **Lemma 4.3.** For each `i ∈ {1,…,n}`, `aᵢ` is an isolated `H`-component of `p`.

Here `p` is any path labelled `w = t f₁ t f₂ … t fₙ`, `aᵢ` its `i`-th `t`-edge (position
`2(i−1)` of `altWord t fs`), and the proof is Proposition 3.6 on the loop closing two
connected components.  In the repository this argument is
`GGT.OsinComponents.peripheralOccurrence_isIsolated_of_uniformBound`: every peripheral
occurrence of a `W`-word whose subgroup letters lie outside the relative ball of radius
`50C` is isolated, `C` being the uniform constant of Dahmani–Guirardel–Osin's
Proposition 4.14 at `(1,1)` (`dgoProposition414Uniform`).  The words `altWord t fs` are
`W`-words (`GerasimovaOsinAlternatingWord`), so Lemma 4.3 is that theorem at the even
positions.  The depth `50C` is larger than (16) asks; (16) is a lower bound on the depth
of `t`, so any deeper `t` is admissible, and `exists_deep_letter` supplies one.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Gerasimova–Osin's Proposition 4.1).
Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GerasimovaOsinWords

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents

universe u

variable {G : Type u} [Group G]

/-- **The choice (16)**: a hyperbolically embedded infinite subgroup has letters
outside every relative ball, by local finiteness (condition (b) of Definition 3.2). -/
theorem exists_deep_letter {D : RelGenSet G Unit} (hD : D.IsHyperbolicallyEmbedded)
    (hinf : (D.fam () : Set G).Infinite) (R : ℕ) :
    ∃ t : G, t ∈ D.fam () ∧ t ∉ D.relBall () R := by
  by_contra hcon
  push_neg at hcon
  exact hinf ((hD.locallyFinite () R).subset fun h hh => hcon h hh)

/-- The letter at an even position of `t f₁ ⋯ t fₙ` is `t`. -/
theorem getElem?_altWord_two_mul {t : G} {fs : List G} {i : ℕ} (hi : i < fs.length) :
    (altWord t fs)[2 * i]? = some (RelLetter.comp () t) := by
  rw [getElem?_altWord_even, List.getElem?_eq_getElem hi]
  rfl

/-- **Gerasimova–Osin, Lemma 4.3.**  Every `t`-edge of a path labelled
`t f₁ ⋯ t fₙ` is a single-letter isolated `H`-component. -/
theorem altWord_isComp_isIsolated {D : RelGenSet G Unit} {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C) {t : G} (ht : t ∈ D.fam ())
    (hdeep : t ∉ D.relBall () (50 * C)) {fs : List G} (hfsX : ∀ f ∈ fs, f ∈ D.base)
    (hfsH : ∀ f ∈ fs, f ∉ D.fam ()) (v : G) {i : ℕ} (hi : i < fs.length) :
    IsComp () (altWord t fs) (2 * i) (2 * i + 1) ∧
      IsIsolated D.fam () v (altWord t fs) (2 * i) := by
  have hW3 := isWThree_altWord D t hfsH
  have hcomp : IsComp () (altWord t fs) (2 * i) (2 * i + 1) :=
    isComp_singleton_of_isWThree_read hW3 (getElem?_altWord_two_mul hi)
  refine ⟨hcomp, ?_⟩
  obtain ⟨occ, hpos, hlabel⟩ :=
    exists_peripheralOccurrence_eq_of_isCompStart (⟨2 * i + 1, hcomp⟩ :
      IsCompStart () (altWord t fs) (2 * i))
  have hiso := peripheralOccurrence_isIsolated_of_uniformBound hC hbound
    (isLetter_altWord D ht hfsX) (isWOne_altWord t fs) (isWTwo_altWord D hdeep fs) hW3 v occ
  rw [hpos, hlabel] at hiso
  exact hiso

end GerasimovaOsinWords
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.GerasimovaOsinWords

#audit_axioms exists_deep_letter
#audit_axioms altWord_isComp_isIsolated
