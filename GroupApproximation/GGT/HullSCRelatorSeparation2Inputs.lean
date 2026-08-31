import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyFourWay
import GroupApproximation.GGT.HullSCRelatorSeparation2Statement

/-!
# The relator chain's chosen-list inputs

Hull builds a relator and chooses its exponent list jointly with the
finite-avoidance conditions.  This module therefore exposes a block count and
the side exclusion for one fixed relator.
The superseded unrestricted-anchor predicate is retained solely as the target
of its formal counterexample; no active construction consumes it.

The active side exclusion requires certificates for both component anchors.
This is exactly what the polygon machinery supplies and rules out the adjacent
non-anchor counterexample.  `HullSC.separationNe₂_clause_of_spelling_of_producer`
consumes the fixed-list predicate, while `HullSC.ExactRelatorDesign₂` packages
the jointly chosen list.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Inputs

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The block count for one fixed relator.**

The exponent list is part of the predicate.  This is essential: the former
all-list version was false on arbitrarily long zero-exponent lists.  Hull's
geometric estimate is consumed only after the deep exact list has been chosen. -/
def RelatorBlockCountAt₂ (E : HypEmbeddedCore₂ A N) (p : List G)
    (ms : List ℕ) (cnt : ℕ) : Prop :=
  ∀ (v : List (GGT.RelLetter G Bool)),
    RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v →
    ∀ i j : ℕ, i ≤ j → j ≤ v.length →
      j - i ≤ wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) v i)
        (GGT.OsinComponents.vertex (1 : G) v j) + blockConst p cnt

/-- Every fixed relator has the tautological block-count constant given by the
length of its exponent list.  A useful Hull estimate must improve this to a
uniform geometric constant, but unlike the superseded all-list predicate this
statement is unconditional and true. -/
theorem relatorBlockCountAt₂_length (E : HypEmbeddedCore₂ A N)
    (p : List G) (ms : List ℕ) :
    RelatorBlockCountAt₂ E p ms ms.length := by
  intro v hv i j hij hj
  have hvlen : v.length = p.length + ms.length := by
    rw [hv.length_eq, length_relatorWord₂]
  have hdist : 0 ≤ wordDist E.rel.alphabet.carrier
      (GGT.OsinComponents.vertex (1 : G) v i)
      (GGT.OsinComponents.vertex (1 : G) v j) := Nat.zero_le _
  simp only [blockConst]
  omega

/-- **The superseded unrestricted side exclusions for one chosen relator.**

This is retained only so
`HullSC.not_relatorSideExclusionAtUnrestricted₂_one_of_two_le` can state the
formal counterexample.  Its anchor indices `d` and `k` are unrestricted, so it
is not an input to any active construction. -/
def RelatorSideExclusionAtUnrestricted₂ (E : HypEmbeddedCore₂ A N) (p : List G)
    (ms : List ℕ) : Prop :=
  ∀ (py pz u u' : List (GGT.RelLetter G Bool)),
      (∃ v tl : List (GGT.RelLetter G Bool),
        RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v ∧
          v = u ++ tl) →
      (∃ v tl : List (GGT.RelLetter G Bool),
        RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v ∧
          v = u' ++ tl) →
      (∀ x ∈ py, ∃ g : G, x = GGT.RelLetter.base g) →
      (∀ x ∈ pz, ∃ g : G, x = GGT.RelLetter.base g) →
      (∀ (s : Bool) (d i' : ℕ), i' ≤ u.length → i' ≠ d →
        GGT.OsinComponents.IsCompStart s
            (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
            (py.length + i') →
        (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u i' ∉ E.rel.fam s) ∧
        (∀ (s : Bool) (k m : ℕ), m ≤ u'.length → m ≠ k →
          GGT.OsinComponents.IsCompStart s
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
              (py.length + u.length + pz.length + (u'.length - m)) →
          (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u' m ∉ E.rel.fam s)

/-- **The two same-side exclusions for one chosen relator.**

This is the non-vacuous granularity of Hull's construction: `p` and `ms` have
already been chosen jointly with the finite-avoidance conditions.  In
particular this predicate does not quantify over degenerate exponent lists.

The anchor on the first long side is required to be the single-letter
component supplied by the matching construction.  On the oppositely oriented
second long side, `k` is the endpoint in `u'`, hence the start in `revWord u'`;
the existential certificate states exactly that it bounds a single-letter
component.  These are the certificates present at every geometric call site,
and they exclude the refuted choice of an arbitrary adjacent anchor. -/
def RelatorSideExclusionAt₂ (E : HypEmbeddedCore₂ A N) (p : List G)
    (ms : List ℕ) : Prop :=
  ∀ (py pz u u' : List (GGT.RelLetter G Bool)),
      (∃ v tl : List (GGT.RelLetter G Bool),
        RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v ∧
          v = u ++ tl) →
      (∃ v tl : List (GGT.RelLetter G Bool),
        RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v ∧
          v = u' ++ tl) →
      (∀ x ∈ py, ∃ g : G, x = GGT.RelLetter.base g) →
      (∀ x ∈ pz, ∃ g : G, x = GGT.RelLetter.base g) →
      0 < py.length → 0 < pz.length →
      (∀ (s : Bool) (d i' : ℕ),
        GGT.OsinComponents.IsComp s u d (d + 1) →
        i' ≤ u.length → i' ≠ d →
        GGT.OsinComponents.IsCompStart s
            (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
            (py.length + i') →
        (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u i' ∉ E.rel.fam s) ∧
        (∀ (s : Bool) (k m : ℕ),
          (∃ j : ℕ, j + 1 = k ∧ GGT.OsinComponents.IsComp s u' j k) →
          m ≤ u'.length → m ≠ k →
          GGT.OsinComponents.IsCompStart s
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
              (py.length + u.length + pz.length + (u'.length - m)) →
          (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u' m ∉ E.rel.fam s)

end Inputs

end HullSC
end GroupApproximation
