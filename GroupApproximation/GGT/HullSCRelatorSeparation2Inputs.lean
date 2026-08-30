import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyFourWay
import GroupApproximation.GGT.HullSCRelatorSeparation2Statement

/-!
# The relator chain's standing inputs, named --- and narrowed to the base part
the construction builds

The chain's two open geometric items travelled as anonymous clauses of a
section variable, which made them impossible to cite and impossible to weaken
one at a time.  They are named here, in both the form the chain has carried and
the form Hull's proof actually discharges.

## Why the narrow form is the faithful one

Hull verifies the `W`-conditions for THE RELATOR HE BUILDS --- `t` adjoined to
the alphabet as a letter, so the word carries exactly one `X`-letter --- and
never for an arbitrary base part.  The `∀ p` form therefore asks for strictly
more than the source proves, and narrowing it to `p.length = 1` moves the
hypothesis toward the citation rather than away from it.  `…Input₂` is the wide
form, `…InputOne₂` the narrow one, and `…InputOne₂_of_Input₂` records that the
second is genuinely weaker.

What the narrowing buys is on the other side of the seam: a relator with one
`X`-letter satisfies Dahmani--Guirardel--Osin's (W1) and (W4), so their
Lemma 4.21(1) reaches every piece of it rather than only the pieces lying
inside the run.  `HullSC.separationNe₂_clause_of_inputs_of_mem_base` is the
route that builds such a relator, and it needs `t⁻¹` in the base --- which is
what `HullSC.HypEmbeddedCore₂.adjoinPair` supplies and what
`HullRelatorStatement₂OfBaseLetter` records as a hypothesis.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Inputs

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The block count, at every base part.**  Item 2 of the Ledger as the chain
has carried it. -/
def RelatorBlockCountInput₂ (E : HypEmbeddedCore₂ A N) (cnt : ℕ) : Prop :=
  ∀ (p : List G) (ms : List ℕ)
      (v : List (GGT.RelLetter G Bool)),
      RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v →
      ∀ i j : ℕ, i ≤ j → j ≤ v.length →
        j - i ≤ wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) v i)
          (GGT.OsinComponents.vertex (1 : G) v j) + blockConst p cnt

/-- **The block count, at the base parts the construction builds.**  Item 2 as
Hull discharges it: his base part is one letter. -/
def RelatorBlockCountInputOne₂ (E : HypEmbeddedCore₂ A N) (cnt : ℕ) : Prop :=
  ∀ (p : List G), p.length = 1 →
    ∀ (ms : List ℕ)
      (v : List (GGT.RelLetter G Bool)),
      RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v →
      ∀ i j : ℕ, i ≤ j → j ≤ v.length →
        j - i ≤ wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G) v i)
          (GGT.OsinComponents.vertex (1 : G) v j) + blockConst p cnt

/-- **The two same-side exclusions, at every base part.**  Item 3 as carried. -/
def RelatorSideExclusionInput₂ (E : HypEmbeddedCore₂ A N) : Prop :=
  ∀ (p : List G) (ms : List ℕ)
      (py pz u u' : List (GGT.RelLetter G Bool)),
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

/-- **The two same-side exclusions, at the base parts built.**  Item 3 as
discharged. -/
def RelatorSideExclusionInputOne₂ (E : HypEmbeddedCore₂ A N) : Prop :=
  ∀ (p : List G), p.length = 1 →
    ∀ (ms : List ℕ)
      (py pz u u' : List (GGT.RelLetter G Bool)),
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

/-- **The narrow count is weaker.**  Forgetting the length hypothesis. -/
theorem relatorBlockCountInputOne₂_of_input₂ {E : HypEmbeddedCore₂ A N}
    {cnt : ℕ} (h : RelatorBlockCountInput₂ E cnt) :
    RelatorBlockCountInputOne₂ E cnt :=
  fun p _ ms v hv i j hij hj => h p ms v hv i j hij hj

/-- **The narrow exclusions are weaker.**  Likewise. -/
theorem relatorSideExclusionInputOne₂_of_input₂ {E : HypEmbeddedCore₂ A N}
    (h : RelatorSideExclusionInput₂ E) : RelatorSideExclusionInputOne₂ E :=
  fun p _ ms py pz u u' hu hu' hpy hpz => h p ms py pz u u' hu hu' hpy hpz

end Inputs

section Target

/-- **Hull's §6 over two subgroups, at a core whose base contains `t⁻¹`.**

`HullRelatorStatement₂` with one hypothesis added.  It is what the chain can
prove from the NARROW inputs, because the one-letter base part is available
exactly when `t⁻¹` is a letter; and it is what the seam can consume, because
`HullSC.HypEmbeddedCore₂.adjoinPair` puts `t⁻¹` in the base of a core whose
other eleven clauses are the ones it was handed. -/
def HullRelatorStatement₂OfBaseLetter : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N → ∀ (t : G),
      t⁻¹ ∈ E.rel.base → ∀ (eps rho : ℕ) (mu : ℝ), 0 < mu →
        ∃ u ∈ N, ∃ W : Set (List (GGT.RelLetter G Bool)),
          (∃ v ∈ W, GGT.RelLetter.listVal v = t⁻¹ * u) ∧
            RelWord.IsSmallCancellation E.rel W eps mu rho

end Target

end HullSC
end GroupApproximation
