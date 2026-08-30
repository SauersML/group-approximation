import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyCompose

/-!
# The separation over every core, and Hull's §6 from it

Bookkeeping, and the last file of the relator chain.
`HullSC.separationNe₂_clause_of_inputs` proves the corrected separation at one
core; `HullSC.hullRelatorStatement₂_of_separationNe₂` consumes it quantified
over every group, alphabet, subgroup and core.  So the three inputs are
quantified the same way and the two are composed.

The constants `cnt` and `δ` sit inside the quantifier as existentials rather
than outside it as parameters, which is the honest reading: the block-count
constant and the hyperbolicity constant belong to the core, and a chain that
fixed them once for all cores would be claiming something it has no reason to.
They do NOT have to know `eps`: the composition works at `max cnt (eps + 2)`,
which it chooses itself once `eps` arrives, and enlarging the constant only
weakens the count.

Nothing here is a mathematical step.  What the chain rests on is the three
clauses of `hinput`, and they are items 1, 2 and 3 of
`GGT/HullSCRelatorSeparation2Ledger.lean` in that order.  There used to be a
fourth, the diagonal leaf; (W4) is a field of the core now, so it is gone.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Quantified

variable
  (hinput : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) (E : HypEmbeddedCore₂ A N), ∃ cnt δ : ℕ,
      Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ ∧
      (∀ (p : List G) (ms : List ℕ)
        (v : List (GGT.RelLetter G Bool)),
        RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v →
        ∀ i j : ℕ, i ≤ j → j ≤ v.length →
          j - i ≤ wordDist E.rel.alphabet.carrier
            (GGT.OsinComponents.vertex (1 : G) v i)
            (GGT.OsinComponents.vertex (1 : G) v j) + blockConst p cnt) ∧
      (∀ (p : List G) (ms : List ℕ)
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
              GGT.OsinComponents.vertex (1 : G) u' m ∉ E.rel.fam s)))

include hinput in
/-- **The corrected separation, over every core.**

The three inputs are the Ledger's standing items: `hδ` is what is left of
item 1, `hcount` is item 2, `hexcl` is item 3. -/
theorem separationNe₂_of_inputs :
    ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
        ∀ (t : G) (eps rho : ℕ), ∃ B : ℕ, ∀ L : ℕ,
          ∃ (p : List G) (ms : List ℕ),
            (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
              (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
                (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
              ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
                RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
                  RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
                    w' ≠ w → (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') →
                      B < u₀.length →
                        ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                          wordNorm E.rel.base z ≤ eps →
                            GGT.RelLetter.listVal u₀'
                                = y * GGT.RelLetter.listVal u₀ * z →
                              GGT.RelLetter.listVal w'
                                = y * GGT.RelLetter.listVal w * y⁻¹ := by
  intro G _ A N E hN t eps rho
  obtain ⟨cnt, δ, hδ, hcount, hexcl⟩ := hinput A N E
  exact separationNe₂_clause_of_inputs E hN cnt hδ hcount hexcl t eps rho

include hinput in
/-- **Hull's §6 over two subgroups, from the three standing items.**

The relator half of Hull's Theorem 5.1, conditional on exactly the three
clauses and on nothing else. -/
theorem hullRelatorStatement₂_of_inputs : HullRelatorStatement₂.{u} :=
  hullRelatorStatement₂_of_separationNe₂ (separationNe₂_of_inputs hinput)

end Quantified

end HullSC
end GroupApproximation
