import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyCompose
import GroupApproximation.GGT.CayleyFourPointConverse

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

/-! ## The wide inputs are retired

`separationNe₂_of_inputs` and `hullRelatorStatement₂_of_inputs` stood here,
taking the block count and the two side exclusions at EVERY base part.  Hull's
§6 verifies the `W`-conditions for the relator he builds --- base part one
letter --- and never for an arbitrary one, so the wide forms asked for strictly
more than the source discharges.  What replaces them is the section below, at
the narrow inputs and at a core whose base carries `t⁻¹`; the wide Props
survive in `GGT/HullSCRelatorSeparation2Inputs.lean` with
`HullSC.relatorBlockCountInputOne₂_of_input₂` and its exclusion twin recording
that the narrowing is a weakening, so nothing that could be proved before has
become unprovable. -/

section QuantifiedBaseLetter

variable
  (hinput : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) (E : HypEmbeddedCore₂ A N), ∃ cnt : ℕ,
      RelatorBlockCountInputOne₂ E cnt ∧ RelatorSideExclusionInputOne₂ E)

include hinput in
/-- **Corrected separation from the narrow, one-letter inputs.**

Unlike the retired wide producer, the current core is assumed to contain
`t⁻¹` in its base.  This is precisely the core produced by `adjoinPair` at the
one-step seam. -/
theorem separationNe₂OfBaseLetter_of_inputs :
    ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
        ∀ (t : G), t⁻¹ ∈ E.rel.base → ∀ (eps rho : ℕ),
          ∃ B : ℕ, ∀ L : ℕ,
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
  intro G _ A N E hN t ht eps rho
  obtain ⟨cnt, hcount, hexcl⟩ := hinput A N E
  obtain ⟨δ, hδ⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded E.rel E.embedded
  exact separationNe₂_clause_of_inputs_of_mem_base E hN cnt hδ hcount hexcl
    t ht eps rho

include hinput in
/-- **Hull's faithful one-letter §6 endpoint from the narrow inputs.** -/
theorem hullRelatorStatement₂OfBaseLetter_of_inputs :
    HullRelatorStatement₂OfBaseLetter.{u} :=
  hullRelatorStatement₂OfBaseLetter_of_separationNe₂
    (separationNe₂OfBaseLetter_of_inputs hinput)

end QuantifiedBaseLetter

end HullSC
end GroupApproximation
