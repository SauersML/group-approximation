import GroupApproximation.BooneHigman.Metabelian.AbsorptionEmbedding
import GroupApproximation.BooneHigman.Metabelian.ChainCharP
import GroupApproximation.BooneHigman.Metabelian.ChainCharZero
import GroupApproximation.Meta.AxiomGuard

/-!
# Absorption, part 2: `GL_M(R) ↪ E_N(R)` modulo `SL_N(R) = E_N(R)`

Lane `bh-met-16`.  The chain skeleton (`ChainCharP.lean`, `ChainCharZero.lean`) needs, for
`N ≥ 3` and `2M ≤ N`, an injective homomorphism `GL_M(R) →* E_N(R)` for the rings
`R = F_p[s_0, ..., s_{k-1}]` and `R = ℤ[1/m][t_0, ..., t_{k-1}]`.

For any commutative ring `R` the homomorphism `g ↦ diag(g, (g⁻¹)ᵀ, 1)` of
`AbsorptionEmbedding.lean` is injective with determinant `1`
(`absorptionUnits_injective`, `absorptionUnits_det`).  So it corestricts to `E_N(R)` as soon as
every determinant-one matrix of size `N` is elementary (`exists_injective_hom_elementaryGroup`).

The remaining input is isolated as `PolynomialSuslinStatement`: `SL_N(R) ⊆ E_N(R)` for `N ≥ 3`
over the two families of rings.  It is strictly smaller in proof content than the two absorption
statements (these additionally need the homomorphism, its injectivity and its determinant, all
proved here).  **Truth check.**  This is Suslin's theorem
(A. A. Suslin, *On the structure of the special linear group over polynomial rings*, 1977):
for a regular Noetherian ring `A` of Krull dimension `d` and `n ≥ max(3, d + 2)`, the map
`SL_n(A[x_1, ..., x_k]) / E_n(A[x_1, ..., x_k]) → SL_n(A) / E_n(A)` is bijective.  Here `A = F_p`
(`d = 0`, a field) or `A = ℤ[1/m]` (`d ≤ 1`, a Euclidean domain), so `SL_n(A) = E_n(A)` and
`n ≥ 3` suffices; the cases `k = 0` are Gaussian elimination, and for `m = 0` the ring `ℤ[1/0]` is
the zero ring and the statement is trivial.  The bound `N ≥ 3` cannot be dropped:
`SL_2(F_p[s_0, s_1]) ≠ E_2` (Cohn's matrix `[[1 + s_0 s_1, s_0²], [-s_1², 1 - s_0 s_1]]`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- `SL_N(R) ⊆ E_N(R)`: every invertible `N × N` matrix of determinant `1` is elementary. -/
def SpecialLinearInElementary (R : Type*) [CommRing R] (N : ℕ) : Prop :=
  ∀ u : Matrix.GeneralLinearGroup (Fin N) R,
    Matrix.det (u : Matrix (Fin N) (Fin N) R) = 1 → u ∈ elementaryGroup (Fin N) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SpecialLinearInElementary

/-- **Absorption over a commutative ring.**  If `SL_N(R) ⊆ E_N(R)` and `2M ≤ N`, then
`g ↦ diag(g, (g⁻¹)ᵀ, 1)` is an injective homomorphism `GL_M(R) →* E_N(R)`. -/
theorem exists_injective_hom_elementaryGroup (R : Type*) [CommRing R] {M N : ℕ}
    (h : 2 * M ≤ N) (hSL : SpecialLinearInElementary R N) :
    ∃ f : Matrix.GeneralLinearGroup (Fin M) R →* elementaryGroup (Fin N) R,
      Function.Injective f := by
  refine ⟨(absorptionUnits (R := R) M N h).codRestrict (elementaryGroup (Fin N) R)
    (fun g ↦ hSL _ (absorptionUnits_det M N h g)), ?_⟩
  intro a b hab
  have h1 := congrArg Subtype.val hab
  apply absorptionUnits_injective (R := R) M N h
  exact h1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.exists_injective_hom_elementaryGroup

/-- **The isolated input (Suslin's theorem for the two coefficient families).**  For `N ≥ 3`,
`SL_N(F_p[s_0, ..., s_{k-1}]) ⊆ E_N` for every prime `p`, and
`SL_N(ℤ[1/m][t_0, ..., t_{k-1}]) ⊆ E_N` for every `m`.  See the module docstring for the truth
check. -/
def PolynomialSuslinStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 3 ≤ N →
      SpecialLinearInElementary (Chain.CharPPoly p k) N) ∧
    ∀ (m k N : ℕ), 3 ≤ N → SpecialLinearInElementary (Chain.SIntPoly m k) N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.PolynomialSuslinStatement

/-- **Positive characteristic absorption from Suslin's theorem.** -/
theorem charPElementaryAbsorptionStatement_of_suslin (hS : PolynomialSuslinStatement) :
    Chain.CharPElementaryAbsorptionStatement := by
  intro p _ k M N hN hMN
  exact exists_injective_hom_elementaryGroup (Chain.CharPPoly p k) hMN (hS.1 p k N hN)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.charPElementaryAbsorptionStatement_of_suslin

/-- **Characteristic zero absorption from Suslin's theorem.** -/
theorem charZeroElementaryAbsorptionStatement_of_suslin (hS : PolynomialSuslinStatement) :
    Chain.CharZeroElementaryAbsorptionStatement := by
  intro m k M N hN hMN
  exact exists_injective_hom_elementaryGroup (Chain.SIntPoly m k) hMN (hS.2 m k N hN)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.charZeroElementaryAbsorptionStatement_of_suslin

/-- Both absorption leaves of the chain skeleton from the single isolated input. -/
theorem elementaryAbsorptionStatements_of_suslin (hS : PolynomialSuslinStatement) :
    Chain.CharPElementaryAbsorptionStatement ∧ Chain.CharZeroElementaryAbsorptionStatement :=
  ⟨charPElementaryAbsorptionStatement_of_suslin hS,
    charZeroElementaryAbsorptionStatement_of_suslin hS⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.elementaryAbsorptionStatements_of_suslin

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
