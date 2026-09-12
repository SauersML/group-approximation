import Mathlib.Data.ZMod.QuotientGroup
import GroupApproximation.Kazhdan.CCKWCosetComplexLocallyFinite
import GroupApproximation.Kazhdan.CCKWCosetComplexLinks
import GroupApproximation.Kazhdan.GHBLatticeRoute

/-!
# `SharpExistence` from `GHB(7)`, over the systolic leaves

CCKW Theorem 3.1(ii) in its cyclic case (`CCKWFiniteOrderConjugateIntoVertex`) follows from the
fixed-clique theorem for systolic triangle complexes, applied to the coset complex of `GHB(7)`
and the finite cyclic group `⟨g⟩`: the complex is connected and simply connected (T2), its links
are 6-large (`cosetComplex_linksSixLarge`), it is locally finite (`cosetComplex_locallyFinite`),
and `⟨g⟩` acts through `cosetAction` by triangle-preserving automorphisms (`tri_cosetAction`).
The invariant clique gives a fixed vertex, hence a conjugation into a vertex group
(`cckwFiniteOrderConjugateIntoVertex_of_invariantCliques`), and `sharpExistence_of_ghb7Leaves`
turns that into `SharpExistence`.

Draft over named leaves, each an ordinary hypothesis of an intermediate theorem (never a binder
of an endpoint), replaced as the producers compile:
* `hT6 : SystolicInvariantCliqueStatement` — the fixed-clique theorem (T6);
* `hsc`, `hconn` — `CCKWTits.cckwCosetComplex_simplyConnected`,
  `CCKWTits.cckwCosetComplex_connected` (`Kazhdan/CCKWTitsGHB.lean`, T2);
* `h3`, `h4` with `Finite (U3 7)`, `Finite (U4 7)` — CCKW Proposition 7.2 order bounds;
* `hhyp`, `hT` — hyperbolicity and property (T) of `GHB(7)`.
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

/-- **The fixed-clique theorem for systolic triangle complexes**, in the form applied here: a
finite group acting by triangle-preserving graph automorphisms on a connected, simply connected,
locally finite triangle complex with 6-large links maps some nonempty clique into itself. -/
def SystolicInvariantCliqueStatement : Prop :=
  ∀ (V : Type) (X : Systolic.TriangleComplex V) (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* (X.G ≃g X.G)),
    Systolic.SimplyConnected X → X.G.Connected → Systolic.LinksSixLarge X →
    (∀ v, (X.G.neighborSet v).Finite) →
    (∀ (γ : Γ) (x y z : V), X.Tri x y z → X.Tri (ρ γ x) (ρ γ y) (ρ γ z)) →
    ∃ σ : Finset V, σ.Nonempty ∧ X.G.IsClique (σ : Set V) ∧ ∀ γ : Γ, ∀ x ∈ σ, ρ γ x ∈ σ

/-- **Every element of finite order of `GHB(7)` maps a nonempty clique of the coset complex into
itself**: the fixed-clique theorem applied to `⟨g⟩` acting through `cosetAction`. -/
theorem invariantCliques_of_systolicInvariantClique (hT6 : SystolicInvariantCliqueStatement)
    (hsc : Systolic.SimplyConnected cosetComplex) (hconn : cosetComplex.G.Connected)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) :
    ∀ g : GHB 7, IsOfFinOrder g → ∃ σ : Finset Vertex, σ.Nonempty ∧
      cosetComplex.G.IsClique (σ : Set Vertex) ∧ ∀ x ∈ σ, cosetAction g x ∈ σ := by
  intro g hg
  haveI : Finite (Subgroup.zpowers g) := hg.finite_zpowers.to_subtype
  obtain ⟨σ, hne, hcl, hinv⟩ := hT6 Vertex cosetComplex (Subgroup.zpowers g)
    (cosetAction.comp (Subgroup.zpowers g).subtype) hsc hconn (cosetComplex_linksSixLarge h3 h4)
    cosetComplex_locallyFinite (fun γ _ _ _ h => tri_cosetAction (γ : GHB 7) h)
  exact ⟨σ, hne, hcl, fun x hx => hinv ⟨g, Subgroup.mem_zpowers g⟩ x hx⟩

/-- **CCKW Theorem 3.1(ii), cyclic case, for `GHB(7)`**, over the systolic leaves. -/
theorem cckwFiniteOrderConjugateIntoVertex_of_systolicLeaves
    (hT6 : SystolicInvariantCliqueStatement) (hsc : Systolic.SimplyConnected cosetComplex)
    (hconn : cosetComplex.G.Connected) [Finite (U3 7)] [Finite (U4 7)]
    (h3 : Nat.card (U3 7) ≤ 7 ^ 3) (h4 : Nat.card (U4 7) ≤ 7 ^ 4) :
    CCKWFiniteOrderConjugateIntoVertex :=
  cckwFiniteOrderConjugateIntoVertex_of_invariantCliques
    (invariantCliques_of_systolicInvariantClique hT6 hsc hconn h3 h4)

end CCKW

/-- **`SharpExistence` from `GHB(7)`**, over the systolic leaves, the order bounds,
hyperbolicity and property (T). -/
theorem sharpExistence_ghb7_of_systolicLeaves (hT6 : CCKW.SystolicInvariantCliqueStatement)
    (hsc : Systolic.SimplyConnected CCKW.cosetComplex) (hconn : CCKW.cosetComplex.G.Connected)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7))
    (hT : HasKazhdanPropertyT.{0, 0} (GHB 7)) : Hyperbolic.SharpExistence :=
  GHBQuotient.sharpExistence_of_ghb7Leaves
    (CCKW.cckwFiniteOrderConjugateIntoVertex_of_systolicLeaves hT6 hsc hconn h3 h4) h3 h4 hhyp hT

end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.CCKW.invariantCliques_of_systolicInvariantClique
#audit_axioms GroupApproximation.KMSGroup.CCKW.cckwFiniteOrderConjugateIntoVertex_of_systolicLeaves
#audit_axioms GroupApproximation.KMSGroup.sharpExistence_ghb7_of_systolicLeaves
