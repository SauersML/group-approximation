import GroupApproximation.GGT.HullSCLemma51QuotientStokes
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridge
import GroupApproximation.GGT.DGOProposition435
import GroupApproximation.Meta.AxiomGuard

/-!
# The embedded Lemma 5.1 bridge, from clause (a) and a letter pullback

`RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`
(`GGT/HullSCLemma51EmbeddedBridge.lean`) concludes that the image family
`D.mapSurjective q hq` is hyperbolically embedded, Dahmani--Guirardel--Osin's
Definition 4.25: (a) the quotient relative Cayley graph is hyperbolic, and (b) every
quotient relative metric is locally finite.

Clause (a) is proved from the least-area certificates
(`hyperbolic_mapSurjective_of_leastAreaCertificates`, `GGT/HullSCLemma51QuotientStokes.lean`).

Clause (b) is Dahmani--Guirardel--Osin's Theorem 4.24 in the direction from linear
relative area to local finiteness.  Its proof reads a quotient relative ball off the
`λ`-component of the closing edge in a van Kampen diagram: the boundary of that
component consists of the closing edge, peripheral letters of relators, and peripheral
letters of short relations of `G`, which lie in fixed source relative balls.  So every
element of a quotient relative ball lifts to an element reachable in `G` by a path that
avoids `Γ_{H_λ}` and uses, besides the source letters, the finitely many values of
peripheral letters of relators as extra base letters.  `QuotientPeripheralLetterPullbackAt`
is that statement, with the extra letters `peripheralLetterValues W`.

It is the right replacement for the refuted `PeripheralPullbackBound`: in the
counterexample recorded in `GGT/HullSCLemma51EmbeddedBridge.lean` the element `q (t^m)`
is the image of the single extra base letter `t^m`.

This module proves that the letter pullback gives local finiteness
(`locallyFinite_mapSurjective_of_letterPullback`) and that, together with clause (a),
it gives the embedded bridge
(`relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback`).  The
letter pullback itself, `QuotientPeripheralLetterPullbackStatement`, is not proved
here; it enters only as the hypothesis of that implication.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric

universe u v w

/-- **The values of the peripheral letters of a relator family**, with their
inverses. -/
def peripheralLetterValues {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) : Set G :=
  {x | ∃ word ∈ W, ∃ a ∈ word, (∃ lam h, a = GGT.RelLetter.comp lam h) ∧
    (x = a.val ∨ x = a.val⁻¹)}

theorem inv_mem_peripheralLetterValues {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) :
    ∀ x ∈ peripheralLetterValues W, x⁻¹ ∈ peripheralLetterValues W := by
  rintro x ⟨word, hword, a, ha, hcomp, hx | hx⟩
  · exact ⟨word, hword, a, ha, hcomp, Or.inr (by rw [hx])⟩
  · exact ⟨word, hword, a, ha, hcomp, Or.inl (by rw [hx, inv_inv])⟩

/-- A strongly bounded family has finitely many peripheral letter values. -/
theorem finite_peripheralLetterValues {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (hW : RelWord.IsStronglyBounded W) :
    (peripheralLetterValues W).Finite := by
  refine ((hW.finiteComponentLetters.image GGT.RelLetter.val).union
    (hW.finiteComponentLetters.image fun a => a.val⁻¹)).subset ?_
  rintro x ⟨word, hword, a, ha, hcomp, hx | hx⟩
  · exact Or.inl ⟨a, ⟨hcomp, word, hword, ha⟩, hx.symm⟩
  · exact Or.inr ⟨a, ⟨hcomp, word, hword, ha⟩, hx.symm⟩

/-- **The letter pullback.**  Every quotient relative ball is the image of a source
relative ball, after adjoining the peripheral letter values of the relators to the
source base. -/
def QuotientPeripheralLetterPullbackAt
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (W : Set (List (GGT.RelLetter G Lambda)))
    (q : G →* Q) (hq : Function.Surjective q) : Prop :=
  ∃ R : ℕ → ℕ, ∀ (lam : Lambda) (n : ℕ),
    (D.mapSurjective q hq).relBall lam n ⊆
      q '' (GGT.RelHyp.adjoinBase D (peripheralLetterValues W)
        (inv_mem_peripheralLetterValues W)).relBall lam (R n)

/-- **Clause (b) from the letter pullback.** -/
theorem locallyFinite_mapSurjective_of_letterPullback
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (W : Set (List (GGT.RelLetter G Lambda)))
    (q : G →* Q) (hq : Function.Surjective q) (hD : D.IsHyperbolicallyEmbedded)
    (hW : RelWord.IsStronglyBounded W) (h : QuotientPeripheralLetterPullbackAt D W q hq) :
    ∀ (lam : Lambda) (n : ℕ), ((D.mapSurjective q hq).relBall lam n).Finite := by
  obtain ⟨R, hR⟩ := h
  intro lam n
  exact ((GGT.RelHyp.relBall_finite_adjoinBase D (peripheralLetterValues W)
    (inv_mem_peripheralLetterValues W) (finite_peripheralLetterValues hW) hD lam
      (R n)).image q).subset (hR lam n)

/-- **The letter pullback at the inputs of the embedded bridge**: Dahmani--Guirardel--Osin's
Theorem 4.24, from linear relative area to local finiteness, in the form the bridge
consumes. -/
def QuotientPeripheralLetterPullbackStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
    ∀ (eps rho : ℕ) (mu : ℝ) (W : Set (List (GGT.RelLetter G Lambda)))
      {Q : Type v} [Group Q] (q : G →* Q) (hq : Function.Surjective q),
      0 < mu → mu ≤ 1 / 1000 → 20 * (eps + 1) ≤ rho →
      RelWord.IsBoundedLemma44Input D W eps mu rho →
      q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
      (∀ (R : ℕ) (Z : RelativeLeastAreaDiagram D W R),
        Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
          Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)) →
        QuotientPeripheralLetterPullbackAt D W q hq

/-- **The embedded Lemma 5.1 bridge from the letter pullback.**  Clause (a) is
`hyperbolic_mapSurjective_of_leastAreaCertificates`; clause (b) is the letter
pullback with the finiteness of the peripheral letter values. -/
theorem relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback
    (hpull : QuotientPeripheralLetterPullbackStatement.{u, v, w}) :
    RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, v, w} := by
  intro G _ Lambda D hD eps rho mu W Q _ q hq hmu hmuUpper hrho hsc hker hcert
  exact ⟨hyperbolic_mapSurjective_of_leastAreaCertificates D hD hsc hmuUpper hrho q hq hker
      hcert,
    locallyFinite_mapSurjective_of_letterPullback D W q hq hD hsc.isStronglyBounded
      (hpull D hD eps rho mu W q hq hmu hmuUpper hrho hsc hker hcert)⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.inv_mem_peripheralLetterValues
#audit_axioms GroupApproximation.HullSC.finite_peripheralLetterValues
#audit_axioms GroupApproximation.HullSC.locallyFinite_mapSurjective_of_letterPullback
#audit_axioms GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback
