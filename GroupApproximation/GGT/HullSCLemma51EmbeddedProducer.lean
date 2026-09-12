import GroupApproximation.GGT.HullSCLemma51QuotientStokes
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridge
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.Set.Finite.List
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
`λ`-component of the closing edge: every element of a quotient relative ball lifts to
a product of boundedly many *atoms*, each a value of a peripheral letter of a relator
or an element, or the inverse of an element, of a fixed source relative ball.
`QuotientPeripheralLetterPullbackAt` is that statement, with the atoms
`peripheralLetterValues W ∪ D.relBall λ (R n) ∪ (D.relBall λ (R n))⁻¹`.

It replaces the refuted `PeripheralPullbackBound`: in the counterexample recorded in
`GGT/HullSCLemma51EmbeddedBridge.lean` the element `q (t^m)` is the image of the single
atom `t^m`, the value of a peripheral letter of the relator.

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
open scoped Pointwise

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

/-- **Products of at most `N` elements of a set.** -/
def boundedProducts {G : Type u} [Group G] (A : Set G) (N : ℕ) : Set G :=
  {h | ∃ l : List G, l.length ≤ N ∧ (∀ x ∈ l, x ∈ A) ∧ l.prod = h}

/-- Boundedly many factors from a finite set have finitely many products. -/
theorem finite_boundedProducts {G : Type u} [Group G] {A : Set G} (hA : A.Finite) (N : ℕ) :
    (boundedProducts A N).Finite := by
  haveI : Finite A := hA.to_subtype
  refine ((List.finite_length_le A N).image fun l => (l.map Subtype.val).prod).subset ?_
  rintro h ⟨l, hlen, hmem, rfl⟩
  refine ⟨l.attach.map fun x => ⟨x.1, hmem x.1 x.2⟩, ?_, ?_⟩
  · show (l.attach.map _).length ≤ N
    rw [List.length_map, List.length_attach]
    exact hlen
  · show ((l.attach.map _).map Subtype.val).prod = l.prod
    rw [List.map_map]
    congr 1
    conv_rhs => rw [← List.attach_map_subtype_val l]
    rfl

/-- **The letter pullback.**  Every element of a quotient relative ball is the image
of a product of boundedly many atoms: values of peripheral letters of the relators,
and elements of a fixed source relative ball or their inverses. -/
def QuotientPeripheralLetterPullbackAt
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (W : Set (List (GGT.RelLetter G Lambda)))
    (q : G →* Q) (hq : Function.Surjective q) : Prop :=
  ∃ R N : ℕ → ℕ, ∀ (lam : Lambda) (n : ℕ),
    (D.mapSurjective q hq).relBall lam n ⊆
      q '' boundedProducts
        (peripheralLetterValues W ∪ D.relBall lam (R n) ∪ (D.relBall lam (R n))⁻¹) (N n)

/-- **Clause (b) from the letter pullback.** -/
theorem locallyFinite_mapSurjective_of_letterPullback
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (W : Set (List (GGT.RelLetter G Lambda)))
    (q : G →* Q) (hq : Function.Surjective q) (hD : D.IsHyperbolicallyEmbedded)
    (hW : RelWord.IsStronglyBounded W) (h : QuotientPeripheralLetterPullbackAt D W q hq) :
    ∀ (lam : Lambda) (n : ℕ), ((D.mapSurjective q hq).relBall lam n).Finite := by
  obtain ⟨R, N, hRN⟩ := h
  intro lam n
  have hball : (D.relBall lam (R n)).Finite := hD.locallyFinite lam (R n)
  have hA : (peripheralLetterValues W ∪ D.relBall lam (R n) ∪
      (D.relBall lam (R n))⁻¹).Finite :=
    ((finite_peripheralLetterValues hW).union hball).union hball.inv
  exact ((finite_boundedProducts hA (N n)).image q).subset (hRN lam n)

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
pullback with the finiteness of the atoms. -/
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
#audit_axioms GroupApproximation.HullSC.finite_boundedProducts
#audit_axioms GroupApproximation.HullSC.locallyFinite_mapSurjective_of_letterPullback
#audit_axioms GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback
