import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.HullSCLemma44QuotientRelGenSet
import GroupApproximation.GGT.HullSCLemma44RelativeBoundary
import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement

/-!
# The relative-isoperimetric bridge in Hull's Lemma 4.4

Osin's proof of Theorem 4.1 uses the exterior cell from Lemma 4.4 in an
induction on the boundary length.  The induction has two outputs.  First, the
quotient relative Cayley graph satisfies a four-point inequality.  Second,
every quotient relative-metric ball is contained in the image of one source
relative-metric ball.  The latter inclusion makes the quotient ball finite.

This file isolates those two outputs in `RelativeIsoperimetricControl` and
proves that they imply hyperbolic embeddedness of the image peripheral family.
The remaining diagram induction is stated by
`RelativeIsoperimetricBridgeStatement`.  Its hypothesis is the certificate
form of Osin's Lemma 4.4 for every reduced diagram, rather than a second
geometric premise.  Thus the statement is the exact bridge from the vk lane's
certificate to the two clauses used by the quotient consumer.

The source correspondence is Osin, *Small cancellations over relatively
hyperbolic groups and embedding theorems*, proof of Lemma 5.1: equations
`(18)`--`(21)` give the linear relative-area induction, Lemma 2.27 controls
isolated peripheral components, and Theorem 1.7 converts the resulting
relative isoperimetric inequality to hyperbolicity of the relative Cayley
graph.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u v w

/-- A uniform pullback bound for quotient relative balls.  It is the local
finiteness output of Osin's relative-area induction: an avoiding quotient path
of length `n` has an endpoint represented by an element in a fixed source
relative ball. -/
def PeripheralPullbackBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (radius : ℕ → ℕ) : Prop :=
  ∀ (lam : Lambda) (n : ℕ),
    (D.mapSurjective q hq).relBall lam n ⊆ q '' D.relBall lam (radius n)

/-- A pullback bound transfers local finiteness from the source peripheral
metrics to the quotient peripheral metrics. -/
theorem locallyFinite_mapSurjective_of_pullbackBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (q : G →* Q) (hq : Function.Surjective q) (radius : ℕ → ℕ)
    (hpull : PeripheralPullbackBound D q hq radius) :
    ∀ (lam : Lambda) (n : ℕ),
      ((D.mapSurjective q hq).relBall lam n).Finite := by
  intro lam n
  exact ((hD.locallyFinite lam (radius n)).image q).subset (hpull lam n)

/-- The two concrete conclusions of the relative isoperimetric argument.
`fourPoint` is the graph-hyperbolicity output, while `peripheralPullback` is
the bounded-lift output used for properness of every transported relative
metric. -/
structure RelativeIsoperimetricControl
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) where
  delta : ℕ
  fourPoint : Hyperbolic.IsFourPointHyperbolic
    (D.mapSurjective q hq).alphabet.carrier delta
  peripheralRadius : ℕ → ℕ
  peripheralPullback :
    PeripheralPullbackBound D q hq peripheralRadius

namespace RelativeIsoperimetricControl

/-- Osin's two isoperimetric outputs give the repository's exact
`IsHyperbolicallyEmbedded` structure for the quotient image family. -/
theorem embedded
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} (hD : D.IsHyperbolicallyEmbedded)
    {q : G →* Q} {hq : Function.Surjective q}
    (C : RelativeIsoperimetricControl D q hq) :
    (D.mapSurjective q hq).IsHyperbolicallyEmbedded := by
  refine ⟨⟨(C.delta : ℝ), ?_⟩, ?_⟩
  · exact GGT.isHyperbolicSpace_cayley_of_fourPoint
      (D.mapSurjective q hq).alphabet C.fourPoint
  · exact locallyFinite_mapSurjective_of_pullbackBound D hD q hq
      C.peripheralRadius C.peripheralPullback

end RelativeIsoperimetricControl

/-! ## The relative Dehn transfer -/

/-- Pointwise form of Osin Lemma 5.1 after the diagram argument has been
reduced to local one-cell cuts.  Strong boundedness is retained as the finite
component-letter support used for the quotient peripheral metrics. -/
def RelativeDehnTransferAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (W : Set (List (GGT.RelLetter G Lambda))) (eps : ℕ)
    {Q : Type v} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q),
    {a : GGT.RelLetter G Lambda |
      (∃ lam h, a = GGT.RelLetter.comp lam h) ∧
        ∃ relator ∈ W, a ∈ relator}.Finite →
      (∀ boundaryWord : List G,
        IsWord D.alphabet.carrier boundaryWord boundaryWord.prod →
        boundaryWord.prod ≠ 1 → q boundaryWord.prod = 1 →
          Nonempty (RelativeDehnCut D W eps q boundaryWord)) →
            Nonempty (RelativeIsoperimetricControl D q hq)

/-- Uniform relative Dehn transfer over every hyperbolically embedded source
family.  This is Osin Lemma 5.1 followed by the relative-presentation
characterization of hyperbolicity used in Theorem 1.7. -/
def RelativeDehnTransferStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded → RelativeDehnTransferAt.{u, v, w} D

/-- Osin Lemma 5.1, phrased as the bridge consumed by Hull Lemma 4.4.

The certificate hypothesis is available for every boundary radius and every
reduced diagram over the chosen family.  The conclusion is strictly below the
canonical Hull quotient statement: it concerns only the image relative
generating set, with no prescribed Cayley ball and no auxiliary-family
packaging. -/
def RelativeIsoperimetricBridgeAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (eps rho : ℕ) (mu : ℝ)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {Q : Type v} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q),
    0 < mu → mu ≤ 1 / 1000 →
      20 * (eps + 1) ≤ rho →
      RelWord.IsLemma44Input D W eps mu rho →
      q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
        (∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
          Nonempty (RelativeDiagramCertificate D W eps mu Z)) →
            Nonempty (RelativeIsoperimetricControl D q hq)

/-- Uniform form of Osin's relative-isoperimetric induction over all source
relative generating sets. -/
def RelativeIsoperimetricBridgeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded → RelativeIsoperimetricBridgeAt.{u, v, w} D

/-- The local Dehn transfer proves the certificate-form isoperimetric bridge.
The only diagram use is the prescribed-boundary construction and certificate
cut; all quotient geometry is delegated to Osin Lemma 5.1's exact transfer. -/
theorem relativeIsoperimetricBridgeStatement_of_dehnTransfer
    (htransfer : RelativeDehnTransferStatement.{u, v, w}) :
    RelativeIsoperimetricBridgeStatement.{u, v, w} := by
  intro G _ Lambda D hD eps rho mu W Q _ q hq hmu hmuUpper hrho
    hsc hker hcert
  apply htransfer D hD W eps q hq hsc.stronglyBounded
  intro boundaryWord hword hne hmap
  exact exists_relativeDehnCut_of_kernelWord D hsc hmuUpper hrho q hker
    hcert boundaryWord hword hne hmap

/-- The bridge statement, followed by its elementary consumer, proves
hyperbolic embeddedness of the concrete quotient image family. -/
theorem isHyperbolicallyEmbedded_mapSurjective_of_bridge
    (hbridge : RelativeIsoperimetricBridgeStatement.{u, v, w})
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    {eps rho : ℕ} {mu : ℝ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (q : G →* Q) (hq : Function.Surjective q)
    (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    (D.mapSurjective q hq).IsHyperbolicallyEmbedded := by
  obtain ⟨C⟩ := hbridge D hD eps rho mu W q hq hmu hmuUpper
    hrho hsc hker hcert
  exact C.embedded hD

/-- Relative-isoperimetric control and injectivity on the selected peripheral
union give Hull's complete peripheral-preservation object. -/
theorem quotientPeripheralPreservation_of_isoperimetricControl
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (C : RelativeIsoperimetricControl D.rel q hq)
    (hinj : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G))) :
    Nonempty (QuotientPeripheralPreservation q D) := by
  exact quotientPeripheralPreservation_of_mapSurjective D q hq
    (C.embedded D.embedded) hinj

/-! ## Degenerate and source-only checks -/

/-- For an empty relator family, the kernel equation makes a surjective map
bijective.  Hyperbolic embeddedness then follows from exact isomorphism
transport, independently of the diagram certificate. -/
theorem isHyperbolicallyEmbedded_mapSurjective_emptyFamily
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure
      (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G Lambda))))) :
    (D.mapSurjective q hq).IsHyperbolicallyEmbedded := by
  have hbot : q.ker = ⊥ := by
    simpa only [Set.image_empty, Subgroup.normalClosure_empty] using hker
  have hinj : Function.Injective q :=
    (MonoidHom.ker_eq_bot_iff q).mp hbot
  exact GGT.RelGenSet.isHyperbolicallyEmbedded_mapSurjective_of_bijective
    D hD q ⟨hinj, hq⟩

/-- The empty-family branch of the relative-isoperimetric consumer is valid
for every source family.  This checks that the bridge has the expected
zero-cell model. -/
theorem relativeIsoperimetricBridge_emptyFamilyModel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure
      (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G Lambda))))) :
    (D.mapSurjective q hq).IsHyperbolicallyEmbedded :=
  isHyperbolicallyEmbedded_mapSurjective_emptyFamily D hD q hq hker

/-- The pullback assertion has a direct one-point source model: every quotient
element is the image of `1`, which lies in the radius-zero source ball. -/
theorem peripheralPullbackBound_trivialSource
    {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet PUnit Lambda) (q : PUnit →* Q)
    (hq : Function.Surjective q) :
    PeripheralPullbackBound D q hq (fun _ => 0) := by
  haveI : Subsingleton Q :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hq x
      obtain ⟨b, rfl⟩ := hq y
      rw [Subsingleton.elim a b]⟩
  intro lam n y hy
  refine ⟨1, ?_, Subsingleton.elim _ _⟩
  rw [GGT.RelGenSet.relBall_zero]
  exact Set.mem_singleton_iff.mpr rfl

/-- The pointwise bridge proposition is inhabited on every relative
generating set of the one-point group.  This tests the quantifier order,
quotient universes, certificate input, and concrete control output. -/
theorem relativeIsoperimetricBridgeAt_trivialSourceModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    RelativeIsoperimetricBridgeAt.{0, v, w} D := by
  intro eps rho mu W Q _ q hq hmu hmuUpper hrho hsc hker hcert
  haveI : Subsingleton Q :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hq x
      obtain ⟨b, rfl⟩ := hq y
      rw [Subsingleton.elim a b]⟩
  refine ⟨⟨0, ?_, fun _ => 0, ?_⟩⟩
  · intro a b c d
    rw [Subsingleton.elim a b, Subsingleton.elim c b,
      Subsingleton.elim d b]
    simp only [WordMetric.wordDist_self, zero_add, max_self, mul_zero,
      le_refl]
  · exact peripheralPullbackBound_trivialSource D q hq

/-- The pointwise Dehn transfer has the one-point source model.  Every
surjective target is a one-point group, so its four-point constant and
peripheral pullback radius are both zero. -/
theorem relativeDehnTransferAt_trivialSourceModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    RelativeDehnTransferAt.{0, v, w} D := by
  intro W eps Q _ q hq hsupport hcuts
  haveI : Subsingleton Q :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hq x
      obtain ⟨b, rfl⟩ := hq y
      rw [Subsingleton.elim a b]⟩
  refine ⟨⟨0, ?_, fun _ => 0, ?_⟩⟩
  · intro a b c d
    rw [Subsingleton.elim a b, Subsingleton.elim c b,
      Subsingleton.elim d b]
    simp only [WordMetric.wordDist_self, zero_add, max_self, mul_zero,
      le_refl]
  · exact peripheralPullbackBound_trivialSource D q hq

/-- In a one-point source group every surjective quotient is a one-point
group.  Its image relative Cayley graph has zero word distance and every
relative ball is finite. -/
theorem relativeIsoperimetricBridge_trivialSourceModel
    {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet PUnit Lambda) (q : PUnit →* Q)
    (hq : Function.Surjective q) :
    (D.mapSurjective q hq).IsHyperbolicallyEmbedded := by
  haveI : Subsingleton Q :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hq x
      obtain ⟨b, rfl⟩ := hq y
      rw [Subsingleton.elim a b]⟩
  haveI : Finite Q := Finite.of_surjective q hq
  refine ⟨⟨0, ?_⟩, ?_⟩
  · intro a b c d
    have heq : ∀ x y : Cayley (D.mapSurjective q hq).alphabet, x = y := by
      intro x y
      change Cayley.val x = Cayley.val y
      exact Subsingleton.elim _ _
    rw [heq a b, heq c b, heq d b]
    simp only [gromovProduct, dist_self, zero_add, sub_zero, min_self]
    norm_num
  · intro lam n
    exact Set.toFinite _

end HullSC
end GroupApproximation
