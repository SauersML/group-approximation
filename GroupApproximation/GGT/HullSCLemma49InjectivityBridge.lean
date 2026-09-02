import GroupApproximation.GGT.HullSCLemma44KernelAssembly
import GroupApproximation.GGT.HullSCLemma49SourceGreendlinger

/-!
# Interfaces for the two remaining Lemma 4.9 handoffs

Hull's Lemma 4.4 supplies injectivity on a relative Cayley ball from its
relative Greendlinger certificate.  This file specializes that output to the
`IsLemma49Input` family used by the power-diagram branches.  The canonical
Hull 4.4 statement is quantified over an auxiliary peripheral family, while
the power-diagram statement is quantified over an arbitrary hyperbolically
embedded relative generating set, so the callback retains the latter
embeddedness witness explicitly.

The source Greendlinger certificate also needs a cellular face-pasting
certificate.  `HullLemma49SourceFacePastingStatement` is precisely the
strictly smaller certificate consumed by the two cyclic-arc branches: the
selected G-cell faces paste to the empty boundary word.  Its PUnit model is
vacuous because a nontrivial power diagram cannot exist there.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The injectivity callback -/

/-- The ball-injectivity output needed by the source-faithful Lemma 4.9
assembly.  The quotient has the source universe, as does the quotient used by
the manuscript power-diagram statement. -/
def HullLemma49InjectivityCallback : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
    ∀ (delta : ℕ),
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Lambda)))
          {Q : Type u} [Group Q] (q : G →* Q),
          RelWord.IsLemma49Input D W eps mu rho →
          q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
            Set.InjOn q (cayleyBall D.alphabet (8 * delta + 1))

/-- Hull's Lemma 4.4 injectivity theorem gives the exact source callback after
converting a Lemma 4.9 input to its Lemma 4.4 input. -/
theorem hullLemma49InjectivityCallback_of_relativeGreendlinger
    (hgeom : RelativeGreendlingerStatement.{u, w}) :
    HullLemma49InjectivityCallback.{u, w} := by
  intro G _ Lambda D hD delta _hdelta
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    exists_relativeBallInjectivityParameters_of_greendlinger
      hgeom D hD (8 * delta + 1)
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hker
  exact hgood W q hinput.toIsLemma44Input hker

/-! ## The auxiliary-family form of the exported Hull 4.4 output -/

/-- The injectivity component of the exported canonical Hull 4.4 conclusion,
spelled out so an auxiliary-family consumer can pass it to a hull49 callback.
This is the exact projection supplied by
`hullLemma44CanonicalQuotientStatement_zero_of_relativeGreendlinger_of_kernelGeodesic_of_prefixTransfer`.
-/
theorem hullLemma44InjectivityOutput_of_canonicalStatement
    (h44 : HullLemma44CanonicalQuotientStatement.{0})
    {G : Type} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S) (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
        {Q : Type} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D.rel W eps mu rho →
        Function.Surjective q →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall A.alphabet R) := by
  exact h44 D R

/-- The named hull44 kernel-assembly theorem supplies the same injectivity
projection for an auxiliary peripheral family. -/
theorem hullLemma44InjectivityOutput_of_relativeGreendlinger_of_kernelGeodesic_of_prefixTransfer
    (hgeom : RelativeGreendlingerStatement.{0, 0})
    (hkernel : KernelGeodesicEstimateStatement.{0, 0, 0})
    (htransfer : PrefixKernelConeTransferStatement.{0, 0, 0})
    {G : Type} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S) (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
        {Q : Type} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D.rel W eps mu rho →
        Function.Surjective q →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall A.alphabet R) := by
  exact hullLemma44InjectivityOutput_of_canonicalStatement
    (h44 :=
      hullLemma44CanonicalQuotientStatement_zero_of_relativeGreendlinger_of_kernelGeodesic_of_prefixTransfer
        hgeom hkernel htransfer)
    D R

/-! ## The face-pasting certificate -/

/-- Every source Greendlinger power certificate has a cellular homotopy from
the designated selected-face boundary to the empty word.  This is the exact
certificate required by `Embedded.Contiguity.arcs_value_of_pasting`. -/
def HullLemma49SourceFacePastingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
      D v g n eps mu Z),
    Nonempty (GGT.VanKampen.Embedded.FaceSetWordHomotopy
      C.diagram C.faces C.contiguity.boundary.cycle [])

/-! ## Model checks -/

/-- A map out of the PUnit source is injective, so the callback is inhabited in
the trivial source model. -/
theorem hullLemma49InjectivityCallback_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    ∀ (delta : ℕ),
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter PUnit Lambda)))
          {Q : Type} [Group Q] (q : PUnit →* Q),
          RelWord.IsLemma49Input D W eps mu rho →
          q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
            Set.InjOn q (cayleyBall D.alphabet (8 * delta + 1)) := by
  intro delta _hdelta
  refine ⟨0, 0, 1, by norm_num, ?_⟩
  intro W Q _ q _hinput _hker x _hx y _hy _hxy
  exact Subsingleton.elim x y

/-- The face-pasting statement is vacuous for a PUnit source: its power
diagram field contradicts the fact that every PUnit element is one. -/
theorem hullLemma49SourceFacePastingStatement_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    ∀ {v : List (GGT.RelLetter PUnit Lambda)} {g : PUnit} {n eps : ℕ}
      {mu : ℝ} {Z : Lemma49GeodesicPowerDiagram D v g n},
      (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
        D v g n eps mu Z) →
      Nonempty (GGT.VanKampen.Embedded.FaceSetWordHomotopy
        C.diagram C.faces C.contiguity.boundary.cycle []) := by
  intro v g n eps mu Z C
  exact (Z.power_ne_one (Subsingleton.elim _ _)).elim

end HullSC
end GroupApproximation
