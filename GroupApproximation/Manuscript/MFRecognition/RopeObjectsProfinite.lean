import GroupApproximation.GroupTheory.CentralHNNResiduallyFinite
import GroupApproximation.Higman.MikhailovaGraphProductProfiniteWitness
import GroupApproximation.Manuscript.MFRecognition.RopeObjects
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Profinite semantics of the concrete manuscript rope input

The manuscript's first rope does not use Higman's generic join construction.
Its ambient embedding is the product of two first-coordinate embeddings, and
its cutter is the direct product of a Mikhailova fibre product and a graph.
Consequently every image transport is split.  Residual finiteness of the
finite-presentation host is the only additional positive-branch hypothesis.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Rope
namespace RopeInput

open GroupApproximation.Higman

noncomputable section

variable (inp : RopeInput)

/-- The marked Mikhailova coordinate of `iEmb` is split by first projection. -/
theorem i0_cofinal : CofinalProfiniteEmbedding (i0 inp) :=
  CofinalProfiniteEmbedding.postcomp_of_retraction
    CofinalProfiniteEmbedding.id (i0 inp)
    MikhailovaRankThree.inputProjection
    (MikhailovaRankThree.inputProjection_comp_inputHom inp.words)

/-- The marked Mikhailova coordinate has closed range for the same split
reason. -/
theorem i0_closed :
    profiniteClosure (i0 inp).range = (i0 inp).range :=
  MikhailovaRankThree.profiniteClosure_inputHom_range inp.words

/-- The graph coordinate of `iEmb` is split by first projection. -/
theorem graphInput_cofinal :
    CofinalProfiniteEmbedding
      (MikhailovaGraphProduct.graphInput (P := Ptarget)) :=
  CofinalProfiniteEmbedding.postcomp_of_retraction
    CofinalProfiniteEmbedding.id
    (MikhailovaGraphProduct.graphInput (P := Ptarget))
    (MonoidHom.fst Fxyt Ptarget) (by ext f; rfl)

/-- The graph coordinate of `iEmb` has closed range. -/
theorem graphInput_closed :
    profiniteClosure
        (MikhailovaGraphProduct.graphInput (P := Ptarget)).range =
      (MikhailovaGraphProduct.graphInput (P := Ptarget)).range := by
  letI : Group.ResiduallyFinite (Fxyt × Ptarget) := inferInstance
  exact profiniteClosure_range_eq_range_of_retraction
    (MikhailovaGraphProduct.graphInput (P := Ptarget))
    (MonoidHom.fst Fxyt Ptarget) (by ext f; rfl)

/-- The exact manuscript embedding has cofinal finite quotients. -/
theorem iEmb_cofinal : CofinalProfiniteEmbedding (iEmb inp) := by
  change CofinalProfiniteEmbedding
    ((i0 inp).prod (MikhailovaGraphProduct.graphInput (P := Ptarget)))
  exact CofinalProfiniteEmbedding.prod_left (i0_cofinal inp)
    (MikhailovaGraphProduct.graphInput (P := Ptarget))

/-- The exact manuscript embedding has closed range. -/
theorem iEmb_closed :
    profiniteClosure (iEmb inp).range = (iEmb inp).range := by
  change profiniteClosure
      ((i0 inp).prod
        (MikhailovaGraphProduct.graphInput (P := Ptarget))).range = _
  exact profiniteClosure_prod_range (i0_cofinal inp) (i0_closed inp)

/-- The concrete cutter `L_e = L⁰_e × Lᵍ_e` is closed.  The first factor is
the Mikhailova fibre product for the RF host quotient, while the second is
the range of a split graph map. -/
theorem Le_closed
    [Group.ResiduallyFinite
      (FreeGroup inp.X ⧸ Subgroup.normalClosure inp.R)] :
    profiniteClosure (Le inp) = Le inp := by
  have h0 : profiniteClosure (L0 inp) = L0 inp :=
    MikhailovaRankThree.profiniteClosure_cuttingSubgroup inp.R
  have hg : profiniteClosure (Lg inp) = Lg inp := by
    exact profiniteClosure_range_eq_range_of_retraction
      (MikhailovaGraphProduct.graphHom (jq inp))
      (MonoidHom.fst Fxyt Ptarget)
      (MikhailovaGraphProductProfinite.fst_comp_graphHom (jq inp))
  have hprod : Le inp =
      (L0 inp).comap (MonoidHom.fst (K0 inp) Kg) ⊓
        (Lg inp).comap (MonoidHom.snd (K0 inp) Kg) := by
    ext z
    rfl
  rw [hprod]
  exact BenignDirectProductResiduallyFinite.profiniteClosure_inf_eq_of_closed
    _ _
    (profiniteClosure_comap_eq_of_closed (L0 inp)
      (MonoidHom.fst (K0 inp) Kg) h0)
    (profiniteClosure_comap_eq_of_closed (Lg inp)
      (MonoidHom.snd (K0 inp) Kg) hg)

/-- The exact benign witness packaged by `RopeObjects` carries all four
profinite fields.  This bypasses both generic `mapEmb` and generic benign
join: the two factors are the literal Mikhailova and graph factors of the
compiler. -/
def profiniteWitness
    [Group.ResiduallyFinite
      (FreeGroup inp.X ⧸ Subgroup.normalClosure inp.R)] :
    ProfiniteBenignWitness inp.N where
  witness := witness inp
  ambientRF := by
    change Group.ResiduallyFinite (K0 inp × Kg)
    infer_instance
  cutterClosed := Le_closed inp
  embCofinal := iEmb_cofinal inp
  embClosed := iEmb_closed inp

/-- The concrete first rope of the manuscript is residually finite whenever
the finite-presentation host is residually finite. -/
theorem centralRope_residuallyFinite
    [Group.ResiduallyFinite
      (FreeGroup inp.X ⧸ Subgroup.normalClosure inp.R)] :
    Group.ResiduallyFinite (CentralRope inp) := by
  let u := profiniteWitness inp
  letI : Group.ResiduallyFinite u.witness.K := u.ambientRF
  exact CentralHNNResiduallyFinite.centralHNN_residuallyFinite
    u.witness.L u.cutterClosed

/-- Hence a countable concrete first rope is operator-MF. -/
theorem centralRope_isOperatorMF
    [Group.ResiduallyFinite
      (FreeGroup inp.X ⧸ Subgroup.normalClosure inp.R)]
    [Countable (CentralRope inp)] :
    IsOperatorMF (CentralRope inp) := by
  letI : Group.ResiduallyFinite (CentralRope inp) :=
    centralRope_residuallyFinite inp
  exact isOperatorMF_of_residuallyFinite

end

end RopeInput
end Rope
end MFRecognition
end Manuscript
end GroupApproximation
