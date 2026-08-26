import GroupApproximation.Higman.BenignDirectProductResiduallyFinite
import GroupApproximation.Higman.BenignJoinResiduallyFinite
import GroupApproximation.Higman.BenignAmbient

/-!
# Benign witnesses with cofinal finite quotients

Residual finiteness of the ambient and closedness of the cutter are not by
themselves enough to iterate Higman's benign operations: later finite-cover
arguments must also refine prescribed finite quotients of the embedded source
group.  `CofinalProfiniteEmbedding` records exactly this quotient-refinement
property, and `ProfiniteBenignWitness` packages the three invariants.

The direct-product operations preserve all three fields.  For Higman's join,
the ambient RF and quotient-refinement fields are also unconditional; the one
remaining field is precisely profinite closedness of `joinL`.  The image
operation (`BenignWitness.mapEmb`) has a genuinely different amalgamated
lifting obligation and is intentionally not claimed here.
-/

namespace GroupApproximation
namespace Higman

noncomputable section

variable {G K N : Type} [Group G] [Group K] [Group N]

/-- Finite quotients of `G` are cofinally refined by restrictions of finite
quotients of `K` along `f`.  Kernel containment is the useful direction: a
finite quotient of `K` may remember more than the prescribed quotient of
`G`, but never less. -/
def CofinalProfiniteEmbedding (f : G →* K) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (q : G →* Q),
    ∃ (R : Type) (_ : Group R) (_ : Finite R) (p : K →* R),
      p.ker.comap f ≤ q.ker

namespace CofinalProfiniteEmbedding

/-- The identity embedding has the quotient-refinement property. -/
theorem id : CofinalProfiniteEmbedding (MonoidHom.id G) := by
  intro Q _ _ q
  refine ⟨Q, inferInstance, inferInstance, q, ?_⟩
  intro g hg
  exact hg

/-- One cofinal coordinate suffices for a product embedding. -/
theorem prod_left {K₂ : Type} [Group K₂] {f : G →* K} (h :
    CofinalProfiniteEmbedding f) (f₂ : G →* K₂) :
    CofinalProfiniteEmbedding (f.prod f₂) := by
  intro Q _ _ q
  obtain ⟨R, hRgroup, hRfinite, p, hp⟩ := h Q q
  letI : Group R := hRgroup
  letI : Finite R := hRfinite
  refine ⟨R, inferInstance, inferInstance,
    p.comp (MonoidHom.fst K K₂), ?_⟩
  intro g hg
  apply hp
  change p (f g) = 1 at hg ⊢
  exact hg

/-- Cofinality survives postcomposition by a split embedding. -/
theorem postcomp_of_retraction {L : Type} [Group L] {f : G →* K}
    (h : CofinalProfiniteEmbedding f) (i : K →* L) (r : L →* K)
    (hri : r.comp i = MonoidHom.id K) :
    CofinalProfiniteEmbedding (i.comp f) := by
  intro Q _ _ q
  obtain ⟨R, hRgroup, hRfinite, p, hp⟩ := h Q q
  letI : Group R := hRgroup
  letI : Finite R := hRfinite
  refine ⟨R, inferInstance, inferInstance, p.comp r, ?_⟩
  intro g hg
  apply hp
  change p (r (i (f g))) = 1 at hg
  have hri_g := congrArg (fun u : K →* K ↦ u (f g)) hri
  change r (i (f g)) = f g at hri_g
  change p (f g) = 1
  rwa [hri_g] at hg

/-- Precomposition by an isomorphism preserves cofinality. -/
theorem precomp_equiv {G' : Type} [Group G'] {f : G →* K}
    (h : CofinalProfiniteEmbedding f) (e : G' ≃* G) :
    CofinalProfiniteEmbedding (f.comp e.toMonoidHom) := by
  intro Q _ _ q
  obtain ⟨R, hRgroup, hRfinite, p, hp⟩ :=
    h Q (q.comp e.symm.toMonoidHom)
  letI : Group R := hRgroup
  letI : Finite R := hRfinite
  refine ⟨R, inferInstance, inferInstance, p, ?_⟩
  intro g hg
  apply hp at hg
  change q (e.symm (e g)) = 1 at hg
  simpa using hg

end CofinalProfiniteEmbedding

/-- A benign witness carrying the three profinite invariants needed by the
finite-quotient compiler. -/
structure ProfiniteBenignWitness (H : Subgroup G) where
  witness : BenignWitness H
  ambientRF : Group.ResiduallyFinite witness.K
  cutterClosed : profiniteClosure witness.L = witness.L
  embCofinal : CofinalProfiniteEmbedding witness.emb

/-- A finitely presented overgroup whose embedding induces the full profinite
topology on the source. -/
structure ProfiniteFPOvergroup (G : Type) [Group G] where
  overgroup : FPOvergroup G
  ambientRF : Group.ResiduallyFinite overgroup.K
  embCofinal : CofinalProfiniteEmbedding overgroup.emb

namespace ProfiniteBenignWitness

variable {H₁ H₂ : Subgroup G}

/-- The intersection witness preserves all profinite data. -/
def inf (u₁ : ProfiniteBenignWitness H₁)
    (u₂ : ProfiniteBenignWitness H₂) :
    ProfiniteBenignWitness (H₁ ⊓ H₂) where
  witness := u₁.witness.inf u₂.witness
  ambientRF := by
    letI : Group.ResiduallyFinite u₁.witness.K := u₁.ambientRF
    letI : Group.ResiduallyFinite u₂.witness.K := u₂.ambientRF
    exact BenignDirectProductResiduallyFinite.inf_ambient_residuallyFinite
      u₁.witness u₂.witness
  cutterClosed :=
    BenignDirectProductResiduallyFinite.profiniteClosure_inf_L
      u₁.witness u₂.witness u₁.cutterClosed u₂.cutterClosed
  embCofinal :=
    CofinalProfiniteEmbedding.prod_left u₁.embCofinal u₂.witness.emb

/-- The preimage witness preserves all profinite data when the chosen
overgroup of the source already carries it. -/
def comap (u : ProfiniteFPOvergroup G) (phi : G →* N)
    {H : Subgroup N} (v : ProfiniteBenignWitness H) :
    ProfiniteBenignWitness (H.comap phi) where
  witness := v.witness.comap u.overgroup phi
  ambientRF := by
    letI : Group.ResiduallyFinite u.overgroup.K := u.ambientRF
    letI : Group.ResiduallyFinite v.witness.K := v.ambientRF
    exact BenignDirectProductResiduallyFinite.comap_ambient_residuallyFinite
      u.overgroup phi v.witness
  cutterClosed :=
    BenignDirectProductResiduallyFinite.profiniteClosure_comap_L
      u.overgroup phi v.witness v.cutterClosed
  embCofinal :=
    CofinalProfiniteEmbedding.prod_left u.embCofinal
      (v.witness.emb.comp phi)

/-- Transport along an isomorphism preserves all profinite data. -/
def congr {G' : Type} [Group G'] (e : G' ≃* G) {H : Subgroup G}
    (u : ProfiniteBenignWitness H) :
    ProfiniteBenignWitness (H.comap e.toMonoidHom) where
  witness := u.witness.congr e
  ambientRF := by
    letI : Group.ResiduallyFinite u.witness.K := u.ambientRF
    exact BenignDirectProductResiduallyFinite.congr_ambient_residuallyFinite
      (w := u.witness) e
  cutterClosed := by
    change profiniteClosure u.witness.L = u.witness.L
    exact u.cutterClosed
  embCofinal := CofinalProfiniteEmbedding.precomp_equiv u.embCofinal e

end ProfiniteBenignWitness

/-! ## The unconditional part of Higman's join -/

namespace ProfiniteBenignJoin

variable {A₁ A₂ : Subgroup G}
variable (u₁ : ProfiniteBenignWitness A₁)
variable (u₂ : ProfiniteBenignWitness A₂)

/-- The exact remaining profinite obligation for Higman's join witness.  The
other two fields (`ambientRF` and `embCofinal`) are proved below. -/
def CutterClosedObligation : Prop :=
  profiniteClosure (joinL u₁.witness u₂.witness) =
    joinL u₁.witness u₂.witness

/-- The two-HNN ambient of the join remains residually finite. -/
theorem ambient_residuallyFinite :
    Group.ResiduallyFinite (JoinLevel2 u₁.witness u₂.witness) := by
  letI : Group.ResiduallyFinite u₁.witness.K := u₁.ambientRF
  letI : Group.ResiduallyFinite u₂.witness.K := u₂.ambientRF
  exact BenignJoinResiduallyFinite.level2_residuallyFinite
    u₁.witness u₂.witness u₁.cutterClosed u₂.cutterClosed

/-- The diagonal source embedding into the product base has cofinal finite
quotients. -/
theorem baseEmbedding_cofinal :
    CofinalProfiniteEmbedding (joinEmb u₁.witness u₂.witness) :=
  CofinalProfiniteEmbedding.prod_left u₁.embCofinal u₂.witness.emb

/-- The source embedding remains cofinal after both central HNN stages.  Both
stable letters may be killed, so the two canonical base maps are split. -/
theorem embedding_cofinal :
    CofinalProfiniteEmbedding (joinEmb₂ u₁.witness u₂.witness) := by
  have h₁ := CofinalProfiniteEmbedding.postcomp_of_retraction
    (baseEmbedding_cofinal u₁ u₂)
    (HNNExtension.of : JoinBase u₁.witness u₂.witness →*
      JoinLevel1 u₁.witness u₂.witness)
    (CentralHNNFreeLabel.baseRet (joinM₁ u₁.witness u₂.witness))
    (BenignJoinResiduallyFinite.baseRet_comp_of u₁.witness u₂.witness
      (joinM₁ u₁.witness u₂.witness))
  exact CofinalProfiniteEmbedding.postcomp_of_retraction h₁
    (HNNExtension.of : JoinLevel1 u₁.witness u₂.witness →*
      JoinLevel2 u₁.witness u₂.witness)
    (CentralHNNFreeLabel.baseRet (joinM₂' u₁.witness u₂.witness))
    (by
      apply MonoidHom.ext
      intro g
      simp [CentralHNNFreeLabel.baseRet_of])

/-!
At this point the join has two of the three fields of a
`ProfiniteBenignWitness`.  The exact missing statement is

`CutterClosedObligation u₁ u₂`.

It needs finite-cover subgroup separability; it does not follow merely from
residual finiteness of the join ambient.  No conditional endpoint is declared.
-/

end ProfiniteBenignJoin

/-! ## The exact obligations for image transport -/

namespace ProfiniteBenignMapEmb

variable [Group.FG G] [Group.IsFinitelyPresented N]
variable {H : Subgroup G} (u : ProfiniteBenignWitness H)
variable (theta : G →* N) (htheta : Function.Injective theta)

/-- The three facts not supplied by the abstract amalgam normal form in
`BenignWitness.mapEmb`.  Unlike the direct-product and join-ambient results,
none follows from the current fields alone: they are a compatible finite-cover
problem for the particular amalgam `u.K *_G N`. -/
def LiftingObligations : Prop :=
  Group.ResiduallyFinite (u.witness.mapEmb theta htheta).K ∧
    profiniteClosure (u.witness.mapEmb theta htheta).L =
      (u.witness.mapEmb theta htheta).L ∧
    CofinalProfiniteEmbedding (u.witness.mapEmb theta htheta).emb

end ProfiniteBenignMapEmb

end


end Higman
end GroupApproximation
