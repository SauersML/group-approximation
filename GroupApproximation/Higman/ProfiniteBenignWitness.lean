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

/-! ## Closed graph embeddings -/

/-- A product embedding has closed range when its first coordinate has closed
range and the full induced profinite topology, and the second target is
residually finite.  The proof compares the second coordinate in a finite
quotient, then uses cofinality of the first coordinate to make that comparison
well-defined on a finite image of the first target. -/
theorem profiniteClosure_prod_range
    {K₂ : Type} [Group K₂] [Group.ResiduallyFinite K₂]
    {f₁ : G →* K} {f₂ : G →* K₂}
    (hcofinal : CofinalProfiniteEmbedding f₁)
    (hclosed : profiniteClosure f₁.range = f₁.range) :
    profiniteClosure (f₁.prod f₂).range = (f₁.prod f₂).range := by
  apply le_antisymm
  · intro z hz
    have hzfst : z.1 ∈ profiniteClosure f₁.range := by
      intro Q _ _ q
      have hzq := hz Q (q.comp (MonoidHom.fst K K₂))
      obtain ⟨y, ⟨g, rfl⟩, hy⟩ := hzq
      refine ⟨f₁ g, ⟨g, rfl⟩, ?_⟩
      exact hy
    rw [hclosed] at hzfst
    obtain ⟨g, hg⟩ := hzfst
    refine ⟨g, Prod.ext hg ?_⟩
    by_contra hsecond
    have hd : (f₂ g)⁻¹ * z.2 ≠ 1 := by
      intro hd
      apply hsecond
      exact inv_mul_eq_one.mp hd
    obtain ⟨N, hN⟩ :=
      Group.exists_finiteIndexNormalSubgroup_notMem ((f₂ g)⁻¹ * z.2) hd
    letI := N.isNormal'
    letI := N.isFiniteIndex'
    let q : K₂ →* K₂ ⧸ N.toSubgroup := QuotientGroup.mk' N.toSubgroup
    have hqd : q ((f₂ g)⁻¹ * z.2) ≠ 1 := by
      intro hq
      apply hN
      exact (QuotientGroup.eq_one_iff ((f₂ g)⁻¹ * z.2)).mp hq
    obtain ⟨R, hRgroup, hRfinite, p, hp⟩ :=
      hcofinal (K₂ ⧸ N.toSubgroup) (q.comp f₂)
    letI : Group R := hRgroup
    letI : Finite R := hRfinite
    let test : K × K₂ →* R × (K₂ ⧸ N.toSubgroup) :=
      (p.comp (MonoidHom.fst K K₂)).prod
        (q.comp (MonoidHom.snd K K₂))
    have hztest := hz (R × (K₂ ⧸ N.toSubgroup)) test
    obtain ⟨y, ⟨g', rfl⟩, hy⟩ := hztest
    have hpEq : p (f₁ g') = p (f₁ g) := by
      have := congrArg Prod.fst hy
      simpa [test, hg] using this
    have hpmem : g⁻¹ * g' ∈ p.ker.comap f₁ := by
      change p (f₁ (g⁻¹ * g')) = 1
      calc
        p (f₁ (g⁻¹ * g')) = (p (f₁ g))⁻¹ * p (f₁ g') := by simp
        _ = 1 := by rw [hpEq, inv_mul_cancel]
    have hqmem := hp hpmem
    change q (f₂ (g⁻¹ * g')) = 1 at hqmem
    rw [map_mul, map_inv] at hqmem
    have hqgg : q (f₂ g') = q (f₂ g) := (inv_mul_eq_one.mp hqmem).symm
    have hqz : q (f₂ g') = q z.2 := by
      have := congrArg Prod.snd hy
      simpa [test] using this
    have hqgz : q (f₂ g) = q z.2 := hqgg.symm.trans hqz
    apply hqd
    rw [map_mul, map_inv, hqgz, inv_mul_cancel]
  · exact le_profiniteClosure (f₁.prod f₂).range

/-- A benign witness carrying the three profinite invariants needed by the
finite-quotient compiler. -/
structure ProfiniteBenignWitness (H : Subgroup G) where
  witness : BenignWitness H
  ambientRF : Group.ResiduallyFinite witness.K
  cutterClosed : profiniteClosure witness.L = witness.L
  embCofinal : CofinalProfiniteEmbedding witness.emb
  embClosed : profiniteClosure witness.emb.range = witness.emb.range

/-- A finitely presented overgroup whose embedding induces the full profinite
topology on the source. -/
structure ProfiniteFPOvergroup (G : Type) [Group G] where
  overgroup : FPOvergroup G
  ambientRF : Group.ResiduallyFinite overgroup.K
  embCofinal : CofinalProfiniteEmbedding overgroup.emb
  embClosed : profiniteClosure overgroup.emb.range = overgroup.emb.range

namespace ProfiniteBenignWitness

variable {H₁ H₂ : Subgroup G}

/-- A finitely generated, profinitely closed subgroup of an RF finitely
presented group has the tautological strengthened witness. -/
def ofClosedFG [Group.IsFinitelyPresented G] [Group.ResiduallyFinite G]
    {H : Subgroup G} (hfg : H.FG)
    (hclosed : profiniteClosure H = H) : ProfiniteBenignWitness H where
  witness := BenignWitness.ofFG hfg
  ambientRF := by
    change Group.ResiduallyFinite G
    infer_instance
  cutterClosed := hclosed
  embCofinal := CofinalProfiniteEmbedding.id
  embClosed := by
    change profiniteClosure (MonoidHom.id G).range = (MonoidHom.id G).range
    have hrange : (MonoidHom.id G).range = (⊤ : Subgroup G) := by
      ext g
      simp
    rw [hrange]
    exact profiniteClosure_top

/-- A residually finite finitely presented group is its own profinitely full
overgroup. -/
def selfOvergroup [Group.IsFinitelyPresented G] [Group.ResiduallyFinite G] :
    ProfiniteFPOvergroup G where
  overgroup := FPOvergroup.self G
  ambientRF := by
    change Group.ResiduallyFinite G
    infer_instance
  embCofinal := CofinalProfiniteEmbedding.id
  embClosed := by
    change profiniteClosure (MonoidHom.id G).range = (MonoidHom.id G).range
    have hrange : (MonoidHom.id G).range = (⊤ : Subgroup G) := by
      ext g
      simp
    rw [hrange]
    exact profiniteClosure_top

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
  embClosed := by
    letI : Group.ResiduallyFinite u₂.witness.K := u₂.ambientRF
    exact profiniteClosure_prod_range u₁.embCofinal u₁.embClosed

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
  embClosed := by
    letI : Group.ResiduallyFinite v.witness.K := v.ambientRF
    exact profiniteClosure_prod_range u.embCofinal u.embClosed

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
  embClosed := by
    have hrange : (u.witness.emb.comp e.toMonoidHom).range =
        u.witness.emb.range := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨e g, rfl⟩
      · rintro ⟨g, rfl⟩
        refine ⟨e.symm g, ?_⟩
        simp
    change profiniteClosure (u.witness.emb.comp e.toMonoidHom).range =
      (u.witness.emb.comp e.toMonoidHom).range
    rw [hrange]
    exact u.embClosed

/-- **RF-safe image transport along a split embedding.**

Instead of the generic amalgam witness from `BenignWitness.mapEmb`, intersect
the preimage `r⁻¹(H)` with the closed retract range `theta(G)`.  The
intersection is exactly `theta(H)`, and only the already-proved direct-product
operations are used.  This is the image construction consumed by diagonal and
factor inclusions in the concrete Higman compiler. -/
def mapSplit {N : Type} [Group N] [Group.IsFinitelyPresented N]
    [Group.ResiduallyFinite N] {H : Subgroup G}
    (u : ProfiniteBenignWitness H) (theta : G →* N) (r : N →* G)
    (hrt : r.comp theta = MonoidHom.id G)
    (hrangeFG : theta.range.FG) : ProfiniteBenignWitness (H.map theta) := by
  have hrangeClosed : profiniteClosure theta.range = theta.range := by
    exact profiniteClosure_range_eq_range_of_retraction theta r hrt
  let pre : ProfiniteBenignWitness (H.comap r) :=
    comap (selfOvergroup (G := N)) r u
  let ran : ProfiniteBenignWitness theta.range :=
    ofClosedFG hrangeFG hrangeClosed
  let both : ProfiniteBenignWitness (H.comap r ⊓ theta.range) := pre.inf ran
  have heq : H.comap r ⊓ theta.range = H.map theta := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnH, g, hgn⟩ := Subgroup.mem_inf.mp hn
      have hrg : r (theta g) = g := by
        have h := congrArg (fun f : G →* G ↦ f g) hrt
        exact h
      refine ⟨g, ?_, hgn⟩
      change r n ∈ H at hnH
      rwa [← hgn, hrg] at hnH
    · rintro ⟨g, hgH, rfl⟩
      apply Subgroup.mem_inf.mpr
      constructor
      · change r (theta g) ∈ H
        have h := congrArg (fun f : G →* G ↦ f g) hrt
        simpa using h ▸ hgH
      · exact ⟨g, rfl⟩
  rw [← heq]
  exact both

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

/-- The diagonal source embedding into the product base has closed range. -/
theorem baseEmbedding_closed :
    profiniteClosure (joinEmb u₁.witness u₂.witness).range =
      (joinEmb u₁.witness u₂.witness).range := by
  letI : Group.ResiduallyFinite u₂.witness.K := u₂.ambientRF
  exact profiniteClosure_prod_range u₁.embCofinal u₁.embClosed

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

/-- The source range stays closed through both split central HNN base maps. -/
theorem embedding_closed :
    profiniteClosure (joinEmb₂ u₁.witness u₂.witness).range =
      (joinEmb₂ u₁.witness u₂.witness).range := by
  letI : Group.ResiduallyFinite u₁.witness.K := u₁.ambientRF
  letI : Group.ResiduallyFinite u₂.witness.K := u₂.ambientRF
  letI : Group.ResiduallyFinite (JoinLevel1 u₁.witness u₂.witness) :=
    BenignJoinResiduallyFinite.level1_residuallyFinite
      u₁.witness u₂.witness u₁.cutterClosed
  have hbase1 : profiniteClosure
      ((joinEmb u₁.witness u₂.witness).range.map
        (HNNExtension.of : JoinBase u₁.witness u₂.witness →*
          JoinLevel1 u₁.witness u₂.witness)) =
      (joinEmb u₁.witness u₂.witness).range.map HNNExtension.of :=
    profiniteClosure_map_eq_of_split_closed
      (HNNExtension.of : JoinBase u₁.witness u₂.witness →*
        JoinLevel1 u₁.witness u₂.witness)
      (CentralHNNFreeLabel.baseRet (joinM₁ u₁.witness u₂.witness))
      (BenignJoinResiduallyFinite.baseRet_comp_of u₁.witness u₂.witness
        (joinM₁ u₁.witness u₂.witness))
      (joinEmb u₁.witness u₂.witness).range
      (baseEmbedding_closed u₁ u₂)
  letI : Group.ResiduallyFinite (JoinLevel2 u₁.witness u₂.witness) :=
    ambient_residuallyFinite u₁ u₂
  have hbase2 := profiniteClosure_map_eq_of_split_closed
    (HNNExtension.of : JoinLevel1 u₁.witness u₂.witness →*
      JoinLevel2 u₁.witness u₂.witness)
    (CentralHNNFreeLabel.baseRet (joinM₂' u₁.witness u₂.witness))
    (by
      apply MonoidHom.ext
      intro g
      simp [CentralHNNFreeLabel.baseRet_of])
    ((joinEmb u₁.witness u₂.witness).range.map
      (HNNExtension.of : JoinBase u₁.witness u₂.witness →*
        JoinLevel1 u₁.witness u₂.witness)) hbase1
  simpa only [joinEmb₂, MonoidHom.range_comp] using hbase2

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
    CofinalProfiniteEmbedding (u.witness.mapEmb theta htheta).emb ∧
    profiniteClosure (u.witness.mapEmb theta htheta).emb.range =
      (u.witness.mapEmb theta htheta).emb.range

end ProfiniteBenignMapEmb

end


end Higman
end GroupApproximation
