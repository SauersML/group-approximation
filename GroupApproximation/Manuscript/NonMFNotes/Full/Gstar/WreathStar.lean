import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.WreathCongr
import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.A5Relation
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed `W_{A₅} = A₅^(G_*/Γ_*) ⋊ G_*`

Manuscript `non_mf_group_notes.tex`, `cor:notes-a5-relation` (tex lines 2052--2073), for the
printed group: `W_K = K^(X) ⋊ G_*` with `X = G_*/Γ_*` (tex lines 1945--1946), `K = A₅`, and
`r` the lamp `(12)(34)` at the site `tΓ_*`.  `notesA5Relation` states the corollary for the
repository's model `AlternatingLampLiteral.WA` over the vertical group; this file transports it
to the literal wreath product over the literal ascending HNN extension `Gstar`.

Main declarations:

* `gstarCosetEquiv` — `G_*/Γ_* ≃ V/ι(Γ̄)`, equivariant along `gstarEquivVertical`;
* `WStar`, `rStar`, `lampStar` — the printed `W_{A₅}`, `r`, and `A₅^(X)`;
* `wstarEquiv` — `W_{A₅} ≃* AlternatingLampLiteral.WA`, with `wstarEquiv_rStar`;
* `notesA5RelationLiteral` — the corollary for the printed group, all clauses.
-/

namespace GroupApproximation.Full.NN05

open MarkedCompression ExplicitLinearModel
open Manuscript.NonMFSentences.IntroWitnessSignSentence (gammaEquiv)
open AlternatingLampLiteral (WA qA rA a5)

/-! ## The site sets -/

/-- `Γ_* ≤ G_*` corresponds to the level-zero copy `ι(Γ̄) ≤ V`. -/
theorem ofGamma_mem_range_iff (x : Gstar) :
    x ∈ ofGamma.range ↔ gstarEquivVertical x ∈ (iotaVertical conjD conjD_injective).range := by
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp h
    exact MonoidHom.mem_range.mpr ⟨gammaEquiv y, (gstarEquivVertical_ofGamma y).symm⟩
  · intro h
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp h
    refine MonoidHom.mem_range.mpr ⟨gammaEquiv.symm z, gstarEquivVertical.injective ?_⟩
    rw [gstarEquivVertical_ofGamma, MulEquiv.apply_symm_apply, hz]

/-- **The site sets agree**: `X = G_*/Γ_*` is the coset space `V/ι(Γ̄)`. -/
noncomputable def gstarCosetEquiv : GstarCosets ≃ Cosets conjD conjD_injective := by
  refine Quotient.congr gstarEquivVertical.toEquiv ?_
  intro a b
  dsimp
  rw [← Quotient.eq'', ← Quotient.eq'', QuotientGroup.eq, QuotientGroup.eq]
  have h := ofGamma_mem_range_iff (a⁻¹ * b)
  rw [map_mul, map_inv] at h
  exact h

theorem gstarCosetEquiv_mk (g : Gstar) :
    gstarCosetEquiv (QuotientGroup.mk g) =
      (QuotientGroup.mk (gstarEquivVertical g) : Cosets conjD conjD_injective) := rfl

/-- The site identification is equivariant along `gstarEquivVertical`. -/
theorem gstarCosetEquiv_smul (g : Gstar) (ξ : GstarCosets) :
    gstarCosetEquiv (g • ξ) = gstarEquivVertical g • gstarCosetEquiv ξ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ξ
  rw [MulAction.Quotient.smul_mk, gstarCosetEquiv_mk, gstarCosetEquiv_mk,
    MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, map_mul]

theorem gstarCosetEquiv_baseCoset :
    gstarCosetEquiv baseCoset = rootCoset conjD conjD_injective := by
  show (QuotientGroup.mk (gstarEquivVertical 1) : Cosets conjD conjD_injective) =
    QuotientGroup.mk 1
  rw [map_one]

/-- The printed witness site `tΓ_*` is the repository's witness site. -/
theorem gstarCosetEquiv_tSite :
    gstarCosetEquiv (stableLetter • baseCoset) = tSite conjD conjD_injective := by
  rw [gstarCosetEquiv_smul, gstarEquivVertical_stableLetter, gstarCosetEquiv_baseCoset]
  rfl

/-! ## The printed group and relator -/

noncomputable instance gstarCosetsDecEq : DecidableEq GstarCosets := Classical.decEq _

/-- **`W_{A₅} = A₅^(X) ⋊ G_*`** with `X = G_*/Γ_*` (tex lines 1945--1946). -/
abbrev WStar : Type := Wreath (alternatingGroup (Fin 5)) Gstar GstarCosets

/-- **`r`**: the lamp `(12)(34)` (with `Fin 5` labels, `(0 1)(2 3)`) at the site `tΓ_*`. -/
noncomputable def rStar : WStar :=
  SemidirectProduct.inl (Lamp.single (stableLetter • baseCoset) a5)

/-- The lamp subgroup `A₅^(X) ≤ W_{A₅}`. -/
abbrev lampStar : Subgroup WStar :=
  (SemidirectProduct.inl : Lamp (alternatingGroup (Fin 5)) GstarCosets →* WStar).range

/-- The printed `W_{A₅}` is the repository's `A₅`-lamp group. -/
noncomputable def wstarEquiv : WStar ≃* WA :=
  wreathCongr (alternatingGroup (Fin 5)) gstarEquivVertical gstarCosetEquiv gstarCosetEquiv_smul

theorem wstarEquiv_rStar : wstarEquiv rStar = rA := by
  have h1 : wstarEquiv rStar = SemidirectProduct.inl
      (lampCongr (alternatingGroup (Fin 5)) gstarCosetEquiv
        (Lamp.single (stableLetter • baseCoset) a5)) :=
    wreathCongr_inl (alternatingGroup (Fin 5)) gstarEquivVertical gstarCosetEquiv
      gstarCosetEquiv_smul (Lamp.single (stableLetter • baseCoset) a5)
  rw [h1, lampCongr_single, gstarCosetEquiv_tSite]
  rfl

/-! ## Transporting the clauses -/

theorem lampStar_eq_ker : (SemidirectProduct.rightHom : WStar →* Gstar).ker = lampStar :=
  ker_rightHom_eq_lampRange

theorem wstar_mem_ker_iff (x : WStar) :
    x ∈ (SemidirectProduct.rightHom : WStar →* Gstar).ker ↔ wstarEquiv x ∈ qA.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  show x.right = 1 ↔
    (wreathCongr (alternatingGroup (Fin 5)) gstarEquivVertical gstarCosetEquiv
      gstarCosetEquiv_smul x).right = 1
  rw [wreathCongr_right]
  exact (MulEquiv.map_eq_one_iff gstarEquivVertical).symm

/-- `Rad_MF(W_{A₅}) = A₅^(X)` for the printed group. -/
theorem wstar_radical : actualCoronaMFResidual WStar = lampStar := by
  have hWA : actualCoronaMFResidual WA = qA.ker :=
    SpectralPaper.oneInvisibleRelationPackage.2.2.2.2.2.2.2.2.2.2.2.2.1
  ext x
  rw [mem_iff_of_map_eq wstarEquiv (map_actualCoronaMFResidual_mulEquiv wstarEquiv) x, hWA,
    ← lampStar_eq_ker, wstar_mem_ker_iff]

theorem map_normalClosure_rStar :
    (Subgroup.normalClosure {rStar}).map wstarEquiv.toMonoidHom =
      Subgroup.normalClosure {rA} := by
  rw [Subgroup.map_normalClosure _ wstarEquiv.toMonoidHom wstarEquiv.surjective,
    Set.image_singleton]
  exact congrArg (fun r : WA => Subgroup.normalClosure {r}) wstarEquiv_rStar

/-- `A₅^(X) = ⟨⟨r⟩⟩` for the printed group. -/
theorem lampStar_eq_normalClosure : lampStar = Subgroup.normalClosure {rStar} := by
  have hker : qA.ker = Subgroup.normalClosure {rA} := SpectralPaper.oneInvisibleRelationPackage.1
  ext x
  rw [mem_iff_of_map_eq wstarEquiv map_normalClosure_rStar x, ← lampStar_eq_ker,
    wstar_mem_ker_iff, hker]

theorem rStar_ne_one : rStar ≠ 1 := fun h =>
  AlternatingLampLiteral.rA_ne_one (by rw [← wstarEquiv_rStar, h, map_one])

/-- **`cor:notes-a5-relation`, printed form.**  For `W_{A₅} = A₅^(G_*/Γ_*) ⋊ G_*` and the
one-site lamp `r = (12)(34)` at `tΓ_*`:

1. `W_{A₅}` is the repository's `A₅`-lamp group `AlternatingLampLiteral.WA`, and `r ≠ 1`;
2. `Rad_MF(W_{A₅}) = A₅^(X)`;
3. `A₅^(X) = ⟨⟨r⟩⟩`;
4. `W_{A₅}/⟨⟨r⟩⟩ ≅ G_*`;
5. `W_{A₅}` is sofic and not MF;
6. `G_*` is residually finite and MF;
7. every homomorphism from `W_{A₅}` to the unitary group of a norm matrix corona maps `r`
   to `1`. -/
theorem notesA5RelationLiteral :
    Nonempty (WStar ≃* WA) ∧ rStar ≠ 1 ∧
      actualCoronaMFResidual WStar = lampStar ∧
      lampStar = Subgroup.normalClosure {rStar} ∧
      Nonempty (WStar ⧸ Subgroup.normalClosure {rStar} ≃* Gstar) ∧
      IsSofic WStar ∧ ¬ IsOperatorMF WStar ∧
      IsResiduallyFinite Gstar ∧ IsOperatorMF Gstar ∧
      (∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
        letI : ∀ n, Nonempty (X n) :=
          fun n ↦ Fintype.card_pos_iff.mp (hX n)
        ∀ rho : WStar →* unitary (NormMatrixCStarCorona (fun n ↦ X n)), rho rStar = 1) := by
  have hmem : rStar ∈ actualCoronaMFResidual WStar := by
    rw [wstar_radical, lampStar_eq_normalClosure]
    exact Subgroup.subset_normalClosure (Set.mem_singleton rStar)
  refine ⟨⟨wstarEquiv⟩, rStar_ne_one, wstar_radical, lampStar_eq_normalClosure, ⟨?_⟩,
    isSofic_of_injective wstarEquiv.toMonoidHom wstarEquiv.injective
      SpectralPaper.oneInvisibleRelationPackage.2.2.2.2.1,
    fun h => AlternatingLampLiteral.not_isOperatorMF_WA
      (CommensurabilityInvariance.isOperatorMF_of_mulEquiv wstarEquiv h),
    gstar_residuallyFinite, gstar_isOperatorMF,
    fun X hX => (mem_actualCoronaMFResidual_iff.mp hmem) X hX⟩
  exact (QuotientGroup.quotientMulEquivOfEq
      (lampStar_eq_normalClosure.symm.trans lampStar_eq_ker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (SemidirectProduct.rightHom : WStar →* Gstar)
      SemidirectProduct.rightHom_surjective)

#audit_axioms gstarCosetEquiv
#audit_axioms gstarCosetEquiv_smul
#audit_axioms gstarCosetEquiv_tSite
#audit_axioms wstarEquiv
#audit_axioms wstarEquiv_rStar
#audit_axioms wstar_radical
#audit_axioms lampStar_eq_normalClosure
#audit_axioms notesA5RelationLiteral

end GroupApproximation.Full.NN05
