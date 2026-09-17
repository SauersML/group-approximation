import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.IndexEight
import GroupApproximation.Algebra.LampCountable
import GroupApproximation.Sofic.WreathWitnessGeneric
import GroupApproximation.Sofic.TorsionSpectralCollapse
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Manuscript.NonMFSentences.IntroWitnessSignSentence
import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedSubgroup
import GroupApproximation.Meta.AxiomGuard

/-!
# The abelian boundary: torsion lamps are not MF

Manuscript `non_mf_group_notes.tex`, `thm:notes-abelian-boundary` (tex lines 2076--2160),
first paragraph of the proof (tex lines 2088--2096):

> If `A` has nontrivial torsion, a finite-order one-site lamp has zero-dimensional spectrum in
> every corona representation.  Theorem `thm:notes-spectral-motion` identifies its image with
> the image of each `Γ_*`-translate in the same fibre of `X → X_1`.  For a nonidentity torsion
> element `a ∈ A`, choose `γ ∈ Γ_*` such that `γ t Γ_* ≠ t Γ_*`; such an element exists because
> `[Γ_* : t Γ_* t⁻¹] = 8`.  Every corona homomorphism annihilates `a_{γ t Γ_*} a_{t Γ_*}⁻¹`,
> which is nonidentity in `A^{(X)}`.

Here `A^{(X)} ⋊ G_*` is the repository's permutational wreath product
`Wreath (Multiplicative A) Gstar GstarCosets` over the literal coset space `X = G_*/Γ_*`
(`AbelianLamp A`).  The spectral-motion collapse is the unconditional torsion collapse
`TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness`, applied with
`L = Γ_*` (property (T), `gamma_hasKazhdanPropertyT`), `s = t` and `k` the one-site lamp at
`t Γ_*`; the translate `γ` is supplied by `NN05.exists_translate_ne`.

Main declarations:

* `AbelianLamp A` — `A^{(X)} ⋊ G_*`;
* `stableLamp_isTorsionCompressionWitness` — a finite-order lamp at `t Γ_*` is a torsion
  compression witness for `(Γ_*, t)`;
* `commutator_stableLamp_ne_one` — the defect `a_{γ t Γ_*} a_{t Γ_*}⁻¹` is nonidentity;
* `not_isOperatorMF_of_isOfFinAddOrder`, `not_isOperatorMF_of_not_isAddTorsionFree`,
  `isAddTorsionFree_of_isOperatorMF` — the torsion direction of the theorem.
-/

namespace GroupApproximation.Full.NN06

open SemidirectProduct GroupApproximation.Full.NN05
open scoped commutatorElement

noncomputable section

/-- **`A^{(X)} ⋊ G_*`** (tex line 2080): finitely supported `A`-configurations over
`X = G_*/Γ_*`, translated by `G_*`. -/
abbrev AbelianLamp (A : Type) [AddCommGroup A] : Type :=
  Wreath (Multiplicative A) Gstar GstarCosets

/-- `G_*` is countable: it is an HNN extension of the countable group `Γ_*`. -/
instance gstar_countable : Countable Gstar :=
  haveI : Countable GammaStar :=
    Manuscript.NonMFSentences.IntroWitnessSignSentence.gamma_countable
  Manuscript.MFRecognition.HNNPermanence.hnnExtension_countable GammaStar ⊤ alphaStar.range
    doublingIso

/-- `X = G_*/Γ_*` is countable. -/
instance gstarCosets_countable : Countable GstarCosets :=
  (QuotientGroup.mk_surjective (s := ofGamma.range)).countable

instance multiplicative_countable (A : Type) [Countable A] : Countable (Multiplicative A) :=
  inferInstanceAs (Countable A)

/-- `A^{(X)} ⋊ G_*` is countable for countable `A`. -/
instance abelianLamp_countable (A : Type) [AddCommGroup A] [Countable A] :
    Countable (AbelianLamp A) :=
  wreath_countable

/-- Classical decidable equality on the site set, used only to place one-site lamps. -/
def gstarCosetsDecEq : DecidableEq GstarCosets := Classical.decEq _

attribute [local instance] gstarCosetsDecEq

/-- The site `t Γ_* ∈ X`. -/
abbrev stableSite : GstarCosets := (QuotientGroup.mk stableLetter : Gstar ⧸ ofGamma.range)

/-- The compressed copy `t Γ_* t⁻¹ = α(Γ_*)` fixes the site `t Γ_*`. -/
theorem compressed_smul_stableSite (g : GammaStar) :
    ofGamma (alphaStar g) • stableSite = stableSite := by
  show (QuotientGroup.mk (ofGamma (alphaStar g) * stableLetter) : GstarCosets) =
    QuotientGroup.mk stableLetter
  rw [← stableLetter_mul_ofGamma]
  exact QuotientGroup.mk_mul_of_mem stableLetter (MonoidHom.mem_range.mpr ⟨g, rfl⟩)

variable (A : Type) [AddCommGroup A]

/-- The copy of `Γ_*` inside `A^{(X)} ⋊ G_*`. -/
abbrev baseSub : Subgroup (AbelianLamp A) :=
  ((inr : Gstar →* AbelianLamp A).comp ofGamma).range

/-- The copy of `Γ_*` has property (T). -/
theorem baseSub_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} ↥(baseSub A) := by
  have hf : Function.Injective ((inr : Gstar →* AbelianLamp A).comp ofGamma) :=
    inr_injective.comp ofGamma_injective
  exact HasKazhdanPropertyT.of_mulEquiv (MonoidHom.ofInjective hf).symm
    Manuscript.NonMFSentences.IntroWitnessSignSentence.gamma_hasKazhdanPropertyT

/-- The stable letter compresses the copy of `Γ_*`: `t γ t⁻¹ = α(γ)`. -/
theorem stable_compress :
    ∀ γ ∈ baseSub A, (inr stableLetter : AbelianLamp A) * γ * (inr stableLetter)⁻¹ ∈
      baseSub A := by
  intro γ hγ
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
  refine MonoidHom.mem_range.mpr ⟨alphaStar g, ?_⟩
  show (inr (ofGamma (alphaStar g)) : AbelianLamp A) =
    inr stableLetter * inr (ofGamma g) * (inr stableLetter)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, stableLetter_conj]

/-- The one-site lamp `a_{t Γ_*}` with value `a` at the site `t Γ_*`. -/
def stableLamp (a : A) : AbelianLamp A :=
  WreathWitness.siteLamp (G := Gstar) stableSite (Multiplicative.ofAdd a)

variable {A}

/-- **A finite-order one-site lamp is a torsion compression witness** for the copy of `Γ_*`
and the stable letter (tex lines 2088--2090): it has finite order, the compressed copy fixes
its site, and its `Γ_*`-conjugates are lamps, hence commute. -/
theorem stableLamp_isTorsionCompressionWitness {a : A} {m : ℕ} (hm : 0 < m)
    (hma : m • a = 0) :
    TorsionCompressionCollapse.IsTorsionCompressionWitness (baseSub A)
      (inr stableLetter) (stableLamp A a) := by
  refine ⟨⟨m, hm, ?_⟩, ?_, ?_⟩
  · have hk : Multiplicative.ofAdd a ^ m = 1 := by
      rw [← ofAdd_nsmul, hma, ofAdd_zero]
    exact WreathWitness.siteLamp_pow (G := Gstar) stableSite (Multiplicative.ofAdd a) m hk
  · intro γ hγ
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
    show Commute ((inr stableLetter : AbelianLamp A) * inr (ofGamma g) *
      (inr stableLetter)⁻¹)
      (WreathWitness.siteLamp (G := Gstar) stableSite (Multiplicative.ofAdd a))
    rw [← map_inv, ← map_mul, ← map_mul, stableLetter_conj]
    exact WreathWitness.commute_inr_siteLamp (ofGamma (alphaStar g)) stableSite
      (Multiplicative.ofAdd a) (compressed_smul_stableSite g)
  · intro γ₁ hγ₁ γ₂ hγ₂
    obtain ⟨g₁, rfl⟩ := MonoidHom.mem_range.mp hγ₁
    obtain ⟨g₂, rfl⟩ := MonoidHom.mem_range.mp hγ₂
    exact WreathWitness.commute_conj_siteLamp (ofGamma g₁) (ofGamma g₂) stableSite
      (Multiplicative.ofAdd a)

/-- **The defect is nonidentity** (tex lines 2094--2096): if `γ t Γ_* ≠ t Γ_*` and `a ≠ 0`,
then `⁅γ, a_{t Γ_*}⁆ = a_{γ t Γ_*} a_{t Γ_*}⁻¹ ≠ 1`. -/
theorem commutator_stableLamp_ne_one {a : A} (ha : a ≠ 0) {γ₀ : GammaStar}
    (hγ₀ : ofGamma γ₀ • stableSite ≠ stableSite) :
    ⁅(inr (ofGamma γ₀) : AbelianLamp A), stableLamp A a⁆ ≠ 1 := by
  intro hcon
  rw [commutatorElement_def] at hcon
  have hconj := mul_inv_eq_one.mp hcon
  rw [stableLamp, WreathWitness.siteLamp,
    conj_inl_single (Multiplicative A) Gstar GstarCosets] at hconj
  have hlamp := inl_injective hconj
  have hval : (Lamp.single (ofGamma γ₀ • stableSite) (Multiplicative.ofAdd a)).toFun
      (ofGamma γ₀ • stableSite) =
      (Lamp.single stableSite (Multiplicative.ofAdd a)).toFun (ofGamma γ₀ • stableSite) := by
    rw [hlamp]
  rw [Lamp.single_apply_self, Lamp.single_apply_of_ne hγ₀] at hval
  exact ha (ofAdd_eq_one.mp hval)

variable [Countable A]

/-- **`thm:notes-abelian-boundary`, torsion direction, elementwise.**  A nonzero finite-order
`a ∈ A` makes `A^{(X)} ⋊ G_*` non-MF. -/
theorem not_isOperatorMF_of_isOfFinAddOrder {a : A} (ha : a ≠ 0)
    (hfin : IsOfFinAddOrder a) : ¬ IsOperatorMF (AbelianLamp A) := by
  obtain ⟨m, hm, hma⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hfin
  obtain ⟨γ₀, hγ₀⟩ := exists_translate_ne
  have hmem : ⁅(inr (ofGamma γ₀) : AbelianLamp A), stableLamp A a⁆ ∈
      actualCoronaMFResidual (AbelianLamp A) :=
    TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness
      (baseSub_hasKazhdanPropertyT A) (stable_compress A)
      (stableLamp_isTorsionCompressionWitness hm hma)
      (MonoidHom.mem_range.mpr ⟨γ₀, rfl⟩)
  intro hMF
  have hbot : actualCoronaMFResidual (AbelianLamp A) = ⊥ :=
    (isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot (G := AbelianLamp A)).mp
      ((isCDEOperatorMF_iff_isOperatorMF (AbelianLamp A)).mpr hMF)
  rw [hbot] at hmem
  exact commutator_stableLamp_ne_one ha hγ₀ (Subgroup.mem_bot.mp hmem)

/-- **`thm:notes-abelian-boundary`, torsion direction.**  If `A` is not torsion-free, then
`A^{(X)} ⋊ G_*` is not MF. -/
theorem not_isOperatorMF_of_not_isAddTorsionFree (hA : ¬ IsAddTorsionFree A) :
    ¬ IsOperatorMF (AbelianLamp A) := by
  obtain ⟨a, ha, hfin⟩ := not_isAddTorsionFree_iff_isOfFinAddOrder.mp hA
  exact not_isOperatorMF_of_isOfFinAddOrder ha hfin

/-- **`thm:notes-abelian-boundary`, the implication "MF ⇒ torsion-free".** -/
theorem isAddTorsionFree_of_isOperatorMF (hMF : IsOperatorMF (AbelianLamp A)) :
    IsAddTorsionFree A :=
  Classical.byContradiction fun hA => not_isOperatorMF_of_not_isAddTorsionFree hA hMF

end

#audit_axioms compressed_smul_stableSite
#audit_axioms baseSub_hasKazhdanPropertyT
#audit_axioms stable_compress
#audit_axioms stableLamp_isTorsionCompressionWitness
#audit_axioms commutator_stableLamp_ne_one
#audit_axioms not_isOperatorMF_of_isOfFinAddOrder
#audit_axioms not_isOperatorMF_of_not_isAddTorsionFree
#audit_axioms isAddTorsionFree_of_isOperatorMF

end GroupApproximation.Full.NN06
