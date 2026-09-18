import GroupApproximation.Sofic.MFTraceRecognition
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.NegativeCornerModel
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Manuscript.MFRecognition.RegularRealizationSentences
import GroupApproximation.Manuscript.NonMFNotes.Full.TWW.SolvableInduction

/-!
# Regular-character models on a subgroup: union closure, base cases, endpoint

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378: "It is amenable, so `C*_r(A)` is quasidiagonal [TWW] and
embeds in a norm matrix corona, and `A` is MF"), and the sharpness paragraph
of `sec:necessity` (the realized Clifford quotient "is amenable, hence MF by
[TWW]").

`SolvableInduction` reduces `Q ⊤` for a (locally finite)-by-solvable group to
three facts about a predicate `Q` on subgroups: closure under increasing
unions, closure under normalizing cyclic extensions, and the base case. This
file supplies a concrete predicate for which everything except the cyclic
extension step is proved here.

`IsModelled H` says that the regular character of `G` has matrix models of
norm at most `1` on every finite test set inside `H`, at every accuracy
(`MFTraceRecognition.RegularCharacterModel`). Restricted to `H`, the regular
character of `G` is the regular character of `H`, so this is the statement
that the canonical trace of `C*_r(H)` is an MF trace with contractive models.

* `isSequentialUnionClosed_isModelled`: union closure. It is elementary
  because a finite test set lies in one member of the chain.
* `isModelled_of_forall_exists_finite`: if every finite subset of `H` lies in
  a finite subgroup, then `IsModelled H`. The models are the exact left
  regular representations of those finite subgroups. Special cases are
  `isModelled_bot` and `isModelled_of_isLocallyFiniteGroup`.
* `isOperatorMF_of_isModelled_top`: `IsModelled ⊤` makes a countable group
  operator MF, through `MFTraceRecognition.isNormApproximable_of_isMFRegularCharacter`.

No hypothesis in this file stands in for a cited theorem. The remaining
analytic input for the manuscript step is closure of `IsModelled` under
normalizing cyclic extensions in an amenable ambient group
(Ozawa--Rørdam--Sato; Tikuisis--White--Winter).
-/

namespace GroupApproximation.Full.TWW

open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G]

/-! ## The predicate -/

/-- The regular character of `G` has contractive matrix models on every finite
test set contained in `H`, at every accuracy. -/
def IsModelled (H : Subgroup G) : Prop :=
  ∀ F : Finset G, (∀ g ∈ F, g ∈ H) → ∀ ε : ℝ, 0 < ε →
    Nonempty (MFTraceRecognition.RegularCharacterModel G F ε (fun _ : G => (1 : ℝ)))

/-- **Union closure.** A finite test set inside an increasing union lies in a
single member of the chain. -/
theorem isSequentialUnionClosed_isModelled :
    IsSequentialUnionClosed (IsModelled (G := G)) := by
  intro H hmono hH F hF ε hε
  have hex : ∀ g ∈ F, ∃ n, g ∈ H n := fun g hg =>
    (Subgroup.mem_iSup_of_directed hmono.directed_le).mp (hF g hg)
  choose! idx hidx using hex
  exact hH (F.sup idx) F
    (fun g hg => hmono (Finset.le_sup (f := idx) hg) (hidx g hg)) ε hε

/-- **Endpoint.** Models on the whole group give an MF regular character. -/
theorem isMFRegularCharacter_of_isModelled_top
    (h : IsModelled (⊤ : Subgroup G)) :
    MFTraceRecognition.IsMFRegularCharacter G :=
  ⟨fun _ : G => (1 : ℝ), fun F ε hε => h F (fun g _ => Subgroup.mem_top g) ε hε⟩

/-- **Endpoint.** A countable group whose regular character is modelled on the
whole group is operator MF (`thm:fixed-radical-membership`, last clause). -/
theorem isOperatorMF_of_isModelled_top [Countable G]
    (h : IsModelled (⊤ : Subgroup G)) : IsOperatorMF G :=
  (OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one (G := G)).mpr
    (MFTraceRecognition.isNormApproximable_of_isMFRegularCharacter (G := G)
      (isMFRegularCharacter_of_isModelled_top h))

/-! ## Exact models from finite subgroups -/

/-- The finite model carried by a finite subgroup. -/
noncomputable def subgroupModel (K : Subgroup G) [Finite K] : FiniteModel :=
  ⟨K, Fintype.ofFinite K, Classical.decEq K⟩

instance subgroupModelGroup (K : Subgroup G) [Finite K] : Group (subgroupModel K) :=
  inferInstanceAs (Group K)

open scoped Classical in
/-- The left regular representation of a finite subgroup `K`, extended by `0`
off `K`. -/
noncomputable def regularMat (K : Subgroup G) [Finite K] (g : G) :
    Matrix (subgroupModel K) (subgroupModel K) ℂ :=
  if hg : g ∈ K then
    (Manuscript.MFRecognition.Sentences.finiteGroupRegularHom (subgroupModel K)
      ((⟨g, hg⟩ : K) : subgroupModel K) : Matrix (subgroupModel K) (subgroupModel K) ℂ)
  else 0

theorem regularMat_of_mem (K : Subgroup G) [Finite K] {g : G} (hg : g ∈ K) :
    regularMat K g =
      (Manuscript.MFRecognition.Sentences.finiteGroupRegularHom (subgroupModel K)
        ((⟨g, hg⟩ : K) : subgroupModel K) :
          Matrix (subgroupModel K) (subgroupModel K) ℂ) := by
  rw [regularMat, dif_pos hg]

theorem regularMat_of_notMem (K : Subgroup G) [Finite K] {g : G} (hg : g ∉ K) :
    regularMat K g = 0 := by
  rw [regularMat, dif_neg hg]

theorem norm_regularMat_le_one (K : Subgroup G) [Finite K] (g : G) :
    ‖regularMat K g‖ ≤ 1 := by
  by_cases hg : g ∈ K
  · rw [regularMat_of_mem K hg]
    exact NegativeCornerModel.norm_le_one_of_mem_unitaryGroup
      (Manuscript.MFRecognition.Sentences.finiteGroupRegularHom (subgroupModel K)
        ((⟨g, hg⟩ : K) : subgroupModel K)).2
  · rw [regularMat_of_notMem K hg, norm_zero]
    exact zero_le_one

theorem regularMat_mul (K : Subgroup G) [Finite K] {g h : G} (hg : g ∈ K)
    (hh : h ∈ K) : regularMat K (g * h) = regularMat K g * regularMat K h := by
  rw [regularMat_of_mem K (K.mul_mem hg hh), regularMat_of_mem K hg,
    regularMat_of_mem K hh]
  have hq : ((⟨g * h, K.mul_mem hg hh⟩ : K) : subgroupModel K) =
      ((⟨g, hg⟩ : K) : subgroupModel K) * ((⟨h, hh⟩ : K) : subgroupModel K) := rfl
  rw [hq, map_mul, Submonoid.coe_mul]

theorem regularMat_inv (K : Subgroup G) [Finite K] {g : G} (hg : g ∈ K) :
    regularMat K g⁻¹ = (regularMat K g)ᴴ := by
  rw [regularMat_of_mem K (K.inv_mem hg), regularMat_of_mem K hg]
  have hq : ((⟨g⁻¹, K.inv_mem hg⟩ : K) : subgroupModel K) =
      ((⟨g, hg⟩ : K) : subgroupModel K)⁻¹ := rfl
  rw [hq, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]

theorem regularMat_one (K : Subgroup G) [Finite K] : regularMat K 1 = 1 := by
  rw [regularMat_of_mem K K.one_mem]
  have hq : ((⟨1, K.one_mem⟩ : K) : subgroupModel K) = 1 := rfl
  rw [hq, map_one, Submonoid.coe_one]

theorem card_subgroupModel_pos (K : Subgroup G) [Finite K] :
    0 < Fintype.card (subgroupModel K) :=
  Fintype.card_pos_iff.mpr ⟨((1 : K) : subgroupModel K)⟩

/-- **The exact regular model of a finite subgroup.** If the test set lies in a
finite subgroup `K`, the left regular representation of `K` is an exact unitary
representation whose normalized trace is the regular character. -/
noncomputable def regularModel (K : Subgroup G) [Finite K] (F : Finset G)
    (hFK : ∀ g ∈ F, g ∈ K) (ε : ℝ) (hε : 0 < ε) :
    MFTraceRecognition.RegularCharacterModel G F ε (fun _ : G => (1 : ℝ)) where
  carrier := subgroupModel K
  nonempty := card_subgroupModel_pos K
  map := regularMat K
  bounded := fun g _ => norm_regularMat_le_one K g
  multiplicative := fun g hg h hh => by
    rw [regularMat_mul K (hFK g hg) (hFK h hh), sub_self, norm_zero]
    exact hε.le
  star_compatible := fun g hg => by
    rw [regularMat_inv K (hFK g hg), sub_self, norm_zero]
    exact hε.le
  trace_correct_one := fun _ => by
    have hcard : (Fintype.card (subgroupModel K) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (card_subgroupModel_pos K).ne'
    rw [regularMat_one K, Matrix.trace_one, div_self hcard, sub_self, norm_zero]
    exact hε.le
  trace_correct_ne := fun g hg hne => by
    haveI : Nonempty (subgroupModel K) := ⟨((1 : K) : subgroupModel K)⟩
    have hne' : ((⟨g, hFK g hg⟩ : K) : subgroupModel K) ≠ 1 := fun h =>
      hne (congrArg Subtype.val (h : (⟨g, hFK g hg⟩ : K) = 1))
    have h0 : Matrix.trace (regularMat K g) / (Fintype.card (subgroupModel K) : ℂ) = 0 := by
      rw [regularMat_of_mem K (hFK g hg)]
      exact Manuscript.MFRecognition.Sentences.normTrace_finiteGroupRegularHom_of_ne_one
        (subgroupModel K) _ hne'
    rw [h0, norm_zero]
    exact hε.le

/-! ## Base cases -/

/-- **Locally finite base case.** If every finite subset of `H` lies in a finite
subgroup of `G`, the regular character is modelled on `H`. -/
theorem isModelled_of_forall_exists_finite {H : Subgroup G}
    (h : ∀ F : Finset G, (∀ g ∈ F, g ∈ H) →
      ∃ K : Subgroup G, Finite K ∧ ∀ g ∈ F, g ∈ K) :
    IsModelled H := by
  intro F hF ε hε
  obtain ⟨K, hKfin, hFK⟩ := h F hF
  exact ⟨regularModel K F hFK ε hε⟩

/-- The trivial subgroup is modelled, which is the base of `of_isSolvable`. -/
theorem isModelled_bot : IsModelled (⊥ : Subgroup G) :=
  isModelled_of_forall_exists_finite fun _ hF => ⟨⊥, inferInstance, hF⟩

/-- A locally finite subgroup is modelled, which is the base of
`of_isSolvable_quotient` for (locally finite)-by-solvable groups. -/
theorem isModelled_of_isLocallyFiniteGroup {L : Subgroup G}
    (h : IsLocallyFiniteGroup L) : IsModelled L := by
  classical
  refine isModelled_of_forall_exists_finite fun F hF => ?_
  obtain ⟨K', hK'fin, hK'⟩ := h (F.subtype fun g => g ∈ L)
  refine ⟨K'.map L.subtype,
    Finite.of_equiv K' (K'.equivMapOfInjective L.subtype L.subtype_injective).toEquiv,
    fun g hg => ?_⟩
  exact Subgroup.mem_map_of_mem L.subtype (hK' ⟨g, hF g hg⟩ (Finset.mem_subtype.mpr hg))

end GroupApproximation.Full.TWW
