import GroupApproximation.GroupTheory.FiniteRelatorQuotient
import GroupApproximation.Manuscript.MFRecognition.LocalityAndCertificates
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Countable.Defs

/-!
# Sentence-level formalization: every f.g. non-MF group is a quotient of a f.p. one

This file formalizes the sentence (tex line 167, key `396318a13c21`) that
follows Korchagin's direct-limit closure theorem in the discussion of
`thm:recognition`:

> Korchagin proved that the MF property is closed under direct
> limits~\cite[Proposition~13]{Korchagin}.  Consequently, every finitely
> generated non-MF group is a quotient of a finitely presented one.

The direct-limit closure itself (Korchagin's Proposition 13, cited but not
proved in the manuscript) is proved below in its narrowest usable form: an
increasing chain of normal subgroups of a *fixed* countable group, with
every finite-stage quotient MF, gives an MF quotient by their union.  The
argument reduces the finite-set operator-norm approximation problem for the
union quotient to one at a single finite stage, using that every relator of
the union's presentation is eventually a relator of some finite stage.
Building the finitely presented approximating stage `F/N_k` from an
enumeration of `N`, and extracting the non-MF stage by contraposition, is
proved separately.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Sentences

noncomputable section

/-- **Korchagin, Proposition 13** — "Korchagin proved that the MF property
is closed under direct limits" — proved here in its narrowest usable form:
for an increasing chain of normal subgroups of a fixed countable group, if
every finite-stage quotient is MF, so is the quotient by their union. -/
theorem isOperatorMF_of_directLimit_quotients
    {F : Type} [Group F] [Countable F] (Nk : ℕ → Subgroup F)
    [∀ k, (Nk k).Normal] (hmono : Monotone Nk)
    [(⨆ k, Nk k).Normal]
    (hMF : ∀ k, IsOperatorMF (F ⧸ Nk k)) :
    IsOperatorMF (F ⧸ ⨆ k, Nk k) := by
  classical
  let Ntop : Subgroup F := ⨆ k, Nk k
  letI : Ntop.Normal := by
    dsimp [Ntop]
    infer_instance
  letI : Countable (F ⧸ Ntop) :=
    Function.Surjective.countable (QuotientGroup.mk'_surjective Ntop)
  change IsOperatorMF (F ⧸ Ntop)
  rw [Certificates.isOperatorMF_iff_isLocallyModelled]
  intro K hK_one ε hε
  let Q := F ⧸ Ntop
  let rawRep : Q → F := fun q ↦
    Classical.choose (QuotientGroup.mk'_surjective Ntop q)
  have hrawRep (q : Q) : QuotientGroup.mk' Ntop (rawRep q) = q :=
    Classical.choose_spec (QuotientGroup.mk'_surjective Ntop q)
  let rep : Q → F := fun q ↦ rawRep q * (rawRep 1)⁻¹
  have hrep (q : Q) : QuotientGroup.mk' Ntop (rep q) = q := by
    change QuotientGroup.mk' Ntop (rawRep q * (rawRep 1)⁻¹) = q
    rw [map_mul, map_inv, hrawRep, hrawRep]
    simp
  have hrep_one : rep (1 : Q) = 1 := by
    change rawRep 1 * (rawRep 1)⁻¹ = 1
    exact mul_inv_cancel _
  let rels : Finset F := (K ×ˢ K).image fun p ↦
    (rep (p.1 * p.2))⁻¹ * (rep p.1 * rep p.2)
  have hrels : ∀ r ∈ rels, r ∈ Ntop := by
    intro r hr
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hr
    rw [← QuotientGroup.eq_one_iff]
    rw [← QuotientGroup.mk'_apply, map_mul, map_mul, map_inv,
      hrep, hrep, hrep]
    simp
  have hdirected : Directed (· ≤ ·) Nk := by
    intro i j
    exact ⟨max i j, hmono (Nat.le_max_left i j), hmono (Nat.le_max_right i j)⟩
  have hrel_eventually : ∀ r ∈ rels, ∀ᶠ k in Filter.atTop, r ∈ Nk k := by
    intro r hr
    obtain ⟨i, hi⟩ :=
      (Subgroup.mem_iSup_of_directed hdirected).mp (hrels r hr)
    filter_upwards [Filter.eventually_ge_atTop i] with k hik
    exact hmono hik hi
  have hall : ∀ᶠ k in Filter.atTop, ∀ r ∈ rels, r ∈ Nk k := by
    rw [Filter.eventually_all_finset]
    exact hrel_eventually
  obtain ⟨m, hm⟩ := hall.exists
  let qm : F →* F ⧸ Nk m := QuotientGroup.mk' (Nk m)
  letI : Countable (F ⧸ Nk m) :=
    Function.Surjective.countable (QuotientGroup.mk'_surjective (Nk m))
  let Km : Finset (F ⧸ Nk m) := insert 1 (K.image fun q ↦ qm (rep q))
  have hlocal : Certificates.IsLocallyModelled (F ⧸ Nk m) :=
    Certificates.isOperatorMF_iff_isLocallyModelled.mp (hMF m)
  obtain ⟨M⟩ := hlocal Km (Finset.mem_insert_self 1 _) ε hε
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    V := fun q ↦ M.V (qm (rep q))
    isUnitary := fun q ↦ M.isUnitary (qm (rep q))
    V_one := ?_
    multiplicative := ?_
    separated := ?_ }⟩
  · rw [hrep_one, map_one, M.V_one]
  · intro g hg h hh hgh
    have hgm : qm (rep g) ∈ Km :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    have hhm : qm (rep h) ∈ Km :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨h, hh, rfl⟩)
    have hghm : qm (rep (g * h)) ∈ Km :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g * h, hgh, rfl⟩)
    have hrelmem : (rep (g * h))⁻¹ * (rep g * rep h) ∈ Nk m := by
      apply hm
      exact Finset.mem_image.mpr
        ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩
    have hqmul : qm (rep (g * h)) = qm (rep g) * qm (rep h) := by
      rw [← inv_mul_eq_one, ← map_inv, ← map_mul, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hrelmem
    rw [hqmul]
    exact M.multiplicative (qm (rep g)) hgm (qm (rep h)) hhm (by
      rw [← hqmul]
      exact hghm)
  · intro g hg hg_one
    have hgm : qm (rep g) ∈ Km :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    have hqne : qm (rep g) ≠ 1 := by
      intro heq
      have hmem : rep g ∈ Ntop :=
        (le_iSup Nk m) ((QuotientGroup.eq_one_iff _).mp heq)
      exact hg_one ((hrep g).symm.trans ((QuotientGroup.eq_one_iff _).mpr hmem))
    exact M.separated (qm (rep g)) hgm hqne

/-- **Sentence `396318a13c21`.**  "Consequently, every finitely generated
non-MF group is a quotient of a finitely presented one."  Formalized for a
finitely generated non-MF group presented as `F/N` with `F` a finite-rank
free group: some stage `F/N_k` of the increasing exhaustion of `N` by the
normal closures of an enumeration of its elements is finitely presented,
not MF, and surjects onto `F/N`. -/
theorem sentence_396318a13c21
    {r : ℕ} (N : Subgroup (FreeGroup (Fin r))) [N.Normal]
    (hNonMF : ¬ IsOperatorMF (FreeGroup (Fin r) ⧸ N)) :
    ∃ Nk : Subgroup (FreeGroup (Fin r)), ∃ hNk : Nk.Normal,
      letI : Nk.Normal := hNk
      Group.IsFinitelyPresented (FreeGroup (Fin r) ⧸ Nk) ∧
      ¬ IsOperatorMF (FreeGroup (Fin r) ⧸ Nk) ∧
      Nk ≤ N := by
  classical
  haveI : Nonempty N := ⟨⟨1, N.one_mem⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat N
  let gens : ℕ → Finset (FreeGroup (Fin r)) := fun k =>
    (Finset.range k).image (fun i => (e i : FreeGroup (Fin r)))
  let Nk : ℕ → Subgroup (FreeGroup (Fin r)) := fun k =>
    Subgroup.normalClosure (gens k : Set (FreeGroup (Fin r)))
  have hgens_subset : ∀ k, gens k ⊆ gens (k + 1) :=
    fun k => Finset.image_subset_image (Finset.range_subset_range.mpr (Nat.le_succ k))
  have hNk_mono : Monotone Nk := by
    apply monotone_nat_of_le_succ
    intro k
    exact Subgroup.normalClosure_mono (Finset.coe_subset.mpr (hgens_subset k))
  have hNk_le_N : ∀ k, Nk k ≤ N := by
    intro k
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (e i).2
  have hUnion : ⨆ k, Nk k = N := by
    apply le_antisymm
    · exact iSup_le hNk_le_N
    · intro n hn
      obtain ⟨i, hi⟩ := he ⟨n, hn⟩
      have hival : (e i : FreeGroup (Fin r)) = n := congrArg Subtype.val hi
      have hmemFinset : (e i : FreeGroup (Fin r)) ∈ gens (i + 1) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_self i), rfl⟩
      have hmem : n ∈ Nk (i + 1) := by
        rw [← hival]
        exact Subgroup.subset_normalClosure (Finset.mem_coe.mpr hmemFinset)
      exact (le_iSup Nk (i + 1)) hmem
  have hNk_finite : ∀ k, ((gens k : Set (FreeGroup (Fin r)))).Finite :=
    fun k => (gens k).finite_toSet
  have hex : ∃ k, ¬ IsOperatorMF (FreeGroup (Fin r) ⧸ Nk k) := by
    by_contra hall
    push Not at hall
    haveI : ∀ k, (Nk k).Normal := fun _ => Subgroup.normalClosure_normal
    haveI : (⨆ k, Nk k).Normal := by rw [hUnion]; infer_instance
    have hdirect := isOperatorMF_of_directLimit_quotients Nk hNk_mono hall
    let e : (FreeGroup (Fin r) ⧸ ⨆ k, Nk k) ≃*
        (FreeGroup (Fin r) ⧸ N) :=
      QuotientGroup.quotientMulEquivOfEq hUnion
    apply hNonMF
    exact hdirect.comap e.symm.toMonoidHom e.symm.injective
  obtain ⟨k, hk⟩ := hex
  refine ⟨Nk k, Subgroup.normalClosure_normal, ?_⟩
  exact ⟨FiniteRelatorQuotient.quotient_isFinitelyPresented (hNk_finite k),
    hk, hNk_le_N k⟩

end

end Sentences
end MFRecognition
end Manuscript
end GroupApproximation
