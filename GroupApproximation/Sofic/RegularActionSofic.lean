import GroupApproximation.Sofic.SoficAction
import GroupApproximation.Sofic.AscendingHNNCosetActionSofic

/-!
# A universally action-sofic group is sofic

Sofic *actions* in the sense of Gao--Kunnawalkam Elayavalli--Patchell do not
require the approximating map to be almost free, which is exactly why a group
can act soficly without being known to be sofic.  On the **regular** action that
freedom disappears: the charts are injective on the tested window, and the
window can be chosen to contain `1` together with the inverses of the tested
group elements, which forces the model permutations of two distinct elements to
disagree on almost every good site.

`isSofic_of_isSoficAction_regular` turns that observation into the implication
`IsSoficAction G G → IsSofic G`, and `isSofic_of_universallyActionSofic` is the
corollary used by Theorems 34.6 and 34.7, where the dossier reads "UAS implies
that `Γ` is sofic" as a step.

Two mismatches have to be crossed.

*Universes.*  `SoficModel` bundles its model set as a `FiniteModel`, whose
carrier lives in `Type 0`, while `SoficActionModel` keeps its model set in the
universe of the acted-on type -- here the universe of `G`.  A finite type is
transportable regardless: `Fintype.equivFin` moves the model set into a
`FiniteModel`, and `Equiv.permCongr` carries the approximating permutations
along.  The transport section below records that this changes neither
multiplicativity nor Hamming distance.  The equivalence is stated with a
`FiniteModel` on the right, not `Fin n`: `(finModel n).carrier` is only
*definitionally* `Fin n`, and a `rw` needs the two sides to agree
syntactically.

*Tolerances.*  Separation costs three copies of the action tolerance -- the good
set and its two preimages -- so the models are taken at `min ε (ε/3)`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation

universe u

/-! ## Transporting a finite permutation model into `Type 0` -/

section Transport

/-- A finite type in `Type 0`, bundled as a `FiniteModel`. -/
def finModel (n : ℕ) : FiniteModel :=
  ⟨Fin n, inferInstance, inferInstance⟩

@[simp] theorem card_finModel (n : ℕ) : Fintype.card (finModel n) = n :=
  Fintype.card_fin n

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
/-- Transport along a bijection is multiplicative on permutations. -/
theorem permCongr_mul {Y : Type*} (e : A ≃ Y) (p q : Equiv.Perm A) :
    e.permCongr (p * q) = e.permCongr p * e.permCongr q := by
  ext i
  simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-- The two normalized distances, unfolded to the same shape. -/
@[simp] theorem permDist_eq (p q : Equiv.Perm A) :
    permDist p q = ((hammingDisagreement p q).card : ℝ) / Fintype.card A := rfl

omit [Fintype A] [DecidableEq A] in
@[simp] theorem hammingDistance_eq (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q
      = ((hammingDisagreement p q).card : ℝ) / Fintype.card Y := rfl

/-- Transport moves the disagreement set by the bijection. -/
theorem hammingDisagreement_permCongr {Y : FiniteModel} (e : A ≃ Y)
    (p q : Equiv.Perm A) :
    hammingDisagreement (e.permCongr p) (e.permCongr q)
      = (hammingDisagreement p q).image e := by
  ext i
  simp only [mem_hammingDisagreement, Finset.mem_image, ne_eq,
    Equiv.permCongr_apply]
  constructor
  · intro h
    refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
    intro hcon
    exact h (congrArg e hcon)
  · rintro ⟨a, ha, rfl⟩
    simp only [Equiv.symm_apply_apply]
    intro hcon
    exact ha (e.injective hcon)

/-- Hence transport preserves the normalized Hamming distance. -/
theorem hammingDistance_permCongr {Y : FiniteModel} (e : A ≃ Y)
    (p q : Equiv.Perm A) :
    hammingDistance Y (e.permCongr p) (e.permCongr q) = permDist p q := by
  have hcard : Fintype.card A = Fintype.card Y := Fintype.card_congr e
  rw [hammingDistance_eq, permDist_eq, hammingDisagreement_permCongr,
    Finset.card_image_of_injective _ e.injective, hcard]

end Transport

/-! ## Almost freeness on the regular action -/

section Regular

variable {G : Type u} [Group G]

/-- **Soficity of a group out of soficity of its regular action.**  On the
window `{1} ∪ F⁻¹` the charts separate `g⁻¹` from `h⁻¹`, so no good site whose
two translates are again good can be fixed by both model permutations; the good
set and its two preimages each miss at most `ε'` of the model, so the two
permutations disagree on at least `1 - 3ε'` of it. -/
theorem isSofic_of_isSoficAction_regular (h : IsSoficAction G G) : IsSofic G := by
  classical
  intro F ε hε
  set ε' : ℝ := min ε (ε / 3) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (by linarith)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hthree : 3 * ε' ≤ ε := by
    have : ε' ≤ ε / 3 := min_le_right _ _
    linarith
  set E : Finset G := insert (1 : G) (F.image fun g => g⁻¹) with hEdef
  have hone : (1 : G) ∈ E := Finset.mem_insert_self _ _
  have hinv : ∀ g ∈ F, g⁻¹ ∈ E := fun g hg =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hg)
  obtain ⟨M⟩ := h F E ε' hε'pos
  have e : M.Site ≃ (finModel (Fintype.card M.Site)).carrier :=
    Fintype.equivFin M.Site
  -- the two translates of a good site, as finsets of the same size
  have hpre : ∀ g : G, ∀ s : M.Site,
      s ∈ M.good.image (fun t => (M.act g)⁻¹ t) ↔ M.act g s ∈ M.good := by
    intro g s
    constructor
    · rintro hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      simpa using ht
    · intro hs
      exact Finset.mem_image.mpr ⟨M.act g s, hs, by simp⟩
  have hprecard : ∀ g : G,
      (M.good.image (fun t => (M.act g)⁻¹ t)).card = M.good.card := fun g =>
    Finset.card_image_of_injective _ (Equiv.injective _)
  refine ⟨{
    carrier := finModel (Fintype.card M.Site)
    nonempty := by rw [card_finModel]; exact M.siteNonempty
    map := fun g => e.permCongr (M.act g)
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h' hh'
    simp only [← permCongr_mul, hammingDistance_permCongr]
    exact le_trans (M.act_mul g hg h' hh') hε'le
  · intro g hg h' hh' hne
    simp only [hammingDistance_permCongr]
    -- every good site with both translates good is a disagreement site
    set A : Finset M.Site := M.good.image (fun t => (M.act g)⁻¹ t) with hAdef
    set B : Finset M.Site := M.good.image (fun t => (M.act h')⁻¹ t) with hBdef
    have hsub : M.good ∩ A ∩ B ⊆ hammingDisagreement (M.act g) (M.act h') := by
      intro s hs
      obtain ⟨hsA, hsB⟩ := Finset.mem_inter.mp hs
      obtain ⟨hgood, hsA⟩ := Finset.mem_inter.mp hsA
      rw [mem_hammingDisagreement]
      intro hcon
      have hgg : M.act g s ∈ M.good := (hpre g s).mp hsA
      have hhg : M.act h' s ∈ M.good := (hpre h' s).mp hsB
      have hxg : M.chart (M.act g s) 1 = M.chart s g⁻¹ := by
        have := M.chart_equivariant g hg s hgood hgg 1 hone
          (by simpa using hinv g hg)
        simpa using this
      have hxh : M.chart (M.act h' s) 1 = M.chart s h'⁻¹ := by
        have := M.chart_equivariant h' hh' s hgood hhg 1 hone
          (by simpa using hinv h' hh')
        simpa using this
      have hcharts : M.chart s g⁻¹ = M.chart s h'⁻¹ := by
        rw [← hxg, ← hxh, hcon]
      exact hne (inv_injective
        (M.chart_inj s hgood g⁻¹ (hinv g hg) h'⁻¹ (hinv h' hh') hcharts))
    -- three sets, each missing at most `ε'` of the model
    have hunion : ∀ s t : Finset M.Site,
        (s.card : ℝ) + t.card
          ≤ ((s ∩ t).card : ℝ) + (Fintype.card M.Site : ℝ) := by
      intro s t
      have h1 : (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
        Finset.card_union_add_card_inter s t
      have h2 : (s ∪ t).card ≤ Fintype.card M.Site := Finset.card_le_univ _
      have h3 : (s.card : ℕ) + t.card ≤ (s ∩ t).card + Fintype.card M.Site := by
        omega
      exact_mod_cast h3
    have hgoodcard : (1 - ε') * (Fintype.card M.Site : ℝ) ≤ (M.good.card : ℝ) :=
      M.good_card
    have hA : (A.card : ℝ) = (M.good.card : ℝ) := by rw [hAdef, hprecard]
    have hB : (B.card : ℝ) = (M.good.card : ℝ) := by rw [hBdef, hprecard]
    have hstep1 := hunion M.good A
    have hstep2 := hunion (M.good ∩ A) B
    have hbig : (1 - 3 * ε') * (Fintype.card M.Site : ℝ)
        ≤ ((M.good ∩ A ∩ B).card : ℝ) := by
      rw [hA] at hstep1
      rw [hB] at hstep2
      nlinarith [hgoodcard, hstep1, hstep2]
    have hcardsub : ((M.good ∩ A ∩ B).card : ℝ)
        ≤ ((hammingDisagreement (M.act g) (M.act h')).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hNpos : (0 : ℝ) < (Fintype.card M.Site : ℝ) := by
      exact_mod_cast M.siteNonempty
    rw [permDist_eq, le_div_iff₀ hNpos]
    calc (1 - ε) * (Fintype.card M.Site : ℝ)
        ≤ (1 - 3 * ε') * (Fintype.card M.Site : ℝ) := by nlinarith
      _ ≤ ((M.good ∩ A ∩ B).card : ℝ) := hbig
      _ ≤ _ := hcardsub

/-- **The corollary Theorems 34.6 and 34.7 use.**  A universally action-sofic
group is sofic: apply the hypothesis to its own regular action. -/
theorem isSofic_of_universallyActionSofic
    (h : MarkedCompression.UniversallyActionSofic G) : IsSofic G :=
  isSofic_of_isSoficAction_regular (h G)

end Regular

end GroupApproximation
