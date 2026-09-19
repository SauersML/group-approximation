import GroupApproximation.Manuscript.MFRecognition.CentralRopeCore

/-!
# `mf_recognition_complexity.tex`, `lem:central-rope`(2): the Britton step

This file proves the remaining step of `lem:central-rope`(2), namely that the natural map
`F *_{N_e} F → Γ_e` is injective:

> "A reduced word of the amalgamated product alternates between elements of
> the two copies of `F` lying outside `N_e`; its image is a word
> `i(f₀) v i(f₁) v⁻¹ i(f₂) ⋯` in which every letter between consecutive
> occurrences of `v^{±1}` is some `i(f_k)` with `f_k ∉ N_e`, so
> `i(f_k) ∉ L_e` by (1).  Such a word contains no pinch `v^{±1} ℓ v^{∓1}`
> with `ℓ ∈ L_e`, so it is nontrivial in `Γ_e` by Britton's lemma."

## The two halves, and where each lives

* *"a reduced word of the amalgamated product alternates ... lying outside
  `N_e`"* is Mathlib's normal form for `Monoid.PushoutI`: every element of
  the amalgam is `base(h) · of(i₁,g₁) · of(i₂,g₂) ⋯` with consecutive indices
  distinct and every `g_k` a nontrivial coset representative, hence
  `g_k ∉ N_e`.  It is consumed here through the recursor
  `Monoid.PushoutI.NormalWord.consRecOn`, whose three cases are exactly
  "empty", "prepend a letter", "prepend an element of the base".
* *"so it is nontrivial in `Γ_e` by Britton's lemma"* is the repository's
  `Higman.Pinch.eq_nil_of_clean`: a **clean** block word --- one with no
  conjugated entry in `L_e`, and no base entry in `L_e` except the last ---
  lies in the base `K_e` only if it has no blocks at all.  That lemma is
  proved from Mathlib's `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`.

## The bridge between them

`BrittonData` is the invariant carried through the recursion: it produces,
for each normal word `w`, a leading base element `z₀` and a *clean* block
list `l` with `θ(w.prod) = word z₀ l`, where `θ` is the printed map
`F *_{N_e} F → Γ_e`.  The three case-clauses of `BrittonData` --- one for
each possible first index of `w` (`none`, `some false`, `some true`) --- are
exactly the bookkeeping that keeps `Clean` provable when a new letter is
prepended: a `false` letter merges into `z₀`, and a `true` letter opens a new
block whose base entry is the old `z₀`, which must therefore lie outside
`L_e`.  The printed input to that bookkeeping is `lem:central-rope`(1), in
the form `iEmb_mem_Le_iff`: `i(f) ∈ L_e` exactly when `f ∈ N_e`.

The conclusion is `amalgamToGamma_injective`, the injectivity assertion used
to identify the amalgam with the printed subgroup `S_e`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Rope
namespace RopeInput

variable (inp : RopeInput)

noncomputable section

/-! ## 1.  `lem:central-rope`(1), read pointwise -/

/-- **`i(f) ∈ L_e` exactly when `f ∈ N_e`.**  The pointwise form of the
printed `i(F) ∩ L_e = i(N_e)`. -/
theorem iEmb_mem_Le_iff (f : Fxyt) : iEmb inp f ∈ Le inp ↔ f ∈ inp.N := by
  have h := SetLike.ext_iff.mp (comap_Le_eq_N inp) f
  rw [Subgroup.mem_comap] at h
  exact h

/-- "so `i(f_k) ∉ L_e` by (1)". -/
theorem iEmb_notMem_Le {f : Fxyt} (hf : f ∉ inp.N) : iEmb inp f ∉ Le inp :=
  fun hmem => hf ((iEmb_mem_Le_iff inp f).mp hmem)

theorem iEmb_mem_Le {f : Fxyt} (hf : f ∈ inp.N) : iEmb inp f ∈ Le inp :=
  (iEmb_mem_Le_iff inp f).mpr hf

/-! ## 2.  The three letter values of the printed map `θ` -/

/-- The first copy of `F` goes to `i(F)`. -/
theorem amalgamToGamma_false_of (f : Fxyt) :
    amalgamToGamma inp (Monoid.PushoutI.of (φ := amalgamDiagram inp) false f)
      = HNNExtension.of (iEmb inp f) :=
  amalgamToGamma_of_false inp f

/-- The second copy of `F` goes to `v i(F) v⁻¹ = t⁻¹ i(F) t`. -/
theorem amalgamToGamma_true_of (f : Fxyt) :
    amalgamToGamma inp (Monoid.PushoutI.of (φ := amalgamDiagram inp) true f)
      = Higman.Rope.gammaConj (witness inp) f := by
  rw [amalgamToGamma_of_true, vConjHom_eq_gammaConj]

/-- The amalgamated subgroup `N_e` sits in the first copy. -/
theorem base_eq_of_false (h : ↥inp.N) :
    Monoid.PushoutI.base (amalgamDiagram inp) h
      = Monoid.PushoutI.of (φ := amalgamDiagram inp) false (h : Fxyt) :=
  (Monoid.PushoutI.of_apply_eq_base (amalgamDiagram inp) false h).symm

/-- ... and therefore goes to `i(N_e)`. -/
theorem amalgamToGamma_base_apply (h : ↥inp.N) :
    amalgamToGamma inp (Monoid.PushoutI.base (amalgamDiagram inp) h)
      = HNNExtension.of (iEmb inp (h : Fxyt)) := by
  rw [base_eq_of_false]
  exact amalgamToGamma_false_of inp (h : Fxyt)

/-! ## 3.  Bookkeeping for Mathlib's normal words -/

/-- The empty normal word has no first letter. -/
theorem empty_fstIdx
    (d : Monoid.PushoutI.NormalWord.Transversal (amalgamDiagram inp)) :
    (Monoid.PushoutI.NormalWord.empty : Monoid.PushoutI.NormalWord d).fstIdx
      = none := rfl

/-- Prepending a letter of index `i` makes `i` the first index. -/
theorem cons_fstIdx
    (d : Monoid.PushoutI.NormalWord.Transversal (amalgamDiagram inp))
    {i : Bool} (g : Higman.Amalgam.fam Fxyt Fxyt i)
    (w : Monoid.PushoutI.NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (amalgamDiagram inp i).range) :
    (Monoid.PushoutI.NormalWord.cons g w hmw hgr).fstIdx = some i := rfl

/-- Multiplying by an element of the base group does not change the letters. -/
theorem baseSmul_fstIdx
    (d : Monoid.PushoutI.NormalWord.Transversal (amalgamDiagram inp))
    (h : ↥inp.N) (w : Monoid.PushoutI.NormalWord d) :
    (h • w).fstIdx = w.fstIdx := rfl

/-- ... it only multiplies the head. -/
theorem baseSmul_head
    (d : Monoid.PushoutI.NormalWord.Transversal (amalgamDiagram inp))
    (h : ↥inp.N) (w : Monoid.PushoutI.NormalWord d) :
    (h • w).head = h * w.head := rfl

/-! ## 4.  The invariant carried through the normal form -/

/-- **The block-word data attached to a normal word of `F *_{N_e} F`.**

`z₀` is the leading base element and `l` the list of blocks
`(v i(f) v⁻¹, base entry)`, so that the image of the word in `Γ_e` is the
block word `Higman.Pinch.word z₀ l`.  The three trailing clauses record what
the first index of the word forces, and are exactly what keeps `Clean`
provable when a letter is prepended. -/
def BrittonData
    (d : Monoid.PushoutI.NormalWord.Transversal (amalgamDiagram inp))
    (w : Monoid.PushoutI.NormalWord d) : Prop :=
  ∃ (z₀ : Ke inp) (l : List (Ke inp × Ke inp)),
    amalgamToGamma inp w.prod = Higman.Pinch.word (Le inp) z₀ l ∧
      Higman.Pinch.Clean (Le inp) l ∧
      (w.fstIdx = none →
        l = [] ∧ z₀ = iEmb inp (w.head : Fxyt) ∧
          w.prod =
            Monoid.PushoutI.of (φ := amalgamDiagram inp) false (w.head : Fxyt)) ∧
      (w.fstIdx = some false → z₀ ∉ Le inp) ∧
      (w.head = 1 → w.fstIdx = some true → z₀ = 1) ∧
      (w.fstIdx = some true → l ≠ [])

/-- **Every normal word carries the block-word data.**

The recursion is Mathlib's `consRecOn`, whose three cases are the empty word,
prepending a letter, and prepending an element of the amalgamated subgroup.
Prepending a `false` letter merges it into the leading base element
(`Higman.Pinch.of_mul_word`); prepending a `true` letter opens a new block
(`Higman.Pinch.conj_mul_word`), and the block is clean because its conjugated
entry is `i(g)` with `g ∉ N_e`, and its base entry is the old leading
element, which the case-clauses guarantee lies outside `L_e`. -/
theorem brittonData
    (d : Monoid.PushoutI.NormalWord.Transversal (amalgamDiagram inp))
    (w : Monoid.PushoutI.NormalWord d) : BrittonData inp d w := by
  letI : ∀ i : Bool, DecidableEq (Higman.Amalgam.fam Fxyt Fxyt i) :=
    fun _ => Classical.decEq _
  induction w using Monoid.PushoutI.NormalWord.consRecOn with
  | empty =>
      have hhead : (Monoid.PushoutI.NormalWord.empty :
          Monoid.PushoutI.NormalWord d).head = 1 := rfl
      refine ⟨1, [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Monoid.PushoutI.NormalWord.prod_empty, Higman.Pinch.word_nil]
        exact (map_one (amalgamToGamma inp)).trans
          (map_one (HNNExtension.of : Ke inp →* Higman.CentHNN (Le inp))).symm
      · simp [Higman.Pinch.Clean]
      · intro _
        refine ⟨rfl, ?_, ?_⟩
        · exact (map_one (iEmb inp)).symm
        · rw [Monoid.PushoutI.NormalWord.prod_empty, hhead]
          exact (map_one
            (Monoid.PushoutI.of (φ := amalgamDiagram inp) false)).symm
      · intro hfs
        rw [empty_fstIdx] at hfs
        exact absurd hfs (by simp)
      · intro _ _
        rfl
      · intro hfs
        rw [empty_fstIdx] at hfs
        exact absurd hfs (by simp)
  | cons i g w hmw hgn hgr hw1 ih =>
      obtain ⟨z₀, l, heq, hclean, h3, h4, h5, h6⟩ := ih
      cases i with
      | false =>
          change Fxyt at g
          have hgN : g ∉ inp.N := fun hg => hgr ⟨⟨g, hg⟩, rfl⟩
          have hz1 : iEmb inp g * z₀ ∉ Le inp := by
            rcases hfw : w.fstIdx with _ | b
            · obtain ⟨-, hz, -⟩ := h3 hfw
              have hz0 : z₀ = 1 := by
                rw [hz, hw1]
                simp
              rw [hz0, mul_one]
              exact iEmb_notMem_Le inp hgN
            · cases b with
              | false => exact absurd hfw hmw
              | true =>
                  rw [h5 hw1 hfw, mul_one]
                  exact iEmb_notMem_Le inp hgN
          refine ⟨iEmb inp g * z₀, l, ?_, hclean, ?_, ?_, ?_, ?_⟩
          · rw [Monoid.PushoutI.NormalWord.prod_cons, map_mul,
              amalgamToGamma_false_of, heq]
            exact Higman.Pinch.of_mul_word (Le inp) (iEmb inp g) z₀ l
          · intro hfs
            rw [cons_fstIdx] at hfs
            exact absurd hfs (by simp)
          · intro _
            exact hz1
          · intro _ hfs
            rw [cons_fstIdx] at hfs
            exact absurd hfs (by simp)
          · intro hfs
            rw [cons_fstIdx] at hfs
            exact absurd hfs (by simp)
      | true =>
          change Fxyt at g
          have hgN : g ∉ inp.N := fun hg => hgr ⟨⟨g, hg⟩, rfl⟩
          have hgL : iEmb inp g ∉ Le inp := iEmb_notMem_Le inp hgN
          refine ⟨1, (iEmb inp g, z₀) :: l, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [Monoid.PushoutI.NormalWord.prod_cons, map_mul,
              amalgamToGamma_true_of, heq]
            exact Higman.Pinch.conj_mul_word (Le inp) (iEmb inp g) z₀ l
          · cases l with
            | nil => exact hgL
            | cons p l' =>
                refine ⟨hgL, ?_, hclean⟩
                rcases hfw : w.fstIdx with _ | b
                · obtain ⟨hl, -, -⟩ := h3 hfw
                  exact absurd hl (by simp)
                · cases b with
                  | false => exact h4 hfw
                  | true => exact absurd hfw hmw
          · intro hfs
            rw [cons_fstIdx] at hfs
            exact absurd hfs (by simp)
          · intro hfs
            rw [cons_fstIdx] at hfs
            exact absurd hfs (by simp)
          · intro _ _
            rfl
          · intro _
            exact List.cons_ne_nil _ _
  | base h w hw1 ih =>
      obtain ⟨z₀, l, heq, hclean, h3, h4, h5, h6⟩ := ih
      have hhL : iEmb inp (h : Fxyt) ∈ Le inp := iEmb_mem_Le inp h.2
      refine ⟨iEmb inp (h : Fxyt) * z₀, l, ?_, hclean, ?_, ?_, ?_, ?_⟩
      · rw [Monoid.PushoutI.NormalWord.prod_smul, map_mul,
          amalgamToGamma_base_apply, heq]
        exact Higman.Pinch.of_mul_word (Le inp) (iEmb inp (h : Fxyt)) z₀ l
      · intro hfs
        rw [Monoid.PushoutI.NormalWord.base_smul_eq_smul,
          baseSmul_fstIdx] at hfs
        obtain ⟨hl, hz, hp⟩ := h3 hfs
        refine ⟨hl, ?_, ?_⟩
        · simp [Monoid.PushoutI.NormalWord.base_smul_eq_smul,
            baseSmul_head, hw1, hz]
        · have hhd : (Monoid.PushoutI.base (amalgamDiagram inp) h • w).head
              = h := by
            rw [Monoid.PushoutI.NormalWord.base_smul_eq_smul, baseSmul_head,
              hw1, mul_one]
          have hp1 : w.prod = 1 := by
            rw [hp, hw1]
            exact map_one
              (Monoid.PushoutI.of (φ := amalgamDiagram inp) false)
          rw [hhd, Monoid.PushoutI.NormalWord.prod_smul, hp1, mul_one,
            base_eq_of_false]
      · intro hfs hmem
        rw [Monoid.PushoutI.NormalWord.base_smul_eq_smul,
          baseSmul_fstIdx] at hfs
        have hinv : (iEmb inp (h : Fxyt))⁻¹ ∈ Le inp := Subgroup.inv_mem _ hhL
        have hmul := Subgroup.mul_mem _ hinv hmem
        rw [← mul_assoc, inv_mul_cancel, one_mul] at hmul
        exact h4 hfs hmul
      · intro hhead hfs
        rw [Monoid.PushoutI.NormalWord.base_smul_eq_smul,
          baseSmul_fstIdx] at hfs
        rw [Monoid.PushoutI.NormalWord.base_smul_eq_smul,
          baseSmul_head, hw1, mul_one] at hhead
        rw [h5 hw1 hfs, hhead]
        simp
      · intro hfs
        rw [Monoid.PushoutI.NormalWord.base_smul_eq_smul,
          baseSmul_fstIdx] at hfs
        exact h6 hfs

/-! ## 5.  Britton's lemma closes the argument -/

/-- **`lem:central-rope`(2), the Britton step.**

"Such a word contains no pinch `v^{±1} ℓ v^{∓1}` with `ℓ ∈ L_e`, so it is
nontrivial in `Γ_e` by Britton's lemma."

Given `θ(x) = 1`, the block word attached to the normal form of `x` lies in
the base `K_e`, so `Higman.Pinch.eq_nil_of_clean` empties its block list; the
first index of the normal form is then neither `some true` (a nonempty block
list) nor `some false` (its leading element would have to lie outside `L_e`,
yet it is `1`), so the word is a single element of the amalgamated subgroup,
and `i` is injective. -/
theorem amalgamToGamma_injective :
    Function.Injective (amalgamToGamma inp) := by
  classical
  letI : ∀ i : Bool, DecidableEq (Higman.Amalgam.fam Fxyt Fxyt i) :=
    fun _ => Classical.decEq _
  refine (injective_iff_map_eq_one (amalgamToGamma inp)).mpr ?_
  intro x hx
  obtain ⟨d⟩ := Monoid.PushoutI.NormalWord.transversal_nonempty
    (amalgamDiagram inp)
    (Higman.Amalgam.famHom_injective inp.N.subtype inp.N.subtype
      (Subgroup.subtype_injective inp.N) (Subgroup.subtype_injective inp.N))
  set w : Monoid.PushoutI.NormalWord d :=
    x • (Monoid.PushoutI.NormalWord.empty : Monoid.PushoutI.NormalWord d) with hwdef
  have hprod : w.prod = x := by
    rw [hwdef, Monoid.PushoutI.NormalWord.prod_smul,
      Monoid.PushoutI.NormalWord.prod_empty, mul_one]
  obtain ⟨z₀, l, heq, hclean, h3, h4, h5, h6⟩ := brittonData inp d w
  rw [hprod, hx] at heq
  have hmem : Higman.Pinch.word (Le inp) z₀ l
      ∈ (HNNExtension.of : Ke inp →* CentralRope inp).range :=
    ⟨1, by rw [map_one]; exact heq⟩
  have hl : l = [] :=
    Higman.Pinch.eq_nil_of_clean (Le inp) z₀ l hclean hmem
  have hz0 : z₀ = 1 := by
    rw [hl, Higman.Pinch.word_nil] at heq
    refine Higman.of_injective_centHNN (Le inp) ?_
    exact heq.symm.trans
      (map_one (HNNExtension.of : Ke inp →* Higman.CentHNN (Le inp))).symm
  rcases hfw : w.fstIdx with _ | b
  · obtain ⟨-, hz, hp⟩ := h3 hfw
    have hhead : (w.head : Fxyt) = 1 := by
      apply iEmb_injective inp
      rw [← hz, hz0, map_one]
    rw [← hprod, hp, hhead]
    exact map_one (Monoid.PushoutI.of (φ := amalgamDiagram inp) false)
  · cases b with
    | false =>
        exact absurd (hz0 ▸ Subgroup.one_mem (Le inp)) (h4 hfw)
    | true => exact absurd hl (h6 hfw)

/-! ## 6. The resulting amalgam isomorphism -/

/-- **The printed natural map `F *_{N_e} F → S_e`.** -/
noncomputable def amalgamHom : Amalgam inp →* ↥(RopeS inp) :=
  MonoidHom.codRestrict (amalgamToGamma inp) (RopeS inp) (amalgamToGamma_mem inp)

@[simp] theorem coe_amalgamHom (a : Amalgam inp) :
    ((amalgamHom inp a : ↥(RopeS inp)) : CentralRope inp)
      = amalgamToGamma inp a := rfl

theorem amalgamHom_surjective : Function.Surjective (amalgamHom inp) := by
  intro b
  have hb : (b : CentralRope inp) ∈ (amalgamToGamma inp).range := by
    rw [amalgamToGamma_range]
    exact b.2
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, Subtype.ext ha⟩

theorem amalgamHom_injective : Function.Injective (amalgamHom inp) := by
  intro a b hab
  exact amalgamToGamma_injective inp
    (congrArg (fun z : ↥(RopeS inp) => (z : CentralRope inp)) hab)

/-- **`lem:central-rope`(2), last clause.** The natural map from the
amalgamated free product `F *_{N_e} F` onto `S_e` is an isomorphism. -/
noncomputable def amalgamEquiv : Amalgam inp ≃* ↥(RopeS inp) :=
  MulEquiv.ofBijective (amalgamHom inp)
    ⟨amalgamHom_injective inp, amalgamHom_surjective inp⟩

/-- The isomorphism sends the first copy to `i(F)`. -/
theorem amalgamEquiv_first (g : Fxyt) :
    ((amalgamEquiv inp (Monoid.PushoutI.of (φ := amalgamDiagram inp) false g) :
        ↥(RopeS inp)) : CentralRope inp) = iGammaHom inp g := by
  show amalgamToGamma inp
      (Monoid.PushoutI.of (φ := amalgamDiagram inp) false g) = iGammaHom inp g
  exact amalgamToGamma_of_false inp g

/-- The isomorphism sends the second copy to `v i(F) v⁻¹`. -/
theorem amalgamEquiv_second (g : Fxyt) :
    ((amalgamEquiv inp (Monoid.PushoutI.of (φ := amalgamDiagram inp) true g) :
        ↥(RopeS inp)) : CentralRope inp) = vConjHom inp g := by
  show amalgamToGamma inp
      (Monoid.PushoutI.of (φ := amalgamDiagram inp) true g) = vConjHom inp g
  exact amalgamToGamma_of_true inp g

end
end RopeInput
end Rope
end MFRecognition
end Manuscript
end GroupApproximation
