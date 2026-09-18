import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRoot
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRingPropertyT
import GroupApproximation.Dynamics.ClopenGroupCrossedProduct
import Mathlib.Data.Set.Finite.List
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity, Step 1 set-up: word-length bound, small clopen sets, dense moved points

`simple_kazhdan_sofic_group.tex`, subsection "Simplicity", proof of `thm:general` (a), tex
l.241–253:

> Let $1\ne K\trianglelefteq G$ and $1\ne g\in K$. (l.241)
>
> Let $w\ge0$ bound the word lengths of the $\xi$ with $u_\xi$ occurring in the entries of $g$ and
> $g^{-1}$. (l.245–246) Call a clopen set $V$ small if (i) $V\cap\xi V=\varnothing$ for every
> $\xi\in B_{2w}\setminus\{e\}$, and (ii) $f\circ\xi$ is constant on $V$ for every $\xi\in B_w$ and
> every coefficient $f\in\LC(C,\F_2)$ of an entry of $g$ or $g^{-1}$. (l.246–249) Each $\xi\ne e$
> fixes a closed set with empty interior, so the points moved by every
> $\xi\in B_{2w}\setminus\{e\}$ form a dense open set. (l.249–251) Small enough clopen neighborhoods
> of these points are small, so every nonempty clopen set contains a nonempty small one.
> (l.251–253)

Setting: `G = EL_n(R)` with `R = ClopenGroupCrossedProduct Λ Z (ZMod 2)`, the crossed product
`LC(Z, F_2) ⋊ Λ`. The ball `B_m` is `SimpleKazhdanSofic.wordBall T m`, where `T` is a finite
symmetric generating set of `Λ`. Topological freeness is `interior {z | ξ • z = z} = ∅` for `ξ ≠ e`.

Proof route:

* the word-length bound `w` exists because the supports of the entries are finite and every element
  of `Λ` lies in some ball (`exists_mem_wordBall`);
* the balls are finite (`finite_wordBall`), so they can be passed as the finite sets `D`, `B` of
  `General.IsSmall`; the printed "small" (`IsPrintedSmall`) follows from it
  (`isPrintedSmall_of_isSmall`);
* the moved points form a finite intersection of complements of closed fixed-point sets, each of
  them dense (`General.dense_moved`);
* around a moved point, the clopen neighbourhood of `General.exists_isSmall_subset` without the
  ambient set `A` is small (`exists_isSmall_nhds`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SimplicitySteps

open scoped Pointwise commutatorElement

/-! ### Word balls -/

section WordBall

variable {Λ : Type*} [Group Λ]

/-- The balls increase with the radius. -/
theorem wordBall_mono (T : Set Λ) {m m' : ℕ} (h : m ≤ m') : wordBall T m ⊆ wordBall T m' := by
  rintro ξ ⟨l, hl, hlT, rfl⟩
  exact ⟨l, hl.trans h, hlT, rfl⟩

/-- A ball over a finite set of letters is finite. -/
theorem finite_wordBall {T : Set Λ} (hT : T.Finite) (m : ℕ) : (wordBall T m).Finite := by
  haveI : Finite ↥T := hT.to_subtype
  refine ((List.finite_length_le (↥T) m).image
    fun l : List ↥T => (l.map Subtype.val).prod).subset ?_
  rintro ξ ⟨l, hl, hlT, rfl⟩
  refine ⟨l.attachWith (fun x => x ∈ T) hlT, ?_, ?_⟩
  · show (l.attachWith (fun x => x ∈ T) hlT).length ≤ m
    rw [List.length_attachWith]
    exact hl
  · show ((l.attachWith (fun x => x ∈ T) hlT).map Subtype.val).prod = l.prod
    rw [List.attachWith_map_subtype_val]

/-- Every element lies in some ball over a symmetric generating set. -/
theorem exists_mem_wordBall {T : Set Λ} (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure T = ⊤) (ξ : Λ) : ∃ m : ℕ, ξ ∈ wordBall T m := by
  have h1 : ξ ∈ Subgroup.closure T := by
    rw [hgen]
    exact Subgroup.mem_top ξ
  have hξ : ξ ∈ Submonoid.closure (T ∪ T⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact h1
  obtain ⟨l, hlT, hl⟩ := Submonoid.exists_list_of_mem_closure hξ
  refine ⟨l.length, l, le_rfl, fun x hx => ?_, hl⟩
  rcases hlT x hx with h | h
  · exact h
  · have h' := hsymm x⁻¹ (Set.mem_inv.mp h)
    rwa [inv_inv] at h'

end WordBall

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]

/-! ### The word-length bound `w` -/

/-- **tex l.245–246**: there is `w ≥ 0` bounding the word lengths of the `ξ` with `u_ξ` occurring in
the entries of `g` and `g⁻¹`: every such `ξ` lies in the ball `B_w`. -/
theorem manuscriptSentence_wordLengthBound {T : Set Λ} (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure T = ⊤) {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :
    ∃ w : ℕ, ∀ (p q : Fin n) (ξ : Λ),
      (ξ ∈ SkewMonoidAlgebra.support (General.mat g p q) ∨
          ξ ∈ SkewMonoidAlgebra.support (General.mat g⁻¹ p q)) →
        ξ ∈ wordBall T w := by
  classical
  choose m hm using exists_mem_wordBall hsymm hgen
  obtain ⟨s, hs⟩ : ∃ s : Finset Λ, ∀ (p q : Fin n) (ξ : Λ),
      (ξ ∈ SkewMonoidAlgebra.support (General.mat g p q) ∨
          ξ ∈ SkewMonoidAlgebra.support (General.mat g⁻¹ p q)) → ξ ∈ s :=
    ⟨Finset.univ.biUnion fun pq : Fin n × Fin n =>
        SkewMonoidAlgebra.support (General.mat g pq.1 pq.2) ∪
          SkewMonoidAlgebra.support (General.mat g⁻¹ pq.1 pq.2),
      fun p q ξ hξ => Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _, Finset.mem_union.mpr hξ⟩⟩
  exact ⟨s.sup m, fun p q ξ hξ =>
    wordBall_mono T (Finset.le_sup (f := m) (hs p q ξ hξ)) (hm ξ)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_wordLengthBound

/-! ### Coefficients of the entries of `g` -/

/-- The coefficient `f ∈ LC(Z, F_2)` of `u_η` in the entry `(p, q)` of `g`. -/
noncomputable def entryCoeff {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (p q : Fin n) (η : Λ) :
    LocallyConstant Z (ZMod 2) :=
  (ClopenGroupCoeff.of Λ Z (ZMod 2)).symm (SkewMonoidAlgebra.coeff (General.mat g p q) η)

/-- The coefficient at a `u_η` outside the support vanishes. -/
theorem entryCoeff_apply_eq_zero {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) {p q : Fin n} {η : Λ}
    (hη : η ∉ SkewMonoidAlgebra.support (General.mat g p q)) (z : Z) :
    entryCoeff g p q η z = 0 := by
  have h0 := SkewMonoidAlgebra.notMem_support_iff.mp hη
  unfold entryCoeff
  rw [h0, map_zero, LocallyConstant.zero_apply]

open Classical in
/-- The finite set of coefficients `f ∈ LC(Z, F_2)` of the entries of `g` and `g⁻¹`. -/
noncomputable def coeffFinset {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :
    Finset (LocallyConstant Z (ZMod 2)) :=
  Finset.univ.biUnion fun pq : Fin n × Fin n =>
    (SkewMonoidAlgebra.support (General.mat g pq.1 pq.2)).image (entryCoeff g pq.1 pq.2) ∪
      (SkewMonoidAlgebra.support (General.mat g⁻¹ pq.1 pq.2)).image (entryCoeff g⁻¹ pq.1 pq.2)

theorem mem_coeffFinset_left {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) {p q : Fin n} {η : Λ}
    (hη : η ∈ SkewMonoidAlgebra.support (General.mat g p q)) :
    entryCoeff g p q η ∈ coeffFinset g := by
  classical
  unfold coeffFinset
  exact Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _,
    Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ hη))⟩

theorem mem_coeffFinset_right {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) {p q : Fin n} {η : Λ}
    (hη : η ∈ SkewMonoidAlgebra.support (General.mat g⁻¹ p q)) :
    entryCoeff g⁻¹ p q η ∈ coeffFinset g := by
  classical
  unfold coeffFinset
  exact Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_univ _,
    Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ hη))⟩

/-! ### Small clopen sets -/

/-- **tex l.246–249, the printed "small"**: a clopen set `V` is small if (i) `V ∩ ξV = ∅` for every
`ξ ∈ B_{2w} ∖ {e}`, and (ii) `f ∘ ξ` is constant on `V` for every `ξ ∈ B_w` and every coefficient
`f ∈ LC(Z, F_2)` of an entry of `g` or `g⁻¹`. -/
def IsPrintedSmall (T : Set Λ) (w : ℕ) {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (V : Set Z) : Prop :=
  IsClopen V ∧ (∀ ξ ∈ wordBall T (2 * w), ξ ≠ 1 → Disjoint V (ξ • V)) ∧
    ∀ (p q : Fin n) (η : Λ), ∀ ξ ∈ wordBall T w, ∀ x ∈ V, ∀ y ∈ V,
      entryCoeff g p q η (ξ • x) = entryCoeff g p q η (ξ • y) ∧
        entryCoeff g⁻¹ p q η (ξ • x) = entryCoeff g⁻¹ p q η (ξ • y)

/-- The finite-set version `General.IsSmall` over the balls and `coeffFinset g` gives the printed
"small". -/
theorem isPrintedSmall_of_isSmall {T : Set Λ} (hT : T.Finite) (w : ℕ) {n : ℕ}
    (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) {V : Set Z}
    (hV : IsClopen V)
    (hs : General.IsSmall (finite_wordBall hT (2 * w)).toFinset (finite_wordBall hT w).toFinset
      (coeffFinset g) V) :
    IsPrintedSmall T w g V := by
  refine ⟨hV, fun ξ hξ h1 => hs.1 ξ ((finite_wordBall hT (2 * w)).mem_toFinset.mpr hξ) h1,
    fun p q η ξ hξ x hx y hy => ⟨?_, ?_⟩⟩
  · by_cases hη : η ∈ SkewMonoidAlgebra.support (General.mat g p q)
    · exact hs.2 _ (mem_coeffFinset_left g hη) ξ ((finite_wordBall hT w).mem_toFinset.mpr hξ)
        x hx y hy
    · rw [entryCoeff_apply_eq_zero g hη, entryCoeff_apply_eq_zero g hη]
  · by_cases hη : η ∈ SkewMonoidAlgebra.support (General.mat g⁻¹ p q)
    · exact hs.2 _ (mem_coeffFinset_right g hη) ξ ((finite_wordBall hT w).mem_toFinset.mpr hξ)
        x hx y hy
    · rw [entryCoeff_apply_eq_zero g⁻¹ hη, entryCoeff_apply_eq_zero g⁻¹ hη]

/-! ### Dense open set of moved points -/

/-- **tex l.249–251**: each `ξ ≠ e` fixes a closed set with empty interior, so the points moved by
every `ξ ∈ B_{2w} ∖ {e}` form a dense open set. -/
theorem manuscriptSentence_movedPointsDenseOpen [T2Space Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {T : Set Λ} (hT : T.Finite)
    (w : ℕ) :
    (∀ ξ : Λ, ξ ≠ 1 → IsClosed {z : Z | ξ • z = z} ∧ interior {z : Z | ξ • z = z} = ∅) ∧
      IsOpen {z : Z | ∀ ξ ∈ wordBall T (2 * w), ξ ≠ 1 → ξ • z ≠ z} ∧
        Dense {z : Z | ∀ ξ ∈ wordBall T (2 * w), ξ ≠ 1 → ξ • z ≠ z} := by
  have hfin := finite_wordBall hT (2 * w)
  have heq : {z : Z | ∀ ξ ∈ wordBall T (2 * w), ξ ≠ 1 → ξ • z ≠ z} =
      {z : Z | ∀ ξ ∈ hfin.toFinset, ξ ≠ 1 → ξ • z ≠ z} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset]
  have hopen : ∀ ξ : Λ, IsOpen {z : Z | ξ ≠ 1 → ξ • z ≠ z} := by
    intro ξ
    by_cases h1 : ξ = 1
    · have huniv : {z : Z | ξ ≠ 1 → ξ • z ≠ z} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun h => absurd h1 h
      rw [huniv]
      exact isOpen_univ
    · have hcompl : {z : Z | ξ ≠ 1 → ξ • z ≠ z} = {z : Z | ξ • z = z}ᶜ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        exact ⟨fun h hfix => h h1 hfix, fun h _ => h⟩
      rw [hcompl]
      exact (General.isClosed_fixed ξ).isOpen_compl
  have hbiInter : {z : Z | ∀ ξ ∈ hfin.toFinset, ξ ≠ 1 → ξ • z ≠ z} =
      ⋂ ξ ∈ hfin.toFinset, {z : Z | ξ ≠ 1 → ξ • z ≠ z} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  refine ⟨fun ξ h1 => ⟨General.isClosed_fixed ξ, hfree ξ h1⟩, ?_, ?_⟩
  · rw [heq, hbiInter]
    exact isOpen_biInter_finset fun ξ _ => hopen ξ
  · rw [heq]
    exact General.dense_moved hfree hfin.toFinset

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_movedPointsDenseOpen

/-- A moved point has a small clopen neighbourhood (`General.exists_isSmall_subset` without the
ambient clopen set). -/
theorem exists_isSmall_nhds [TotallySeparatedSpace Z] (D B : Finset Λ)
    (F : Finset (LocallyConstant Z (ZMod 2))) {x : Z} (hxm : ∀ ξ ∈ D, ξ ≠ 1 → ξ • x ≠ x) :
    ∃ U : Set Z, IsClopen U ∧ x ∈ U ∧ General.IsSmall D B F U := by
  classical
  have hsep : ∀ ξ ∈ D, ∃ C : Set Z, ξ ≠ 1 → IsClopen C ∧ x ∈ C ∧ ξ • x ∈ Cᶜ := by
    intro ξ hξ
    by_cases h1 : ξ = 1
    · exact ⟨Set.univ, fun h => absurd h1 h⟩
    · obtain ⟨C, hC, hxC, hyC⟩ := exists_isClopen_of_totally_separated (hxm ξ hξ h1).symm
      exact ⟨C, fun _ => ⟨hC, hxC, hyC⟩⟩
  choose! C hC using hsep
  refine ⟨(⋂ ξ ∈ D.filter (fun ξ => ξ ≠ 1), (C ξ ∩ (fun z => ξ • z) ⁻¹' (C ξ)ᶜ)) ∩
      ⋂ p ∈ F ×ˢ B, (fun z => p.2 • z) ⁻¹' {y | p.1 y = p.1 (p.2 • x)}, ?_, ?_, ?_⟩
  · refine (isClopen_biInter_finset fun ξ hξ => ?_).inter
      (isClopen_biInter_finset fun p _ => ?_)
    · have h1 := Finset.mem_filter.mp hξ
      obtain ⟨hCc, -, -⟩ := hC ξ h1.1 h1.2
      exact hCc.inter (hCc.compl.preimage (continuous_const_smul ξ))
    · exact (p.1.isLocallyConstant.isClopen_fiber _).preimage (continuous_const_smul p.2)
  · refine ⟨Set.mem_iInter₂.mpr fun ξ hξ => ?_, Set.mem_iInter₂.mpr fun p _ => rfl⟩
    have h1 := Finset.mem_filter.mp hξ
    obtain ⟨-, hxC, hyC⟩ := hC ξ h1.1 h1.2
    exact ⟨hxC, hyC⟩
  · refine ⟨fun ξ hξ h1 => ?_, fun f hf ξ hξ y hy z hz => ?_⟩
    · rw [Set.disjoint_left]
      intro z hz hzξ
      obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hzξ
      have hmem : ξ ∈ D.filter (fun ξ => ξ ≠ 1) := Finset.mem_filter.mpr ⟨hξ, h1⟩
      have hzC : ξ • v ∈ C ξ := (Set.mem_iInter₂.mp hz.1 ξ hmem).1
      have hvC : ξ • v ∈ (C ξ)ᶜ := (Set.mem_iInter₂.mp hv.1 ξ hmem).2
      exact hvC hzC
    · have hmem : (f, ξ) ∈ F ×ˢ B := Finset.mem_product.mpr ⟨hf, hξ⟩
      have h1 : f (ξ • y) = f (ξ • x) := Set.mem_iInter₂.mp hy.2 (f, ξ) hmem
      have h2 : f (ξ • z) = f (ξ • x) := Set.mem_iInter₂.mp hz.2 (f, ξ) hmem
      exact h1.trans h2.symm

/-- **tex l.251–253**: small enough clopen neighbourhoods of the moved points are small: every point
moved by every `ξ ∈ B_{2w} ∖ {e}` has a clopen neighbourhood all of whose clopen subsets are small.
So every nonempty clopen set contains a nonempty small one. -/
theorem manuscriptSentence_smallClopenNeighbourhoods [TotallySeparatedSpace Z]
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) {T : Set Λ} (hT : T.Finite)
    (w : ℕ) {n : ℕ} (g : elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :
    (∀ x : Z, (∀ ξ ∈ wordBall T (2 * w), ξ ≠ 1 → ξ • x ≠ x) →
        ∃ U : Set Z, IsClopen U ∧ x ∈ U ∧
          ∀ V : Set Z, IsClopen V → V ⊆ U → IsPrintedSmall T w g V) ∧
      ∀ A : Set Z, IsClopen A → A.Nonempty →
        ∃ V : Set Z, V.Nonempty ∧ V ⊆ A ∧ IsPrintedSmall T w g V := by
  refine ⟨fun x hx => ?_, fun A hA hne => ?_⟩
  · obtain ⟨U, hU, hxU, hs⟩ := exists_isSmall_nhds (finite_wordBall hT (2 * w)).toFinset
      (finite_wordBall hT w).toFinset (coeffFinset g)
      (x := x) fun ξ hξ h1 => hx ξ ((finite_wordBall hT (2 * w)).mem_toFinset.mp hξ) h1
    exact ⟨U, hU, hxU, fun V hV hVU => isPrintedSmall_of_isSmall hT w g hV (hs.mono hVU)⟩
  · obtain ⟨V, hV, hVne, hVA, hs⟩ := General.exists_isSmall_subset hfree
      (finite_wordBall hT (2 * w)).toFinset (finite_wordBall hT w).toFinset (coeffFinset g) hA hne
    exact ⟨V, hVne, hVA, isPrintedSmall_of_isSmall hT w g hV hs⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_smallClopenNeighbourhoods

/-! ### The opening sentence -/

/-- **tex l.241**: let `1 ≠ K ⊴ G` and pick `1 ≠ g ∈ K`: a nontrivial normal subgroup of
`G = EL_n(LC(Z, F_2) ⋊ Λ)` has a nontrivial element. -/
theorem manuscriptSentence_letNontrivialNormalSubgroupAndElement {n : ℕ}
    (K : Subgroup (elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))
    (_hK : K.Normal) (hne : K ≠ ⊥) : ∃ g ∈ K, g ≠ 1 :=
  (Subgroup.bot_or_exists_ne_one K).resolve_left hne

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.manuscriptSentence_letNontrivialNormalSubgroupAndElement

end SimplicitySteps
end SimpleKazhdanSofic
end GroupApproximation
