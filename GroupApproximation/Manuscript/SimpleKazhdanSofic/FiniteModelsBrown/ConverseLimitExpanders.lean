import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanGeneralClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTheorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialMarkedLimitWords
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FreeAlgebraKazhdan
import GroupApproximation.Manuscript.SimpleKazhdanSofic.KazhdanQuotientExpanders
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialQuotientsExpanders
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# "Finite simple models", tex 332–342: the converse, the limit, and the expanders

`simple_kazhdan_sofic_group.tex`, subsection "Finite simple models" (proof of Theorem
`thm:general`(b)), with `G = EL_n(R)`, `R = LC(Z, F₂) ⋊ Λ`, marked by the `e_ij(s)`, `s ∈ S`:

> (tex 332–333) Conversely, let $w$ be a word that is nontrivial in $G$.
> (tex 333–334) As $G$ is simple, $e_{12}(1)$ is a product of conjugates of $w$ and $w^{-1}$ in $G$.
> (tex 334–336) This relation holds in $\SL_{3N_k}(\F_2)$ for large $k$, where $e_{12}(1)$ maps to the
> transvection $e_{12}(I)\ne I$, so $w$ is nontrivial in $\SL_{3N_k}(\F_2)$ for large $k$.
> (tex 336–338) Therefore these marked finite simple groups converge to $G$, so $G$ is LEF, and
> $N_k\to\infty$ because $G$ is infinite.
> (tex 338–342) Since $\EL_3(\mathcal A)$ has property~(T)~[EJZ, Theorem 1.1], the Cayley graphs of
> its finite quotients with respect to the images of its generators form a family of
> expanders~[Margulis, Kassabov], so $G$ is an expander limit of the $\SL_{3N_k}(\F_2)$.

Every endpoint carries the full hypotheses of `thm:general` (minimal topologically free action of a
finitely generated `Λ` on a Cantor set, finite `S ∋ 1` generating `R`, `R` matricial via `φ_k`) and
is stated for every rank `n ≥ 3` (the printed text uses `n = 3`).

Proof route:

* Simplicity of `G`, the marked limit, the identification `EL_n(M_{N_k}(F₂)) = SL_{nN_k}(F₂)`, the
  simplicity of the finite groups, infiniteness and the expander family are the closed theorem
  `printedSimpleKazhdanGeneral`.
* "product of conjugates": in a simple group the normal closure of `g ≠ 1` is everything
  (`mem_normalClosure_of_isSimpleGroup`), and every element of a normal closure is a product of
  conjugates of `g` and `g⁻¹` (`exists_list_isConj_of_mem_normalClosure`, by closure induction).
* "This relation holds for large k": lift the relation to a word `r` in the normal closure of `w`
  (`exists_word_mem_normalClosure`, via `Subgroup.map_normalClosure`); the marked limit makes
  `r = e_12(1)` hold in the models eventually, and a normal subgroup containing `w` would contain
  `e_12(I) ≠ I` (`eventually_lift_ne_one_of_mem_normalClosure`).
* LEF: `isTextbookLEF_of_isMarkedLimit`, `isLEF_of_isMarkedLimit`; `N_k → ∞`:
  `tendsto_card_of_isMarkedLimit` and `tendsto_atTop_of_tendsto_card_comp`.
* Expanders: `hasKazhdanPropertyT_elementaryGroup_freeAlgebra` (the proved EJZ theorem),
  `isExpanderFamily_of_hasKazhdanPropertyT_quotients` (finite quotients of a Kazhdan group form
  expanders), the quotient maps `EL_n(ρ_k)` (`elementaryGroupMap_surjective_of_surjective`,
  `lift_surjective_of_closure`) and the compatibility of the markings.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace FiniteModelsBrown

open Filter

/-! ## Normal closures and products of conjugates -/

theorem isConj_inv_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by rw [← hc, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]⟩

/-- Every element of the normal closure of `g` is a product of conjugates of `g` and `g⁻¹`. -/
theorem exists_list_isConj_of_mem_normalClosure {G : Type*} [Group G] {g x : G}
    (hx : x ∈ Subgroup.normalClosure ({g} : Set G)) :
    ∃ l : List G, (∀ y ∈ l, IsConj g y ∨ IsConj g⁻¹ y) ∧ l.prod = x := by
  change x ∈ Subgroup.closure (Group.conjugatesOfSet ({g} : Set G)) at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at hay
    refine ⟨[y], fun z hz => ?_, List.prod_singleton⟩
    rw [List.mem_singleton] at hz
    rw [hz]
    exact Or.inl hay
  | one => exact ⟨[], fun z hz => absurd hz List.not_mem_nil, List.prod_nil⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨l₁, hl₁, hp₁⟩ := ihy
    obtain ⟨l₂, hl₂, hp₂⟩ := ihz
    refine ⟨l₁ ++ l₂, fun u hu => ?_, by rw [List.prod_append, hp₁, hp₂]⟩
    rcases List.mem_append.1 hu with hu | hu
    · exact hl₁ u hu
    · exact hl₂ u hu
  | inv y _ ihy =>
    obtain ⟨l, hl, hp⟩ := ihy
    refine ⟨(l.map fun z => z⁻¹).reverse, fun u hu => ?_, by rw [← List.prod_inv_reverse, hp]⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hu)
    rcases hl v hv with h | h
    · exact Or.inr (isConj_inv_of_isConj h)
    · have h' := isConj_inv_of_isConj h
      rw [inv_inv] at h'
      exact Or.inl h'

/-- In a simple group, every element lies in the normal closure of any `g ≠ 1`. -/
theorem mem_normalClosure_of_isSimpleGroup {G : Type*} [Group G] (hG : IsSimpleGroup G) {g : G}
    (hg : g ≠ 1) (x : G) : x ∈ Subgroup.normalClosure ({g} : Set G) := by
  haveI := hG
  have htop : Subgroup.normalClosure ({g} : Set G) = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({g} : Set G))
      inferInstance).resolve_left fun hbot => hg ?_
    have hmem : g ∈ Subgroup.normalClosure ({g} : Set G) :=
      Subgroup.subset_normalClosure (Set.mem_singleton g)
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  rw [htop]
  exact Subgroup.mem_top x

/-! ## Transferring relations along a marked limit -/

section MarkedLimits

variable {ι G : Type*} [Group G] {s : ι → G} {H : ℕ → Type*} [∀ ℓ, Group (H ℓ)]
  {σ : ∀ ℓ, ι → H ℓ}

/-- Elements of the normal closure of the value of a word `w` are values of words in the normal
closure of `w`. -/
theorem exists_word_mem_normalClosure (hlim : IsMarkedLimit s σ) {w : FreeGroup ι} {x : G}
    (hx : x ∈ Subgroup.normalClosure ({FreeGroup.lift s w} : Set G)) :
    ∃ r ∈ Subgroup.normalClosure ({w} : Set (FreeGroup ι)), FreeGroup.lift s r = x := by
  have hsurj : Function.Surjective (FreeGroup.lift s) := fun g =>
    exists_word_of_isMarkedLimit hlim g
  have heq : ({FreeGroup.lift s w} : Set G) = (FreeGroup.lift s) '' {w} := Set.image_singleton.symm
  rw [heq, ← Subgroup.map_normalClosure _ _ hsurj] at hx
  exact Subgroup.mem_map.1 hx

/-- **The transfer of a relation** (tex 334–336): if a word `r` in the normal closure of `w` has the
same value in `G` as a word `u`, then `r = u` holds in the models for large `ℓ`; if moreover `u` is
eventually nontrivial in the models, then so is `w`. -/
theorem eventually_lift_ne_one_of_mem_normalClosure (hlim : IsMarkedLimit s σ)
    {w r u : FreeGroup ι} (hr : r ∈ Subgroup.normalClosure ({w} : Set (FreeGroup ι)))
    (hru : FreeGroup.lift s r = FreeGroup.lift s u)
    (hu : ∀ᶠ ℓ in atTop, FreeGroup.lift (σ ℓ) u ≠ 1) :
    (∀ᶠ ℓ in atTop, FreeGroup.lift (σ ℓ) r = FreeGroup.lift (σ ℓ) u) ∧
      ∀ᶠ ℓ in atTop, FreeGroup.lift (σ ℓ) w ≠ 1 := by
  obtain ⟨-, -, hw⟩ := hlim
  have hrel : ∀ᶠ ℓ in atTop, FreeGroup.lift (σ ℓ) r = FreeGroup.lift (σ ℓ) u := by
    filter_upwards [hw (u⁻¹ * r)] with ℓ hℓ
    have h1 : FreeGroup.lift s (u⁻¹ * r) = 1 := by
      rw [map_mul, map_inv, hru, inv_mul_cancel]
    have h2 := hℓ.2 h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2.symm
  refine ⟨hrel, ?_⟩
  filter_upwards [hrel, hu] with ℓ hℓ hne hw1
  apply hne
  have hle : Subgroup.normalClosure ({w} : Set (FreeGroup ι)) ≤ (FreeGroup.lift (σ ℓ)).ker :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.2 (MonoidHom.mem_ker.2 hw1))
  rw [← hℓ]
  exact MonoidHom.mem_ker.1 (hle hr)

end MarkedLimits

/-! ## The root `e_12(1)` -/

/-- The pair `(1, 2)` (zero-indexed `(0, 1)`) of distinct indices in rank `n ≥ 3`. -/
def root12 (n : ℕ) (hn : 3 ≤ n) : {p : Fin n × Fin n // p.1 ≠ p.2} :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), fun h => Nat.zero_ne_one (congrArg Fin.val h)⟩

/-- The elementary matrix `e_12(1) ∈ EL_n(R)`. -/
noncomputable def unitRoot12 (n : ℕ) (hn : 3 ≤ n) (R : Type*) [Ring R] :
    ↥(elementaryGroup (Fin n) R) :=
  ⟨elementaryUnit (root12 n hn).1.1 (root12 n hn).1.2 (root12 n hn).2 1, elementaryUnit_mem _ _ _ _⟩

/-- The marking index of `e_12(s)` with `s = 1 ∈ S`. -/
def index12 (n : ℕ) (hn : 3 ≤ n) {R : Type*} [Ring R] (S : Finset R) (hS1 : (1 : R) ∈ S) :
    MarkingIndex n S :=
  (root12 n hn, ⟨1, hS1⟩)

/-- `e_12(1) ≠ 1` over a nontrivial ring. -/
theorem unitRoot12_ne_one (n : ℕ) (hn : 3 ≤ n) (R : Type*) [Ring R] [Nontrivial R] :
    unitRoot12 n hn R ≠ 1 := by
  intro h
  have h' : elementaryUnit (root12 n hn).1.1 (root12 n hn).1.2 (root12 n hn).2 (1 : R) =
      elementaryUnit (root12 n hn).1.1 (root12 n hn).1.2 (root12 n hn).2 0 := by
    rw [elementaryUnit_zero]
    exact congrArg Subtype.val h
  exact one_ne_zero (elementaryUnit_injective _ _ _ h')

theorem lift_elementaryMarking_index12 (n : ℕ) (hn : 3 ≤ n) {R : Type*} [Ring R] (S : Finset R)
    (hS1 : (1 : R) ∈ S) :
    FreeGroup.lift (elementaryMarking n S) (FreeGroup.of (index12 n hn S hS1)) =
      unitRoot12 n hn R := by
  rw [FreeGroup.lift_apply_of]
  rfl

/-- The generator `e_12(1)` maps to the transvection `e_12(I)` in every model. -/
theorem lift_matricialMarking_index12 (n : ℕ) (hn : 3 ≤ n) {R : Type*} [Ring R] (S : Finset R)
    (hS1 : (1 : R) ∈ S) (N : ℕ → ℕ) (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (h1 : ∀ k, φ k 1 = 1) (k : ℕ) :
    FreeGroup.lift (matricialMarking n S N φ k) (FreeGroup.of (index12 n hn S hS1)) =
      unitRoot12 n hn (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) := by
  rw [FreeGroup.lift_apply_of]
  apply Subtype.ext
  show elementaryUnit (root12 n hn).1.1 (root12 n hn).1.2 (root12 n hn).2 (φ k 1) =
    elementaryUnit (root12 n hn).1.1 (root12 n hn).1.2 (root12 n hn).2 1
  rw [h1 k]

/-- If the orders `f (N k)` tend to infinity, then so do the sizes `N k`. -/
theorem tendsto_atTop_of_tendsto_card_comp {f N : ℕ → ℕ}
    (hcard : Tendsto (fun k => f (N k)) atTop atTop) : Tendsto N atTop atTop := by
  refine Filter.tendsto_atTop.2 fun B => ?_
  refine (Filter.tendsto_atTop.1 hcard ((Finset.range B).sup f + 1)).mono fun k hk => ?_
  by_contra hB
  have hle : f (N k) ≤ (Finset.range B).sup f :=
    Finset.le_sup (Finset.mem_range.2 (not_le.1 hB))
  exact lt_irrefl _ (lt_of_lt_of_le (Nat.lt_succ_of_le hle) hk)

/-! ## The endpoints -/

/-- **tex 333–334**: for `G = EL_n(R)` as in `thm:general` and a word `w` in the generators
`e_ij(s)` that is nontrivial in `G` (tex 332–333), `e_12(1)` lies in the normal closure of `w` and is
a product of conjugates of `w` and `w⁻¹` in `G`. -/
theorem manuscriptSentence_unitIsProductOfConjugates (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) (w : FreeGroup (MarkingIndex n S))
    (hw : FreeGroup.lift (elementaryMarking n S) w ≠ 1) :
    unitRoot12 n hn (ClopenGroupCrossedProduct Λ Z (ZMod 2)) ∈
        Subgroup.normalClosure ({FreeGroup.lift (elementaryMarking n S) w} :
          Set ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))) ∧
      ∃ l : List ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))),
        (∀ y ∈ l, IsConj (FreeGroup.lift (elementaryMarking n S) w) y ∨
          IsConj (FreeGroup.lift (elementaryMarking n S) w)⁻¹ y) ∧
        l.prod = unitRoot12 n hn (ClopenGroupCrossedProduct Λ Z (ZMod 2)) := by
  obtain ⟨-, -, hG, -⟩ := printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  have hmem := mem_normalClosure_of_isSimpleGroup hG hw
    (unitRoot12 n hn (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
  exact ⟨hmem, exists_list_isConj_of_mem_normalClosure hmem⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.FiniteModelsBrown.manuscriptSentence_unitIsProductOfConjugates

/-- **tex 334–336**: for `G` as in `thm:general` and a word `w` nontrivial in `G`, the relation
expressing `e_12(1)` through conjugates of `w^{±1}` (a word `r` in the normal closure of `w` with
value `e_12(1)` in `G`) holds in `EL_n(M_{N_k}(F₂)) = SL_{nN_k}(F₂)` for large `k`; there the
generator `e_12(1)` maps to the transvection `e_12(I) ≠ I`; and `w` is nontrivial in
`SL_{nN_k}(F₂)` for large `k`. -/
theorem manuscriptSentence_relationTransfersToSpecialLinear (Λ : Type) [Group Λ] [Group.FG Λ]
    (Z : Type) [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) (w : FreeGroup (MarkingIndex n S))
    (hw : FreeGroup.lift (elementaryMarking n S) w ≠ 1) :
    (∃ r ∈ Subgroup.normalClosure ({w} : Set (FreeGroup (MarkingIndex n S))),
        FreeGroup.lift (elementaryMarking n S) r =
          unitRoot12 n hn (ClopenGroupCrossedProduct Λ Z (ZMod 2)) ∧
        ∀ᶠ k in atTop, FreeGroup.lift (matricialMarking n S N φ k) r =
          unitRoot12 n hn (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) ∧
      (∀ k, FreeGroup.lift (matricialMarking n S N φ k) (FreeGroup.of (index12 n hn S hS1)) =
        unitRoot12 n hn (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) ∧
      (∀ k, unitRoot12 n hn (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) ≠ 1) ∧
      (∀ k,
        (elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).map
            (elementaryBlockUnitEquiv (ι := Fin n) (κ := Fin (N k)) (R := ZMod 2)).toMonoidHom =
          (AlgebraicK.detUnits (ι := Fin n × Fin (N k)) (k := ZMod 2)).ker) ∧
      ∀ᶠ k in atTop, FreeGroup.lift (matricialMarking n S N φ k) w ≠ 1 := by
  obtain ⟨-, -, hG, -, hlim, -, hSL, -⟩ :=
    printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  obtain ⟨hpos, h1, -, -⟩ := hφ
  have hmem := mem_normalClosure_of_isSimpleGroup hG hw
    (unitRoot12 n hn (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
  obtain ⟨r, hr, hrs⟩ := exists_word_mem_normalClosure hlim hmem
  have hσ12 := lift_matricialMarking_index12 n hn S hS1 N φ h1
  have hne : ∀ k, unitRoot12 n hn (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) ≠ 1 := fun k => by
    haveI : Nonempty (Fin (N k)) := ⟨⟨0, hpos k⟩⟩
    exact unitRoot12_ne_one n hn (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
  have hu : ∀ᶠ k in atTop,
      FreeGroup.lift (matricialMarking n S N φ k) (FreeGroup.of (index12 n hn S hS1)) ≠ 1 :=
    Filter.Eventually.of_forall fun k => by
      rw [hσ12 k]
      exact hne k
  obtain ⟨hrel, hwne⟩ := eventually_lift_ne_one_of_mem_normalClosure hlim hr
    (hrs.trans (lift_elementaryMarking_index12 n hn S hS1).symm) hu
  refine ⟨⟨r, hr, hrs, ?_⟩, hσ12, hne, hSL, hwne⟩
  filter_upwards [hrel] with k hk
  rw [hk, hσ12 k]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.FiniteModelsBrown.manuscriptSentence_relationTransfersToSpecialLinear

/-- **tex 336–338**: for `G` as in `thm:general`, the marked finite simple groups
`EL_n(M_{N_k}(F₂)) = SL_{nN_k}(F₂)` converge to `G`, so `G` is LEF (in both the textbook form and the
corpus form of the definition), and `N_k → ∞` because `G` is infinite (the orders of the models tend
to infinity as well). -/
theorem manuscriptSentence_markedLimitLEFSizesGrow (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) :
    IsMarkedLimit (elementaryMarking n S) (matricialMarking n S N φ) ∧
      (∀ k, IsSimpleGroup ↥(elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))) ∧
      (∀ k, Finite ↥(elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))) ∧
      (∀ k,
        (elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).map
            (elementaryBlockUnitEquiv (ι := Fin n) (κ := Fin (N k)) (R := ZMod 2)).toMonoidHom =
          (AlgebraicK.detUnits (ι := Fin n × Fin (N k)) (k := ZMod 2)).ker) ∧
      IsTextbookLEF ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      IsLEF ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      Tendsto (fun k =>
        Nat.card ↥(elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))) atTop atTop ∧
      Tendsto N atTop atTop := by
  obtain ⟨hInf, -, -, -, hlim, hsimple, hSL, -⟩ :=
    printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  have hfin : ∀ k, Finite ↥(elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) :=
    fun k => finite_elementaryGroup_matrix n (N k)
  haveI := hInf
  have hcard := tendsto_card_of_isMarkedLimit hfin hlim
  exact ⟨hlim, hsimple, hfin, hSL, isTextbookLEF_of_isMarkedLimit hfin hlim,
    isLEF_of_isMarkedLimit hfin hlim, hcard,
    tendsto_atTop_of_tendsto_card_comp
      (f := fun m => Nat.card ↥(elementaryGroup (Fin n) (Matrix (Fin m) (Fin m) (ZMod 2)))) hcard⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.FiniteModelsBrown.manuscriptSentence_markedLimitLEFSizesGrow

/-- **tex 338–342**: for `G` as in `thm:general`, `EL_n(𝒜)`, `𝒜 = F₂⟨τ_s : s ∈ S⟩`, has property (T)
(EJZ); the Cayley graphs of its finite quotients with orders tending to infinity, with respect to the
images of its generators `e_ij(1)`, `e_ij(τ_s)`, form a family of expanders (Margulis); the models
`EL_n(M_{N_k}(F₂))` are such quotients via `EL_n(ρ_k)`, carrying the generators `e_ij(τ_s)` to the
marking `e_ij(φ_k(s))`; so `G` is the limit of the `SL_{nN_k}(F₂)`, whose Cayley graphs form a family
of expanders. -/
theorem manuscriptSentence_expanderLimitFromPropertyT (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin n) (FreeAlgebra (ZMod 2) ↥S)) ∧
      (∀ (H : ℕ → Type) [∀ ℓ, Group (H ℓ)] [∀ ℓ, Finite (H ℓ)]
          (π : ∀ ℓ, ↥(elementaryGroup (Fin n) (FreeAlgebra (ZMod 2) ↥S)) →* H ℓ),
          (∀ ℓ, Function.Surjective (π ℓ)) →
          Tendsto (fun ℓ => Nat.card (H ℓ)) atTop atTop →
          IsExpanderFamily (fun ℓ (i : {p : Fin n × Fin n // p.1 ≠ p.2} × Option ↥S) =>
            π ℓ (elementaryLetterMarking n ↥S i))) ∧
      (∀ k, Function.Surjective (elementaryGroupMap (ι := Fin n) (rhoLetters S N φ k))) ∧
      (∀ (k : ℕ) (p : MarkingIndex n S), matricialMarking n S N φ k p =
        elementaryGroupMap (ι := Fin n) (rhoLetters S N φ k)
          (elementaryLetterMarking n ↥S (p.1, some p.2))) ∧
      IsExpanderFamily (matricialMarking n S N φ) ∧
      IsMarkedLimit (elementaryMarking n S) (matricialMarking n S N φ) ∧
      (∀ k,
        (elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).map
            (elementaryBlockUnitEquiv (ι := Fin n) (κ := Fin (N k)) (R := ZMod 2)).toMonoidHom =
          (AlgebraicK.detUnits (ι := Fin n × Fin (N k)) (k := ZMod 2)).ker) := by
  obtain ⟨-, -, -, -, hlim, -, hSL, hexp⟩ :=
    printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  obtain ⟨-, -, hgen, -⟩ := hφ
  have hT := hasKazhdanPropertyT_elementaryGroup_freeAlgebra ↥S n hn
  have hρ : ∀ k, Function.Surjective (rhoLetters S N φ k) := fun k y => by
    obtain ⟨x, hx⟩ := lift_surjective_of_closure S (φ k) (hgen k) y
    exact ⟨x, hx⟩
  refine ⟨hT, ?_, fun k => elementaryGroupMap_surjective_of_surjective _ (hρ k), ?_, hexp, hlim,
    hSL⟩
  · intro H _ _ π hπ hcard
    exact isExpanderFamily_of_hasKazhdanPropertyT_quotients hT (elementaryLetterMarking n ↥S)
      (closure_range_elementaryLetterMarking n hn ↥S) π hπ hcard
  · intro k p
    apply Subtype.ext
    show elementaryUnit p.1.1.1 p.1.1.2 p.1.2
        (φ k (p.2 : ClopenGroupCrossedProduct Λ Z (ZMod 2))) =
      elementaryMatrixUnitMap (rhoLetters S N φ k)
        (elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (FreeAlgebra.ι (ZMod 2) p.2))
    rw [elementaryMatrixUnitMap_elementaryUnit, rhoLetters_ι]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.FiniteModelsBrown.manuscriptSentence_expanderLimitFromPropertyT

end FiniteModelsBrown
end SimpleKazhdanSofic
end GroupApproximation
