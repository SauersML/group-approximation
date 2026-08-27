import GroupApproximation.PropertyTT.CoordinateBlocks
import GroupApproximation.PropertyTT.Basic
import GroupApproximation.Leavitt.ElementaryNoFiniteQuotients

/-!
# Uniform coordinate-block generation under single-sandwich division

This is the reusable algebraic theorem behind the Leavitt application.  Over
any nontrivial ring in which every nonzero element `a` admits `x * a * y = 1`,
every finite-rank general linear group is a bounded product of elementary
transvections and one fixed coordinate-block subgroup.  The proof is the
explicit one-stage elimination; no stable-range or `K₁` theorem is used.

For unital simple rings, the sandwich hypothesis is the standard algebraic
characterization used by Ara--Goodearl--Pardo for purely infinite simplicity
(with division rings excluded separately).  The bounded-product theorem below
is the formal contribution of this file; that literature result is credited for
identifying the natural class of examples.
-/

namespace GroupApproximation

universe v

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-- Elementary transvections together with the coordinate block omitting `j`.
This is the precise bounded generating set used by the analytic argument. -/
def coordinateBlockOrRoot (j : ι) : Set (Matrix ι ι R)ˣ :=
  {x | IsElementaryUnit x ∨ x ∈ coordinateBlock R j}

/-- The inverse of a single elementary transvection is elementary. -/
theorem IsElementaryUnit.inv {x : (Matrix ι ι R)ˣ}
    (hx : IsElementaryUnit x) : IsElementaryUnit x⁻¹ := by
  obtain ⟨i, j, hij, a, rfl⟩ := hx
  refine ⟨i, j, hij, -a, ?_⟩
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [elementaryUnit_mul]
  simp [elementaryUnit_zero]

/-- The reversed pointwise-inverse word represents the inverse product. -/
def elementaryInverseWord {G : Type*} [Group G] (l : List G) : List G :=
  (l.map Inv.inv).reverse

@[simp] theorem length_elementaryInverseWord {G : Type*} [Group G]
    (l : List G) : (elementaryInverseWord l).length = l.length := by
  simp [elementaryInverseWord]

theorem prod_elementaryInverseWord {G : Type*} [Group G] (l : List G) :
    (elementaryInverseWord l).prod = l.prod⁻¹ := by
  exact (List.prod_inv_reverse l).symm

theorem elementaryInverseWord_isElementary
    (l : List (Matrix ι ι R)ˣ)
    (hl : ∀ x ∈ l, IsElementaryUnit x) :
    ∀ x ∈ elementaryInverseWord l, IsElementaryUnit x := by
  intro x hx
  rw [elementaryInverseWord, List.mem_reverse] at hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
  subst x
  exact (hl y hy).inv

theorem rightClearFactors_elementary (j : ι) (f : ι → R)
    (l : List {k : ι // k ≠ j}) :
    ∀ x ∈ rightClearFactors j f l, IsElementaryUnit x := by
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact ⟨j, (k : ι), k.property.symm, f k, rfl⟩

theorem leftClearFactors_elementary (j : ι) (f : ι → R)
    (l : List {k : ι // k ≠ j}) :
    ∀ x ∈ leftClearFactors j f l, IsElementaryUnit x := by
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact ⟨(k : ι), j, k.property, f k, rfl⟩

@[simp] theorem length_otherIndices (j : ι) :
    (otherIndices j).length = Fintype.card ι - 1 := by
  simp [otherIndices]

/-- **Uniform strong-division bounded generation.**  A rank with at least
two coordinates has width at most `2 * card ι + 2` with respect to the
elementary roots and one coordinate copy of `GL`. -/
theorem boundedProduct_coordinateBlockOrRoot [Nontrivial R] [Nontrivial ι]
    (hdiv : HasSingleSandwichDivision R) (j : ι) :
    IsBoundedProduct (Matrix ι ι R)ˣ (coordinateBlockOrRoot j)
      (2 * Fintype.card ι + 2) := by
  intro A
  obtain ⟨i, hij⟩ := exists_ne j
  obtain ⟨E, F, hjj, l, r, hl, hr, hlelem, hrelem, hlE, hrF⟩ :=
    exists_three_move_diagonal_pivot hdiv A i j hij
  let B : (Matrix ι ι R)ˣ := E * A * F
  let t : List (Matrix ι ι R)ˣ :=
    rightClearFactors j (fun k ↦ -(B : Matrix ι ι R) j k)
      (otherIndices j)
  let T : (Matrix ι ι R)ˣ := t.prod
  let C : (Matrix ι ι R)ˣ := B * T
  have hCrow : ∀ c, (C : Matrix ι ι R) j c =
      if j = c then 1 else 0 := by
    intro c
    dsimp [C, T, t]
    rw [← Units.val_mul]
    exact rightClearFactors_clear_row
      (B : Matrix ι ι R) j (by simpa [B, mul_assoc] using hjj) c
  let s : List (Matrix ι ι R)ˣ :=
    leftClearFactors j (fun k ↦ -(C : Matrix ι ι R) k j)
      (otherIndices j)
  let S : (Matrix ι ι R)ˣ := s.prod
  let D : (Matrix ι ι R)ˣ := S * C
  have hD : D ∈ coordinateBlock R j := by
    dsimp only [D, S, s]
    exact leftClearFactors_make_coordinateBlock C j hCrow
  let w : List (Matrix ι ι R)ˣ :=
    elementaryInverseWord l ++ elementaryInverseWord s ++ [D] ++
      elementaryInverseWord t ++ elementaryInverseWord r
  refine ⟨w, ?_, ?_, ?_⟩
  · have hslen : s.length = Fintype.card ι - 1 := by
      simp [s, leftClearFactors]
    have htlen : t.length = Fintype.card ι - 1 := by
      simp [t, rightClearFactors]
    have hcard : 2 ≤ Fintype.card ι :=
      Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    dsimp [w]
    simp only [List.length_append, length_elementaryInverseWord, List.length_cons,
      List.length_nil]
    omega
  ·
    have hselem : ∀ y ∈ s, IsElementaryUnit y := by
      dsimp [s]
      exact leftClearFactors_elementary j _ _
    have htelem : ∀ y ∈ t, IsElementaryUnit y := by
      dsimp [t]
      exact rightClearFactors_elementary j _ _
    dsimp [w]
    have hall : ∀ x ∈ elementaryInverseWord l ++
        (elementaryInverseWord s ++
          ([D] ++ (elementaryInverseWord t ++ elementaryInverseWord r))),
        x ∈ coordinateBlockOrRoot j := by
      refine List.forall_mem_append.mpr ⟨?_, ?_⟩
      · intro x hx
        exact Or.inl (elementaryInverseWord_isElementary l hlelem x hx)
      refine List.forall_mem_append.mpr ⟨?_, ?_⟩
      · intro x hx
        exact Or.inl (elementaryInverseWord_isElementary s hselem x hx)
      refine List.forall_mem_append.mpr ⟨?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst x
        exact Or.inr hD
      refine List.forall_mem_append.mpr ⟨?_, ?_⟩
      · intro x hx
        exact Or.inl (elementaryInverseWord_isElementary t htelem x hx)
      · intro x hx
        exact Or.inl (elementaryInverseWord_isElementary r hrelem x hx)
    simpa only [List.append_assoc] using hall
  · dsimp [w]
    simp only [List.prod_append, prod_elementaryInverseWord, List.prod_cons,
      List.prod_nil, mul_one, hlE, hrF]
    dsimp [D, S, C, T, B]
    group

/-! ## Analytic globalization over the natural ring class -/

/-- **General coordinate-block `(TT)/T` theorem.**  Strong sandwich division
supplies bounded generation.  If the ambient general linear group has relative
`(TT)/T` with respect to each of its finitely many coordinate blocks, then it
has global `(TT)/T`.

The relative hypotheses are stated openly here: proving them is the analytic
Mimura--Ozawa input, logically independent of pure infiniteness.  In
particular this theorem does not mislabel a ring-theoretic hypothesis as an
analytic consequence. -/
theorem hasTTmodT_of_relative_coordinateBlocks_of_sandwich [Nontrivial R]
    (hcard : 3 ≤ Fintype.card ι)
    (hdiv : HasSingleSandwichDivision R)
    (hrel : ∀ j : ι,
      HasRelativeTTmodT.{_, v} (Matrix ι ι R)ˣ (coordinateBlock R j)) :
    HasTTmodT.{_, v} (Matrix ι ι R)ˣ := by
  letI : Nontrivial ι :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let j₀ : ι := Classical.choice inferInstance
  intro E _ _ _ rho hno b D hb
  have hblock : ∀ j : ι,
      IsNormBoundedOn b (coordinateBlock R j : Set (Matrix ι ι R)ˣ) := by
    intro j
    exact hrel j E rho hno b D hb
  have hset : IsNormBoundedOn b (coordinateBlockOrRoot j₀) := by
    apply isNormBoundedOn_of_finite_cover Finset.univ
      (coordinateBlockOrRoot j₀)
      (fun j : ι ↦ (coordinateBlock R j : Set (Matrix ι ι R)ˣ))
    · intro x hx
      rcases hx with hx | hx
      · obtain ⟨i, j, hij, a, rfl⟩ := hx
        obtain ⟨q, hqi, hqj⟩ := exists_third_index hcard i j
        exact ⟨q, Finset.mem_univ q,
          elementaryUnit_mem_coordinateBlock_of_ne q i j hij hqi hqj a⟩
      · exact ⟨j₀, Finset.mem_univ j₀, hx⟩
    · intro j _
      exact hblock j
  exact isNormBoundedOn_univ_of_boundedProduct hb hset
    (boundedProduct_coordinateBlockOrRoot hdiv j₀)

end GroupApproximation
