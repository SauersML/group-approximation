import GroupApproximation.GGT.HullSCLemma51EmbeddedProducer
import GroupApproximation.GGT.HullSCLemma51LetterWords
import GroupApproximation.GGT.RelativeCosetPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The face relation at a coset

A word over the letters of a relative generating set whose value lies in `H_λ`, read
from `1`, is cut at the vertices of `H_λ` into coset pieces
(`GGT.RelHyp.exists_cosetPieces`): peripheral letters of index `λ` read at those
vertices, and avoiding stretches, whose values lie in a relative ball.  So when the
peripheral letters read at vertices of `H_λ` all have values in a set `A`, the value of
the word is a bounded product of elements of `A` and of the relative ball
(`listVal_mem_boundedProducts_of_cosetLettersAt`), from any base point
(`listVal_mem_boundedProducts_of_cosetLettersAt_from`).

`CosetLettersAt D λ A c x u` says that every peripheral letter of index `λ` of the word
`u` read from `x`, read at a vertex of the coset `c H_λ`, has value in `A`.  It is
assembled along concatenations (`CosetLettersAt.append`), for single letters, and for
words read backwards with inverse letters (`cosetLettersAt_respellInv`), and it is
invariant under left translation of the representative and the base together.  These
are the face relations of the letter pullback of Osin's Lemma 5.1.
-/

namespace GroupApproximation
namespace HullSC

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## Bounded products -/

theorem one_mem_boundedProducts (A : Set G) (N : ℕ) : (1 : G) ∈ boundedProducts A N :=
  ⟨[], Nat.zero_le _, by simp, rfl⟩

theorem boundedProducts_mono {A B : Set G} (hAB : A ⊆ B) {N M : ℕ} (hNM : N ≤ M) :
    boundedProducts A N ⊆ boundedProducts B M := by
  rintro x ⟨l, hl, hmem, rfl⟩
  exact ⟨l, le_trans hl hNM, fun y hy => hAB (hmem y hy), rfl⟩

theorem mem_boundedProducts_of_mem {A : Set G} {x : G} (hx : x ∈ A) {N : ℕ} (hN : 1 ≤ N) :
    x ∈ boundedProducts A N :=
  ⟨[x], by simpa using hN, by simpa using hx, by simp⟩

theorem mul_mem_boundedProducts {A : Set G} {x y : G} {N M : ℕ}
    (hx : x ∈ boundedProducts A N) (hy : y ∈ boundedProducts A M) :
    x * y ∈ boundedProducts A (N + M) := by
  obtain ⟨l₁, hl₁, hm₁, rfl⟩ := hx
  obtain ⟨l₂, hl₂, hm₂, rfl⟩ := hy
  refine ⟨l₁ ++ l₂, by rw [List.length_append]; omega, ?_, List.prod_append⟩
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hm₁ z hz
  · exact hm₂ z hz

theorem inv_mem_boundedProducts {A : Set G} (hA : ∀ x ∈ A, x⁻¹ ∈ A) {x : G} {N : ℕ}
    (hx : x ∈ boundedProducts A N) : x⁻¹ ∈ boundedProducts A N := by
  obtain ⟨l, hl, hm, rfl⟩ := hx
  refine ⟨(l.map fun y => y⁻¹).reverse, by simpa using hl, ?_, (List.prod_inv_reverse l).symm⟩
  intro z hz
  simp only [List.mem_reverse, List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hA y (hm y hy)

/-! ## Peripheral letters read at a coset -/

/-- **Every peripheral letter of index `λ` read at a vertex of the coset `c H_λ` has
value in `A`**, for the word `u` read from `x`. -/
def CosetLettersAt (D : GGT.RelGenSet G Lambda) (lam : Lambda) (A : Set G) (c x : G)
    (u : List (GGT.RelLetter G Lambda)) : Prop :=
  ∀ (i : ℕ) (hi : i < u.length), GGT.RelLetter.IsCompOf lam u[i] →
    c⁻¹ * (x * GGT.RelLetter.listVal (u.take i)) ∈ D.fam lam → u[i].val ∈ A

theorem cosetLettersAt_nil (D : GGT.RelGenSet G Lambda) (lam : Lambda) (A : Set G) (c x : G) :
    CosetLettersAt D lam A c x [] := fun i hi => absurd hi (by simp)

theorem CosetLettersAt.mono {D : GGT.RelGenSet G Lambda} {lam : Lambda} {A B : Set G} {c x : G}
    {u : List (GGT.RelLetter G Lambda)} (h : CosetLettersAt D lam A c x u) (hAB : A ⊆ B) :
    CosetLettersAt D lam B c x u :=
  fun i hi hc hv => hAB (h i hi hc hv)

/-- A word all of whose peripheral letters of index `λ` have values in `A`. -/
theorem cosetLettersAt_of_forall {D : GGT.RelGenSet G Lambda} {lam : Lambda} {A : Set G}
    (c x : G) {u : List (GGT.RelLetter G Lambda)}
    (h : ∀ a ∈ u, GGT.RelLetter.IsCompOf lam a → a.val ∈ A) : CosetLettersAt D lam A c x u :=
  fun _ hi hc _ => h _ (List.getElem_mem hi) hc

/-- The representative may move inside its coset. -/
theorem CosetLettersAt.of_rep {D : GGT.RelGenSet G Lambda} {lam : Lambda} {A : Set G}
    {c c' x : G} {u : List (GGT.RelLetter G Lambda)} (h : CosetLettersAt D lam A c x u)
    (hcc : c'⁻¹ * c ∈ D.fam lam) : CosetLettersAt D lam A c' x u := by
  intro i hi hc hv
  apply h i hi hc
  have e : c⁻¹ * (x * GGT.RelLetter.listVal (u.take i)) =
      (c'⁻¹ * c)⁻¹ * (c'⁻¹ * (x * GGT.RelLetter.listVal (u.take i))) := by group
  rw [e]
  exact (D.fam lam).mul_mem ((D.fam lam).inv_mem hcc) hv

/-- Left translation of the representative and the base together. -/
theorem CosetLettersAt.translate {D : GGT.RelGenSet G Lambda} {lam : Lambda} {A : Set G}
    {c x : G} {u : List (GGT.RelLetter G Lambda)} (y : G) (h : CosetLettersAt D lam A c x u) :
    CosetLettersAt D lam A (y * c) (y * x) u := by
  intro i hi hc hv
  apply h i hi hc
  have e : (y * c)⁻¹ * (y * x * GGT.RelLetter.listVal (u.take i)) =
      c⁻¹ * (x * GGT.RelLetter.listVal (u.take i)) := by group
  rwa [e] at hv

/-- Words read one after the other. -/
theorem CosetLettersAt.append {D : GGT.RelGenSet G Lambda} {lam : Lambda} {A : Set G} {c x : G}
    {u v : List (GGT.RelLetter G Lambda)} (hu : CosetLettersAt D lam A c x u)
    (hv : CosetLettersAt D lam A c (x * GGT.RelLetter.listVal u) v) :
    CosetLettersAt D lam A c x (u ++ v) := by
  intro i hi hc hvert
  by_cases hiu : i < u.length
  · rw [List.getElem_append_left hiu] at hc ⊢
    rw [List.take_append_of_le_length hiu.le] at hvert
    exact hu i hiu hc hvert
  · have hle : u.length ≤ i := not_lt.mp hiu
    rw [List.getElem_append_right hle] at hc ⊢
    rw [List.take_append, List.take_of_length_le hle, RelWord.listVal_append] at hvert
    exact hv (i - u.length) _ hc (by simpa only [mul_assoc] using hvert)

/-- A single letter. -/
theorem cosetLettersAt_singleton {D : GGT.RelGenSet G Lambda} {lam : Lambda} {A : Set G}
    {c x : G} {a : GGT.RelLetter G Lambda}
    (h : GGT.RelLetter.IsCompOf lam a → c⁻¹ * x ∈ D.fam lam → a.val ∈ A) :
    CosetLettersAt D lam A c x [a] := by
  intro i hi hc hvert
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  simp only [List.take_zero, GGT.RelLetter.listVal_nil, mul_one] at hvert
  exact h hc hvert

/-- The value of a peripheral letter of index `λ` lies in `H_λ`. -/
theorem val_mem_fam_of_isCompOf {D : GGT.RelGenSet G Lambda} {lam : Lambda}
    {a : GGT.RelLetter G Lambda} (ha : D.IsLetter a) (hc : GGT.RelLetter.IsCompOf lam a) :
    a.val ∈ D.fam lam := by
  cases a with
  | base x => exact False.elim hc
  | comp mu h =>
      have hmu : mu = lam := hc
      subst hmu
      exact ha

/-- **A word read backwards with inverse letters.**  Read from the endpoint `x · u` of
the forward reading, a peripheral letter of index `λ` read at a vertex of `c H_λ` comes
from a letter of `u` that is peripheral of index `λ`, or a base letter in `H_λ`, read
forwards at a vertex of `c H_λ`. -/
theorem cosetLettersAt_respellInv (D : GGT.RelGenSet G Lambda) (lam : Lambda) (A : Set G)
    (c : G) :
    ∀ (x : G) (u : List (GGT.RelLetter G Lambda)), (∀ a ∈ u, D.IsLetter a) →
      (∀ (k : ℕ) (hk : k < u.length),
        (GGT.RelLetter.IsCompOf lam u[k] ∨ ∃ y : G, u[k] = GGT.RelLetter.base y ∧ y ∈ D.fam lam) →
          c⁻¹ * (x * GGT.RelLetter.listVal (u.take k)) ∈ D.fam lam →
            (invLetter D u[k]).val ∈ A) →
        CosetLettersAt D lam A c (x * GGT.RelLetter.listVal u) (respellInv D u)
  | _, [], _, _ => cosetLettersAt_nil D lam A c _
  | x, a :: t, hletters, h => by
      rw [respellInv_cons]
      have ht : ∀ b ∈ t, D.IsLetter b := fun b hb => hletters b (List.mem_cons_of_mem _ hb)
      have hbase : x * GGT.RelLetter.listVal (a :: t) =
          (x * a.val) * GGT.RelLetter.listVal t := by
        rw [RelWord.listVal_cons, mul_assoc]
      rw [hbase]
      refine CosetLettersAt.append (cosetLettersAt_respellInv D lam A c (x * a.val) t ht ?_) ?_
      · intro k hk hc hvert
        have e : (a :: t).take (k + 1) = a :: t.take k := rfl
        exact h (k + 1) (by simp; omega) hc
          (by rw [e, RelWord.listVal_cons]; simpa only [mul_assoc] using hvert)
      · apply cosetLettersAt_singleton
        intro hc hvert
        rw [listVal_respellInv, mul_inv_cancel_right] at hvert
        have hsrc := isCompOf_invLetter D hc
        have hval : a.val ∈ D.fam lam := by
          rcases hsrc with hsrc | ⟨y, rfl, hy⟩
          · exact val_mem_fam_of_isCompOf (hletters a (List.mem_cons_self ..)) hsrc
          · exact hy
        have hx : c⁻¹ * (x * GGT.RelLetter.listVal ((a :: t).take 0)) ∈ D.fam lam := by
          have h' := (D.fam lam).mul_mem hvert ((D.fam lam).inv_mem hval)
          simpa [GGT.RelLetter.listVal_nil, mul_assoc] using h'
        exact h 0 (by simp) hsrc hx

/-! ## The face relation -/

/-- The value of an inl coset piece is the letter it names. -/
theorem pieceVal_inl {rest : List (GGT.RelLetter G Lambda)} {i : ℕ} (hi : i < rest.length) :
    GGT.RelHyp.pieceVal rest (Sum.inl i) = rest[i].val := by
  show (rest.getD i (GGT.RelLetter.base 1)).val = rest[i].val
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **The face relation.**  A word with value in `H_λ` whose peripheral letters read at
vertices of `H_λ` have values in `A` has value a bounded product of elements of `A` and of
the relative ball of its length. -/
theorem listVal_mem_boundedProducts_of_cosetLettersAt (D : GGT.RelGenSet G Lambda)
    (lam : Lambda) (A : Set G) {rest : List (GGT.RelLetter G Lambda)}
    (hrest : ∀ a ∈ rest, D.IsLetter a) (hval : GGT.RelLetter.listVal rest ∈ D.fam lam)
    (hA : CosetLettersAt D lam A 1 1 rest) :
    GGT.RelLetter.listVal rest ∈
      boundedProducts (A ∪ D.relBall lam rest.length) (rest.length + 1) := by
  obtain ⟨pieces, hprod, hinr, hinl, -, -, hlen⟩ :=
    GGT.RelHyp.exists_cosetPieces D lam rest hrest hval
  refine ⟨pieces.map (GGT.RelHyp.pieceVal rest), by rw [List.length_map]; exact hlen, ?_, hprod⟩
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  cases p with
  | inl i =>
      obtain ⟨hi, hcomp, hvert⟩ := hinl i hp
      left
      rw [pieceVal_inl hi]
      exact hA i hi hcomp (by rw [inv_one, one_mul, ← vertex_eq_mul_listVal_take]; exact hvert)
  | inr g =>
      right
      exact hinr g hp

/-- **The face relation from any base point.**  A word read from `x`, returning to the
coset `x H_λ`, whose peripheral letters read at vertices of `x H_λ` have values in `A`. -/
theorem listVal_mem_boundedProducts_of_cosetLettersAt_from (D : GGT.RelGenSet G Lambda)
    (lam : Lambda) (A : Set G) (x : G) {rest : List (GGT.RelLetter G Lambda)}
    (hrest : ∀ a ∈ rest, D.IsLetter a) (hval : GGT.RelLetter.listVal rest ∈ D.fam lam)
    (hA : CosetLettersAt D lam A x x rest) :
    GGT.RelLetter.listVal rest ∈
      boundedProducts (A ∪ D.relBall lam rest.length) (rest.length + 1) := by
  apply listVal_mem_boundedProducts_of_cosetLettersAt D lam A hrest hval
  have h := hA.translate x⁻¹
  rwa [inv_mul_cancel] at h

/-- Enlarging the radius and the length bound of bounded products. -/
theorem boundedProducts_relBall_mono (D : GGT.RelGenSet G Lambda) (lam : Lambda) (A : Set G)
    {m n N M : ℕ} (hmn : m ≤ n) (hNM : N ≤ M) :
    boundedProducts (A ∪ D.relBall lam m) N ⊆ boundedProducts (A ∪ D.relBall lam n) M :=
  boundedProducts_mono (Set.union_subset_union_right _
    (GGT.OsinComponents.relBall_mono_radius D lam hmn)) hNM

/-- **The face relation with one letter split off.**  If that letter is not read at a
vertex of `H_λ`, the value is a bounded product; if it is, the value is a bounded
product, the letter, and a bounded product. -/
theorem face_relation_split (D : GGT.RelGenSet G Lambda) (lam : Lambda) (A : Set G)
    {u₁ u₂ : List (GGT.RelLetter G Lambda)} {a : GGT.RelLetter G Lambda}
    (hletters : ∀ b ∈ u₁ ++ a :: u₂, D.IsLetter b)
    (hval : GGT.RelLetter.listVal (u₁ ++ a :: u₂) ∈ D.fam lam)
    (h₁ : CosetLettersAt D lam A 1 1 u₁)
    (h₂ : CosetLettersAt D lam A 1 (GGT.RelLetter.listVal u₁ * a.val) u₂) :
    (¬ (GGT.RelLetter.IsCompOf lam a ∧ GGT.RelLetter.listVal u₁ ∈ D.fam lam) →
        GGT.RelLetter.listVal (u₁ ++ a :: u₂) ∈
          boundedProducts (A ∪ D.relBall lam (u₁ ++ a :: u₂).length)
            ((u₁ ++ a :: u₂).length + 1)) ∧
      ((GGT.RelLetter.IsCompOf lam a ∧ GGT.RelLetter.listVal u₁ ∈ D.fam lam) →
        ∃ x y : G,
          x ∈ boundedProducts (A ∪ D.relBall lam (u₁ ++ a :: u₂).length)
            ((u₁ ++ a :: u₂).length + 1) ∧
          y ∈ boundedProducts (A ∪ D.relBall lam (u₁ ++ a :: u₂).length)
            ((u₁ ++ a :: u₂).length + 1) ∧
            GGT.RelLetter.listVal (u₁ ++ a :: u₂) = x * a.val * y) := by
  have hsplit : GGT.RelLetter.listVal (u₁ ++ a :: u₂) =
      GGT.RelLetter.listVal u₁ * a.val * GGT.RelLetter.listVal u₂ := by
    rw [RelWord.listVal_append, RelWord.listVal_cons, mul_assoc]
  have hlen₁ : u₁.length ≤ (u₁ ++ a :: u₂).length := by simp
  have hlen₂ : u₂.length ≤ (u₁ ++ a :: u₂).length := by simp; omega
  have hl₁ : ∀ b ∈ u₁, D.IsLetter b := fun b hb => hletters b (by simp [hb])
  have hl₂ : ∀ b ∈ u₂, D.IsLetter b := fun b hb => hletters b (by simp [hb])
  have ha : D.IsLetter a := hletters a (by simp)
  constructor
  · intro hnot
    apply listVal_mem_boundedProducts_of_cosetLettersAt D lam A hletters hval
    refine h₁.append (CosetLettersAt.append (cosetLettersAt_singleton ?_) ?_)
    · intro hc hv
      exact absurd ⟨hc, by simpa using hv⟩ hnot
    · simpa [RelWord.listVal_singleton] using h₂
  · rintro ⟨hc, hv⟩
    have haval : a.val ∈ D.fam lam := val_mem_fam_of_isCompOf ha hc
    have hv₂ : GGT.RelLetter.listVal u₂ ∈ D.fam lam := by
      have e : GGT.RelLetter.listVal u₂ =
          (GGT.RelLetter.listVal u₁ * a.val)⁻¹ * GGT.RelLetter.listVal (u₁ ++ a :: u₂) := by
        rw [hsplit]; group
      rw [e]
      exact (D.fam lam).mul_mem ((D.fam lam).inv_mem ((D.fam lam).mul_mem hv haval)) hval
    refine ⟨GGT.RelLetter.listVal u₁, GGT.RelLetter.listVal u₂, ?_, ?_, hsplit⟩
    · exact boundedProducts_relBall_mono D lam A hlen₁ (by omega)
        (listVal_mem_boundedProducts_of_cosetLettersAt D lam A hl₁ hv h₁)
    · refine boundedProducts_relBall_mono D lam A hlen₂ (by omega)
        (listVal_mem_boundedProducts_of_cosetLettersAt_from D lam A
          (GGT.RelLetter.listVal u₁ * a.val) hl₂ hv₂ (h₂.of_rep ?_))
      simpa using (D.fam lam).inv_mem ((D.fam lam).mul_mem hv haval)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.mul_mem_boundedProducts
#audit_axioms GroupApproximation.HullSC.inv_mem_boundedProducts
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.of_rep
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.translate
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.append
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv
#audit_axioms GroupApproximation.HullSC.listVal_mem_boundedProducts_of_cosetLettersAt
#audit_axioms GroupApproximation.HullSC.listVal_mem_boundedProducts_of_cosetLettersAt_from
#audit_axioms GroupApproximation.HullSC.face_relation_split
