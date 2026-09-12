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
(`listVal_mem_boundedProducts_of_cosetLettersAt`); when one letter is exceptional, the
value is either such a product, or, when the exceptional letter is itself read at a
vertex of `H_λ`, a product with a copy of that letter in the middle
(`face_relation_split`).

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
  fun i hi hc _ => h _ (List.getElem_mem hi) hc

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
  rw [mul_assoc] at hv
  rwa [← mul_assoc, e] at hv

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
    rw [List.take_append, List.take_of_length_le hle, RelWord.listVal_append, ← mul_assoc]
      at hvert
    exact hv (i - u.length) _ hc hvert

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
          (by rw [e, RelWord.listVal_cons, ← mul_assoc]; exact hvert)
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

/-- The coset letters of a word with one letter split off. -/
theorem cosetLetters_split {D : GGT.RelGenSet G Lambda} {lam : Lambda} {A : Set G}
    {u₁ u₂ : List (GGT.RelLetter G Lambda)} {a : GGT.RelLetter G Lambda}
    (h₁ : CosetLettersAt D lam A 1 1 u₁)
    (h₂ : CosetLettersAt D lam A 1 (GGT.RelLetter.listVal u₁ * a.val) u₂) :
    ∀ (i : ℕ) (hi : i < (u₁ ++ a :: u₂).length), i ≠ u₁.length →
      GGT.RelLetter.IsCompOf lam (u₁ ++ a :: u₂)[i] →
        GGT.OsinComponents.vertex 1 (u₁ ++ a :: u₂) i ∈ D.fam lam →
          (u₁ ++ a :: u₂)[i].val ∈ A := by
  intro i hi hne hc hvert
  rw [vertex_eq_mul_listVal_take, one_mul] at hvert
  by_cases hiu : i < u₁.length
  · rw [List.getElem_append_left hiu] at hc ⊢
    rw [List.take_append_of_le_length hiu.le] at hvert
    exact h₁ i hiu hc (by rw [inv_one, one_mul, one_mul]; exact hvert)
  · have hle : u₁.length + 1 ≤ i := by omega
    have hsucc : i - u₁.length = (i - u₁.length - 1) + 1 := by omega
    have hget : (u₁ ++ a :: u₂)[i] = u₂[i - u₁.length - 1]'(by simp at hi; omega) := by
      rw [List.getElem_append_right (by omega)]
      simp only [hsucc, List.getElem_cons_succ]
    rw [hget] at hc ⊢
    have htake : (u₁ ++ a :: u₂).take i = u₁ ++ a :: u₂.take (i - u₁.length - 1) := by
      rw [List.take_append, List.take_of_length_le (by omega), hsucc, List.take_succ_cons]
    rw [htake, RelWord.listVal_append, RelWord.listVal_cons] at hvert
    apply h₂ (i - u₁.length - 1) _ hc
    rw [inv_one, one_mul, mul_assoc, mul_assoc]
    exact hvert

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
  set rest := u₁ ++ a :: u₂ with hrest_def
  have hj : u₁.length < rest.length := by rw [hrest_def]; simp
  have hgetj : rest[u₁.length] = a := by
    rw [hrest_def, List.getElem_append_right le_rfl]
    simp
  have hvertj : GGT.OsinComponents.vertex 1 rest u₁.length = GGT.RelLetter.listVal u₁ := by
    rw [hrest_def, GGT.RelHyp.cosetPieces_vertex_append, one_mul]
  obtain ⟨pieces, hprod, hinr, hinl, hall, hpair, hlen⟩ :=
    GGT.RelHyp.exists_cosetPieces D lam rest hletters hval
  have hsplit := cosetLetters_split h₁ h₂
  have hclass : ∀ p ∈ pieces, p ≠ Sum.inl u₁.length →
      GGT.RelHyp.pieceVal rest p ∈ A ∪ D.relBall lam rest.length := by
    intro p hp hne
    cases p with
    | inl i =>
        obtain ⟨hi, hcomp, hvert⟩ := hinl i hp
        left
        rw [pieceVal_inl hi]
        exact hsplit i hi (fun h => hne (by rw [h])) hcomp hvert
    | inr g =>
        right
        exact hinr g hp
  constructor
  · intro hnot
    have hmem : Sum.inl u₁.length ∉ pieces := by
      intro hmem
      obtain ⟨hi, hcomp, hvert⟩ := hinl _ hmem
      apply hnot
      refine ⟨?_, ?_⟩
      · have e : rest.get ⟨u₁.length, hi⟩ = a := hgetj
        rw [← e]
        exact hcomp
      · rw [← hvertj]
        exact hvert
    refine ⟨pieces.map (GGT.RelHyp.pieceVal rest), by rw [List.length_map]; exact hlen, ?_,
      hprod⟩
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact hclass p hp (by rintro rfl; exact hmem hp)
  · rintro ⟨hcomp, hvert⟩
    have hmem : Sum.inl u₁.length ∈ pieces :=
      hall u₁.length hj (by rw [show rest.get ⟨u₁.length, hj⟩ = a from hgetj]; exact hcomp)
        (by rw [hvertj]; exact hvert)
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
    have hfm : ((s ++ Sum.inl u₁.length :: t).filterMap Sum.getLeft?) =
        s.filterMap Sum.getLeft? ++ u₁.length :: t.filterMap Sum.getLeft? := by
      simp [List.filterMap_append]
    rw [hfm, List.pairwise_append, List.pairwise_cons] at hpair
    obtain ⟨-, ⟨hjt, -⟩, hst⟩ := hpair
    have hs : ∀ p ∈ s, p ≠ Sum.inl u₁.length := by
      rintro p hp rfl
      have hmemi : u₁.length ∈ s.filterMap Sum.getLeft? := List.mem_filterMap.mpr ⟨_, hp, rfl⟩
      exact Nat.lt_irrefl _ (hst _ hmemi _ (List.mem_cons_self ..))
    have ht : ∀ p ∈ t, p ≠ Sum.inl u₁.length := by
      rintro p hp rfl
      have hmemi : u₁.length ∈ t.filterMap Sum.getLeft? := List.mem_filterMap.mpr ⟨_, hp, rfl⟩
      exact Nat.lt_irrefl _ (hjt _ hmemi)
    simp only [List.length_append, List.length_cons] at hlen
    refine ⟨(s.map (GGT.RelHyp.pieceVal rest)).prod, (t.map (GGT.RelHyp.pieceVal rest)).prod,
      ⟨s.map (GGT.RelHyp.pieceVal rest), by rw [List.length_map]; omega, ?_, rfl⟩,
      ⟨t.map (GGT.RelHyp.pieceVal rest), by rw [List.length_map]; omega, ?_, rfl⟩, ?_⟩
    · intro z hz
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
      exact hclass p (List.mem_append_left _ hp) (hs p hp)
    · intro z hz
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
      exact hclass p (List.mem_append_right _ (List.mem_cons_of_mem _ hp)) (ht p hp)
    · rw [← hprod, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
        pieceVal_inl hj, hgetj, mul_assoc]

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.mul_mem_boundedProducts
#audit_axioms GroupApproximation.HullSC.inv_mem_boundedProducts
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.of_rep
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.translate
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.append
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv
#audit_axioms GroupApproximation.HullSC.listVal_mem_boundedProducts_of_cosetLettersAt
#audit_axioms GroupApproximation.HullSC.cosetLetters_split
#audit_axioms GroupApproximation.HullSC.face_relation_split
