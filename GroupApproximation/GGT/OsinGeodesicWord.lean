import GroupApproximation.GGT.OsinPenetration

/-!
# Every pair is joined by a geodesic word over `RelLetter`

`GGT/OsinPenetration.lean` left `ExistsGeodesicWord` named rather than proved,
because lifting a realising `List G` to a `List (RelLetter G Λ)` is a choice,
for each letter, of which side of `X ⊔ ℋ` it is read from.  It is bookkeeping
about the letter type rather than about Osin's geometry, and it blocks every use
of `sepCard`, so it gets its own module.

`WordMetric.exists_isWord_length_eq` supplies a list of group elements of length
`|f⁻¹g|`, each lying in `X ∪ ⋃ H λ`.  `exists_relWord` lifts it: induction on the
list, and at each step the membership is a disjunction --- a base letter or a
letter of some `H λ` --- so the two constructors of `RelLetter` cover it and the
existential absorbs the choice of `λ`.  No `Classical.choice` appears: an
induction that produces an existential never has to name the branch it took.

The point of the lift is that `RelLetter` keeps the union disjoint.  The same
group element can be both a letter of `X` and a letter of some `H λ`, and those
label *different* edges of `Γ(G, X ⊔ ℋ)`; a bare `List G` has forgotten which
edge was traversed, which is exactly the information a component --- hence a
penetration, hence a separating coset --- is about.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Lifting a word of group elements to a word of relative letters.**  Each
letter of `X ∪ ⋃ H λ` is a `base` letter or a `comp` letter, and the induction
carries the choice inside the existential. -/
theorem exists_relWord (D : RelGenSet G Λ) :
    ∀ l : List G, (∀ x ∈ l, x ∈ D.alphabet.carrier) →
      ∃ w : List (RelLetter G Λ), (∀ a ∈ w, D.IsLetter a) ∧
        RelLetter.listVal w = l.prod ∧ w.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨[], by simp, RelLetter.listVal_nil, rfl⟩
  | cons x t ih =>
      intro hmem
      obtain ⟨w, hw1, hw2, hw3⟩ :=
        ih (fun y hy => hmem y (List.mem_cons_of_mem _ hy))
      have hx : x ∈ D.alphabet.carrier := hmem x List.mem_cons_self
      rcases hx with hx | hx
      · refine ⟨RelLetter.base x :: w, ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.1 ha with rfl | ha'
          · exact hx
          · exact hw1 a ha'
        · rw [listVal_cons, hw2, List.prod_cons]
          rfl
        · simp [hw3]
      · rw [Set.mem_iUnion] at hx
        obtain ⟨lam, hlam⟩ := hx
        refine ⟨RelLetter.comp lam x :: w, ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.1 ha with rfl | ha'
          · exact hlam
          · exact hw1 a ha'
        · rw [listVal_cons, hw2, List.prod_cons]
          rfl
        · simp [hw3]

/-- **`ExistsGeodesicWord` holds, for every relative generating set.**  The
realising list of `WordMetric.exists_isWord_length_eq` lifted through
`exists_relWord`; its length is `|f⁻¹g|`, which is `d_{X⊔ℋ}(f,g)` by definition
of `wordDist`. -/
theorem existsGeodesicWord (D : RelGenSet G Λ) : ExistsGeodesicWord D := by
  intro f g
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq D.symmetricGenerating (f⁻¹ * g)
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_relWord D l hl.letters
  refine ⟨w, hw1, ?_, ?_⟩
  · rw [hw2, hl.prod_eq]
    group
  · rw [hw3, hlen, wordDist]
    rfl

/-- `S(f,g;D)` is finite for every pair, with no geodesic supplied by the
caller: `existsGeodesicWord` produces one.  This is what makes `sepCard`
usable. -/
theorem sepSet_finite' {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ}
    (h48 : LemmaFourEight D lam Dc) (f g : G) :
    (sepSet D lam Dc f g).Finite := by
  obtain ⟨w, hw⟩ := existsGeodesicWord D f g
  exact sepSet_finite h48 f g hw

end OsinComponents
end GGT
end GroupApproximation
