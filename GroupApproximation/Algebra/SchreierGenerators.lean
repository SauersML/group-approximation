import GroupApproximation.Algebra.FiniteIndexTransversal
import GroupApproximation.Algebra.WordMetricComparison

/-!
# Schreier generators of a finite-index subgroup

Let `Λ ≤ Γ` have finite index, let `tr` be a right transversal
(`Algebra/FiniteIndexTransversal.lean`) and let `S` be a symmetric generating set
of `Γ`.  The **Schreier alphabet** is the set of cocycle values

```
    schreierSet tr S = { c · x · sec(c·x)⁻¹ : c ∈ reps, x ∈ S } ⊆ Λ,
```

finite as soon as `S` is, and this module proves the three facts about it that
the rest of the development uses.

* `isSymmetricGeneratingSet_schreierSet` --- it is a symmetric generating set of
  `Λ`.  The generating half is **Schreier's theorem**: a finite-index subgroup of
  a finitely generated group is finitely generated (`group_fg_of_finiteIndex`).
* `wordDist_retract_le` --- the retraction `γ ↦ γ·sec(γ)⁻¹` is `1`-Lipschitz
  from the word metric of `S` to the word metric of the Schreier alphabet.  Not
  `K`-Lipschitz: **one** ambient step moves the retraction by **one** Schreier
  generator, which is the content of `RightTransversal.retract_mul_right`.
* `exists_wordNorm_le_mul_schreier` --- conversely the ambient word length of an
  element of `Λ` is at most a constant multiple of its Schreier word length,
  the constant being the largest ambient length of a Schreier generator.

Together these say that `Λ` with its Schreier metric is quasi-isometric to `Γ`,
which is what `Algebra/FiniteIndexQuasiIsometry.lean` assembles.

## The engine

`exists_schreier_word` is the only induction in the file: following a word of
the ambient alphabet from any starting point `γ` moves the retraction by a word
of the *same length* in the Schreier alphabet.  Everything else is a
specialisation --- `γ = 1` gives generation, general `γ` gives the Lipschitz
estimate --- and the induction step is one application of
`RightTransversal.retract_mul_right` together with the telescoping identity
`coe_cocycle_sec`.
-/

namespace GroupApproximation
namespace FiniteIndex

open WordMetric

universe u

variable {Γ : Type u} [Group Γ] {Λ : Subgroup Γ}

/-! ## Symmetrising an alphabet -/

/-- Adjoining inverses to a generating set makes it symmetric without changing
what it generates. -/
theorem isSymmetricGeneratingSet_union_inv {S : Set Γ} (hS : Subgroup.closure S = ⊤) :
    IsSymmetricGeneratingSet (S ∪ S⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inr (Set.mem_inv.mpr (by simpa using hx))
    · exact Or.inl (Set.mem_inv.mp hx)
  · rw [Subgroup.closure_union, Subgroup.closure_inv, hS, sup_idem]

/-- The symmetrisation of a finite set is finite. -/
theorem finite_union_inv {S : Set Γ} (hS : S.Finite) : (S ∪ S⁻¹).Finite :=
  hS.union hS.inv

/-! ## The Schreier alphabet -/

/-- The **Schreier alphabet**: the values of the transversal cocycle on
`reps × S`. -/
def schreierSet (tr : RightTransversal Γ Λ) (S : Set Γ) : Set ↥Λ :=
  (fun p : Γ × Γ => cocycle tr p.1 p.2) '' ((tr.reps : Set Γ) ×ˢ S)

variable (tr : RightTransversal Γ Λ)

/-- Every cocycle value on `reps × S` is a Schreier generator. -/
theorem cocycle_mem_schreierSet {S : Set Γ} {c : Γ} (hc : c ∈ tr.reps) {x : Γ}
    (hx : x ∈ S) : cocycle tr c x ∈ schreierSet tr S :=
  ⟨(c, x), ⟨Finset.mem_coe.mpr hc, hx⟩, rfl⟩

/-- ... and every Schreier generator is one. -/
theorem exists_of_mem_schreierSet {S : Set Γ} {u : ↥Λ} (hu : u ∈ schreierSet tr S) :
    ∃ c ∈ tr.reps, ∃ x ∈ S, cocycle tr c x = u := by
  obtain ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩ := hu
  exact ⟨c, Finset.mem_coe.mp hc, x, hx, rfl⟩

/-- **The Schreier alphabet of a finite alphabet is finite.**  This is where
finiteness of the index is used: `reps` is a `Finset`. -/
theorem schreierSet_finite {S : Set Γ} (hS : S.Finite) : (schreierSet tr S).Finite :=
  ((tr.reps.finite_toSet).prod hS).image _

/-- **The Schreier alphabet is symmetric** when the ambient one is: the inverse
of the generator at `(c, x)` is the generator at `(sec(c·x), x⁻¹)`. -/
theorem schreierSet_inv {S : Set Γ} (hS : ∀ x ∈ S, x⁻¹ ∈ S) :
    ∀ u ∈ schreierSet tr S, u⁻¹ ∈ schreierSet tr S := by
  intro u hu
  obtain ⟨c, hc, x, hx, rfl⟩ := exists_of_mem_schreierSet tr hu
  have hval : (cocycle tr c x)⁻¹ = cocycle tr (tr.sec (c * x)) x⁻¹ := by
    refine Subtype.ext ?_
    have hsec : tr.sec (tr.sec (c * x) * x⁻¹) = c := by
      rw [tr.sec_sec_mul, mul_assoc, mul_inv_cancel, mul_one]
      exact tr.sec_eq_self c hc
    simp only [Subgroup.coe_inv, cocycle_coe, hsec]
    group
  rw [hval]
  exact cocycle_mem_schreierSet tr (tr.sec_mem_reps (c * x)) (hS x hx)

/-! ## The telescoping identity and the induction -/

/-- The coercion of a list product in `Λ`. -/
theorem coe_list_prod (m : List ↥Λ) :
    ((m.prod : ↥Λ) : Γ) = (m.map (fun u : ↥Λ => (u : Γ))).prod := by
  induction m with
  | nil => simp
  | cons u t _ => simp

/-- **The one-step telescoping identity.**  The Schreier generator attached to
`(sec γ, x)` is exactly the amount by which one step to the right moves the
retraction. -/
theorem coe_cocycle_sec (γ x : Γ) :
    ((cocycle tr (tr.sec γ) x : ↥Λ) : Γ) = (tr.retract γ)⁻¹ * tr.retract (γ * x) := by
  rw [tr.retract_mul_right γ x, cocycle_coe, ← mul_assoc, inv_mul_cancel, one_mul]

/-- **The Schreier rewriting process.**  A word of the ambient alphabet, read
from any starting point `γ`, moves the retraction by a word of the same length
in the Schreier alphabet. -/
theorem exists_schreier_word {S : Set Γ} :
    ∀ l : List Γ, (∀ x ∈ l, x ∈ S) → ∀ γ : Γ,
      ∃ m : List ↥Λ, (∀ u ∈ m, u ∈ schreierSet tr S) ∧ m.length = l.length ∧
        ((m.prod : ↥Λ) : Γ) = (tr.retract γ)⁻¹ * tr.retract (γ * l.prod) := by
  intro l
  induction l with
  | nil =>
      intro _ γ
      exact ⟨[], by simp, by simp, by simp⟩
  | cons x t ih =>
      intro hmem γ
      obtain ⟨m, hm, hlen, hprod⟩ :=
        ih (fun y hy => hmem y (List.mem_cons_of_mem x hy)) (γ * x)
      refine ⟨cocycle tr (tr.sec γ) x :: m, ?_, ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact cocycle_mem_schreierSet tr (tr.sec_mem_reps γ) (hmem x (by simp))
        · exact hm u hu'
      · simp [hlen]
      · have hxt : (x :: t).prod = x * t.prod := List.prod_cons
        have hassoc : γ * (x * t.prod) = γ * x * t.prod := (mul_assoc γ x t.prod).symm
        rw [hxt, hassoc, List.prod_cons, Subgroup.coe_mul, hprod, coe_cocycle_sec]
        group

/-! ## Generation -/

/-- Every element of `Λ` is spelled by a Schreier word no longer than its
ambient word length. -/
theorem exists_schreier_word_of_mem {S : Set Γ} (hS : IsSymmetricGeneratingSet S)
    (a : ↥Λ) :
    ∃ m : List ↥Λ, (∀ u ∈ m, u ∈ schreierSet tr S) ∧ m.length = wordNorm S (a : Γ) ∧
      m.prod = a := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS (a : Γ)
  obtain ⟨m, hm, hmlen, hprod⟩ := exists_schreier_word tr l hl.letters 1
  refine ⟨m, hm, by rw [hmlen, hlen], ?_⟩
  refine Subtype.ext ?_
  rw [hprod, tr.retract_one, inv_one, one_mul, one_mul, hl.prod_eq,
    tr.retract_of_mem a.2]

/-- **Schreier's generation theorem.**  The Schreier alphabet generates `Λ`. -/
theorem schreierSet_closure {S : Set Γ} (hS : IsSymmetricGeneratingSet S) :
    Subgroup.closure (schreierSet tr S) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro a
  obtain ⟨m, hm, -, rfl⟩ := exists_schreier_word_of_mem tr hS a
  exact Subgroup.list_prod_mem _ fun u hu => Subgroup.subset_closure (hm u hu)

/-- The Schreier alphabet is a symmetric generating set of `Λ`. -/
theorem isSymmetricGeneratingSet_schreierSet {S : Set Γ}
    (hS : IsSymmetricGeneratingSet S) :
    IsSymmetricGeneratingSet (schreierSet tr S) :=
  ⟨schreierSet_inv tr hS.inv_mem, schreierSet_closure tr hS⟩

/-- **A finite-index subgroup of a finitely generated group is finitely
generated** (Schreier).  The witness is the Schreier alphabet of a symmetrised
finite generating set of `Γ`. -/
theorem group_fg_of_finiteIndex {Γ : Type u} [Group Γ] (Λ : Subgroup Γ)
    [Λ.FiniteIndex] [Group.FG Γ] : Group.FG ↥Λ := by
  classical
  obtain ⟨tr⟩ := exists_rightTransversal Λ
  obtain ⟨S₀, hS₀⟩ := (Group.fg_iff (G := Γ)).mp ‹Group.FG Γ›
  obtain ⟨hgen, hfin⟩ := hS₀
  have hsymm : IsSymmetricGeneratingSet (S₀ ∪ S₀⁻¹) :=
    isSymmetricGeneratingSet_union_inv hgen
  have hSfin : (S₀ ∪ S₀⁻¹).Finite := finite_union_inv hfin
  have hTfin : (schreierSet tr (S₀ ∪ S₀⁻¹)).Finite := schreierSet_finite tr hSfin
  refine ⟨⟨hTfin.toFinset, ?_⟩⟩
  rw [hTfin.coe_toFinset]
  exact schreierSet_closure tr hsymm

/-! ## The two metric estimates -/

/-- **The retraction is `1`-Lipschitz.**  One ambient step moves the retraction
by at most one Schreier generator, so a geodesic of the ambient metric is
matched letter for letter by a Schreier word. -/
theorem wordDist_retract_le {S : Set Γ} (hS : IsSymmetricGeneratingSet S) (x y : Γ) :
    wordDist (schreierSet tr S) ⟨tr.retract x, tr.retract_mem x⟩
        ⟨tr.retract y, tr.retract_mem y⟩ ≤ wordDist S x y := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS (x⁻¹ * y)
  obtain ⟨m, hm, hmlen, hprod⟩ := exists_schreier_word tr l hl.letters x
  have hxy : x * l.prod = y := by rw [hl.prod_eq, mul_inv_cancel_left]
  have hword : IsWord (schreierSet tr S) m
      (⟨tr.retract x, tr.retract_mem x⟩⁻¹ * ⟨tr.retract y, tr.retract_mem y⟩) := by
    refine ⟨hm, ?_⟩
    refine Subtype.ext ?_
    rw [hprod, hxy]
    simp
  have hle := wordNorm_le_length hword
  rw [hmlen, hlen] at hle
  simpa [wordDist] using hle

/-- **The comparison in the other direction.**  Each Schreier generator has some
ambient word length; the largest of them is a Lipschitz constant for the
inclusion. -/
theorem exists_wordNorm_le_mul_schreier {S : Set Γ} (hS : IsSymmetricGeneratingSet S)
    (hfin : (schreierSet tr S).Finite) :
    ∃ M : ℕ, ∀ a : ↥Λ,
      wordNorm S (a : Γ) ≤ M * wordNorm (schreierSet tr S) a := by
  classical
  refine ⟨hfin.toFinset.sup fun u : ↥Λ => wordNorm S (u : Γ), fun a => ?_⟩
  obtain ⟨m, hm, hmlen⟩ :=
    exists_isWord_length_eq (isSymmetricGeneratingSet_schreierSet tr hS) a
  have hcoe : ((m.prod : ↥Λ) : Γ) = (a : Γ) := by rw [hm.prod_eq]
  have hbound : ∀ z ∈ (m.map fun u : ↥Λ => (u : Γ)).map (wordNorm S),
      z ≤ hfin.toFinset.sup fun u : ↥Λ => wordNorm S (u : Γ) := by
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨u, hu, rfl⟩ := hw
    exact Finset.le_sup (f := fun u : ↥Λ => wordNorm S (u : Γ))
      (hfin.mem_toFinset.mpr (hm.letters u hu))
  calc wordNorm S (a : Γ)
      = wordNorm S (m.map fun u : ↥Λ => (u : Γ)).prod := by
        rw [← coe_list_prod, hcoe]
    _ ≤ ((m.map fun u : ↥Λ => (u : Γ)).map (wordNorm S)).sum :=
        wordNorm_prod_le hS _
    _ ≤ (((m.map fun u : ↥Λ => (u : Γ)).map (wordNorm S)).length) *
          (hfin.toFinset.sup fun u : ↥Λ => wordNorm S (u : Γ)) :=
        sum_le_length_mul _ _ hbound
    _ = (hfin.toFinset.sup fun u : ↥Λ => wordNorm S (u : Γ)) *
          wordNorm (schreierSet tr S) a := by
        rw [List.length_map, List.length_map, hmlen]
        ring

end FiniteIndex
end GroupApproximation
