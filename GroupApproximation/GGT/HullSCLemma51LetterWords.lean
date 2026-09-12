import GroupApproximation.GGT.HullSCLemma51QuotientStokes
import GroupApproximation.Algebra.CayleyPathVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# Words over a relative alphabet: inverse respelling and geodesic cosets

Two facts about words over the letters of a relative generating set, used by the
letter pullback of Osin's Lemma 5.1 (`GGT/HullSCLemma51EmbeddedProducer.lean`).

**Inverse respelling.**  A relative ball `D.relBall λ n` is read along paths of
admissible letters in the forward direction, and the formal inverse of a base letter
need not be a base letter.  `respellInv D w` reads `w` backwards letter by letter,
spelling the inverse of each letter as a letter of `D`: the inverse of a base letter is
a base letter when it can be, and otherwise a peripheral letter, which exists because
the alphabet is symmetric.  It spells the inverse element
(`listVal_respellInv`), and a peripheral letter of index `λ` in it comes from a
peripheral letter of index `λ` of `w` or from a base letter of `w` lying in `H_λ`
(`isCompOf_invLetter`).

**Geodesic cosets.**  A geodesic word reads at most one peripheral letter of index `λ`
in each coset of `H_λ` (`eq_of_isCompOf_of_mem_fam_of_geodesic`): two such letters
would be joined by a single peripheral letter.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric
open GroupApproximation.DiscreteStokes

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## Inverse respelling -/

open Classical in
/-- **The inverse of a letter, spelled as a letter of `D`.** -/
noncomputable def invLetter (D : GGT.RelGenSet G Lambda) :
    GGT.RelLetter G Lambda → GGT.RelLetter G Lambda
  | GGT.RelLetter.base x =>
      if x⁻¹ ∈ D.base then GGT.RelLetter.base x⁻¹
      else if h : ∃ lam, x⁻¹ ∈ D.fam lam then GGT.RelLetter.comp (Classical.choose h) x⁻¹
      else GGT.RelLetter.base x⁻¹
  | GGT.RelLetter.comp lam h => GGT.RelLetter.comp lam h⁻¹

theorem val_invLetter (D : GGT.RelGenSet G Lambda) (a : GGT.RelLetter G Lambda) :
    (invLetter D a).val = a.val⁻¹ := by
  cases a with
  | base x =>
      simp only [invLetter]
      split_ifs <;> rfl
  | comp lam h => rfl

theorem isLetter_invLetter (D : GGT.RelGenSet G Lambda) {a : GGT.RelLetter G Lambda}
    (ha : D.IsLetter a) : D.IsLetter (invLetter D a) := by
  cases a with
  | base x =>
      have hmem : x⁻¹ ∈ D.base ∪ ⋃ lam : Lambda, (D.fam lam : Set G) :=
        D.symmetricGenerating.inv_mem x (Set.mem_union_left _ ha)
      simp only [invLetter]
      split_ifs with h1 h2
      · exact h1
      · exact Classical.choose_spec h2
      · exfalso
        rcases hmem with hb | hf
        · exact h1 hb
        · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
          exact h2 ⟨lam, hlam⟩
  | comp lam h =>
      show h⁻¹ ∈ D.fam lam
      exact (D.fam lam).inv_mem ha

/-- A peripheral letter of index `λ` in a respelled inverse comes from a peripheral
letter of index `λ`, or from a base letter lying in `H_λ`. -/
theorem isCompOf_invLetter (D : GGT.RelGenSet G Lambda) {lam : Lambda}
    {a : GGT.RelLetter G Lambda} (ha : GGT.RelLetter.IsCompOf lam (invLetter D a)) :
    GGT.RelLetter.IsCompOf lam a ∨ ∃ x : G, a = GGT.RelLetter.base x ∧ x ∈ D.fam lam := by
  cases a with
  | base x =>
      right
      refine ⟨x, rfl, ?_⟩
      simp only [invLetter] at ha
      split_ifs at ha with h1 h2
      · exact False.elim ha
      · have hlam : Classical.choose h2 = lam := ha
        have hspec := Classical.choose_spec h2
        rw [hlam] at hspec
        simpa using (D.fam lam).inv_mem hspec
      · exact False.elim ha
  | comp mu h =>
      left
      exact ha

/-- **Reading a word backwards, letter by letter, with inverse letters of `D`.** -/
noncomputable def respellInv (D : GGT.RelGenSet G Lambda)
    (word : List (GGT.RelLetter G Lambda)) : List (GGT.RelLetter G Lambda) :=
  (word.map (invLetter D)).reverse

@[simp] theorem length_respellInv (D : GGT.RelGenSet G Lambda)
    (word : List (GGT.RelLetter G Lambda)) : (respellInv D word).length = word.length := by
  simp [respellInv]

theorem isLetter_respellInv (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)} (hword : ∀ a ∈ word, D.IsLetter a) :
    ∀ a ∈ respellInv D word, D.IsLetter a := by
  intro a ha
  simp only [respellInv, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact isLetter_invLetter D (hword b hb)

theorem respellInv_cons (D : GGT.RelGenSet G Lambda) (a : GGT.RelLetter G Lambda)
    (t : List (GGT.RelLetter G Lambda)) :
    respellInv D (a :: t) = respellInv D t ++ [invLetter D a] := by
  simp [respellInv]

theorem respellInv_append (D : GGT.RelGenSet G Lambda)
    (v t : List (GGT.RelLetter G Lambda)) :
    respellInv D (v ++ t) = respellInv D t ++ respellInv D v := by
  simp [respellInv]

/-- **The respelled inverse spells the inverse element.** -/
theorem listVal_respellInv (D : GGT.RelGenSet G Lambda) :
    ∀ word : List (GGT.RelLetter G Lambda),
      GGT.RelLetter.listVal (respellInv D word) = (GGT.RelLetter.listVal word)⁻¹
  | [] => by simp [respellInv, GGT.RelLetter.listVal]
  | a :: t => by
      rw [respellInv_cons, RelWord.listVal_append, listVal_respellInv D t,
        RelWord.listVal_singleton, val_invLetter, RelWord.listVal_cons, mul_inv_rev]

/-! ## Geodesic words and cosets -/

/-- The vertices of a relative word are the partial products of its values. -/
theorem vertex_one_eq_prod_take (word : List (GGT.RelLetter G Lambda)) (i : ℕ) :
    GGT.OsinComponents.vertex 1 word i = ((word.map GGT.RelLetter.val).take i).prod := by
  rw [vertex_eq_mul_listVal_take, one_mul]
  unfold GGT.RelLetter.listVal
  rw [List.map_take]

/-- **Vertices of a geodesic relative word are at their index distance.** -/
theorem wordDist_vertex_of_geodesic (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)} (hword : ∀ a ∈ word, D.IsLetter a)
    (hgeo : word.length = wordNorm D.alphabet.carrier (GGT.RelLetter.listVal word))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ word.length) :
    wordDist D.alphabet.carrier (GGT.OsinComponents.vertex 1 word i)
      (GGT.OsinComponents.vertex 1 word j) = j - i := by
  have hγ : IsGeodesicWord D.alphabet.carrier (word.map GGT.RelLetter.val)
      (word.map GGT.RelLetter.val).prod := by
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact RelativeBoundaryContiguity.val_mem_alphabet_of_isLetter D (hword a ha)
    · rw [List.length_map]
      exact hgeo
  have h := wordDist_take_of_geodesic D.alphabet.symmetricGenerating hγ 1 hij
    (by rw [List.length_map]; exact hj)
  rw [one_mul, one_mul] at h
  rw [vertex_one_eq_prod_take, vertex_one_eq_prod_take]
  exact h

/-- **A geodesic word reads at most one peripheral letter of index `λ` in each coset of
`H_λ`.** -/
theorem eq_of_isCompOf_of_mem_fam_of_geodesic (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)} (hword : ∀ a ∈ word, D.IsLetter a)
    (hgeo : word.length = wordNorm D.alphabet.carrier (GGT.RelLetter.listVal word))
    {lam : Lambda} {i k : ℕ} (hik : i ≤ k) (hk : k < word.length)
    (hkcomp : GGT.RelLetter.IsCompOf lam (word[k]))
    (hcoset : (GGT.OsinComponents.vertex 1 word i)⁻¹ * GGT.OsinComponents.vertex 1 word k ∈
      D.fam lam) : i = k := by
  have hletter : D.IsLetter (word[k]) := hword _ (List.getElem_mem hk)
  have hvalfam : (word[k]).val ∈ D.fam lam := by
    revert hkcomp hletter
    cases word[k] with
    | base x => intro h; exact False.elim h
    | comp mu h =>
        intro hmu hh
        have hmu' : mu = lam := hmu
        subst hmu'
        exact hh
  have hsucc : GGT.OsinComponents.vertex 1 word (k + 1) =
      GGT.OsinComponents.vertex 1 word k * (word[k]).val := by
    rw [vertex_eq_mul_listVal_take, vertex_eq_mul_listVal_take, List.take_succ_eq_append_getElem hk,
      RelWord.listVal_append, RelWord.listVal_singleton, mul_assoc]
  have hjump : (GGT.OsinComponents.vertex 1 word i)⁻¹ * GGT.OsinComponents.vertex 1 word (k + 1) ∈
      D.fam lam := by
    rw [hsucc, ← mul_assoc]
    exact (D.fam lam).mul_mem hcoset hvalfam
  have hle : wordDist D.alphabet.carrier (GGT.OsinComponents.vertex 1 word i)
      (GGT.OsinComponents.vertex 1 word (k + 1)) ≤ 1 :=
    wordNorm_le_one_of_mem (GGT.RelGenSet.fam_subset_alphabet D lam hjump)
  rw [wordDist_vertex_of_geodesic D hword hgeo (i := i) (j := k + 1) (by omega) (by omega)] at hle
  omega

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.val_invLetter
#audit_axioms GroupApproximation.HullSC.isLetter_invLetter
#audit_axioms GroupApproximation.HullSC.isCompOf_invLetter
#audit_axioms GroupApproximation.HullSC.listVal_respellInv
#audit_axioms GroupApproximation.HullSC.wordDist_vertex_of_geodesic
#audit_axioms GroupApproximation.HullSC.eq_of_isCompOf_of_mem_fam_of_geodesic
