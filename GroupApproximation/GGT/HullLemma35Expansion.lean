import GroupApproximation.GGT.HullSCUnconePathPoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: guessed paths along an expansion of the letters

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`).  Its hyperbolicity clause
is proved with Bowditch's guessing-geodesics criterion: a geodesic word of a relative generating set
`D` is expanded letter by letter into a word over a smaller alphabet `S`.

This module builds the guessed paths for any expansion `ex : RelLetter G Λ → List G` that spells
every letter of `D` (`hprod`) with letters of `S` (`hmem`):

* `guessPath_zero`, `guessPath_len` — the path runs from `x` to `y`;
* `wordDist_guessPath_succ`, `wordDist_guessPath_le` — consecutive points are adjacent in `Γ(G, S)`;
* `guessPath_short` — adjacent endpoints give a short path, when `S` lies in the alphabet of `D` and
  the expansion of a letter spelling an element of `S` is short;
* `guessPath_at_letter`, `guessPath_in_letter`, `exists_letter_block` — the points of the path, read
  off the letters of the geodesic word.

It adapts `GGT/HullSCUnconeExpansion.lean` and `GGT/HullSCUnconePathPoints.lean`, where `ex` expands
the letters of cyclic members.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

section Words

variable {G : Type u} {Λ : Type w}

/-! ## Expanding a word -/

/-- **The expansion of a word of `D`**, letter by letter along `ex`. -/
def expWord (ex : RelLetter G Λ → List G) : List (RelLetter G Λ) → List G
  | [] => []
  | a :: t => ex a ++ expWord ex t

theorem expWord_nil (ex : RelLetter G Λ → List G) : expWord ex [] = [] := rfl

theorem expWord_cons (ex : RelLetter G Λ → List G) (a : RelLetter G Λ)
    (t : List (RelLetter G Λ)) : expWord ex (a :: t) = ex a ++ expWord ex t := rfl

theorem expWord_append (ex : RelLetter G Λ → List G) :
    ∀ w₁ w₂ : List (RelLetter G Λ), expWord ex (w₁ ++ w₂) = expWord ex w₁ ++ expWord ex w₂ := by
  intro w₁
  induction w₁ with
  | nil => intro w₂; rfl
  | cons a t ih =>
      intro w₂
      rw [List.cons_append, expWord_cons, expWord_cons, ih, List.append_assoc]

theorem expWord_take_append (ex : RelLetter G Λ → List G) (w : List (RelLetter G Λ)) (k : ℕ) :
    expWord ex w = expWord ex (w.take k) ++ expWord ex (w.drop k) := by
  rw [← expWord_append, List.take_append_drop]

theorem expWord_drop_eq_cons (ex : RelLetter G Λ → List G) (w : List (RelLetter G Λ)) {k : ℕ}
    (hk : k < w.length) :
    expWord ex (w.drop k) = ex (w[k]'hk) ++ expWord ex (w.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk, expWord_cons]

theorem length_expWord_take_le (ex : RelLetter G Λ → List G) (w : List (RelLetter G Λ)) (k : ℕ) :
    (expWord ex (w.take k)).length ≤ (expWord ex w).length := by
  rw [expWord_take_append ex w k, List.length_append]
  omega

/-- The expansion of the letters up to and including the `j`-th fits in the whole expansion. -/
theorem length_expWord_take_add_le (ex : RelLetter G Λ → List G) (w : List (RelLetter G Λ))
    {j : ℕ} (hj : j < w.length) :
    (expWord ex (w.take j)).length + (ex (w[j]'hj)).length ≤ (expWord ex w).length := by
  rw [expWord_take_append ex w j, expWord_drop_eq_cons ex w hj, List.length_append,
    List.length_append]
  omega

/-- **Every index of the expansion is at a letter boundary or strictly inside one letter.** -/
theorem exists_letter_block (ex : RelLetter G Λ → List G) :
    ∀ (w : List (RelLetter G Λ)) (j : ℕ), j ≤ (expWord ex w).length →
      (∃ k : ℕ, k ≤ w.length ∧ j = (expWord ex (w.take k)).length) ∨
        (∃ (k : ℕ) (hk : k < w.length) (s : ℕ), 0 < s ∧
          s < (ex (w[k]'hk)).length ∧ j = (expWord ex (w.take k)).length + s) := by
  intro w
  induction w with
  | nil =>
      intro j hj
      refine Or.inl ⟨0, le_rfl, ?_⟩
      simp only [expWord, List.length_nil] at hj
      simp [expWord]
      omega
  | cons a t ih =>
      intro j hj
      rw [expWord_cons, List.length_append] at hj
      by_cases hja : j ≤ (ex a).length
      · by_cases hj0 : j = 0
        · exact Or.inl ⟨0, by simp, by simp [expWord, hj0]⟩
        · by_cases hjl : j = (ex a).length
          · refine Or.inl ⟨1, by simp, ?_⟩
            simp [expWord, hjl]
          · refine Or.inr ⟨0, by simp, j, by omega, ?_, by simp [expWord]⟩
            simp only [List.getElem_cons_zero]
            omega
      · obtain h | h := ih (j - (ex a).length) (by omega)
        · obtain ⟨k, hk, hjk⟩ := h
          refine Or.inl ⟨k + 1, by simp; omega, ?_⟩
          simp only [List.take_succ_cons, expWord_cons, List.length_append]
          omega
        · obtain ⟨k, hk, s, hs0, hsl, hjk⟩ := h
          refine Or.inr ⟨k + 1, by simp; omega, s, hs0, ?_, ?_⟩
          · simpa using hsl
          · simp only [List.take_succ_cons, expWord_cons, List.length_append]
            omega

end Words

section Expansion

variable {G : Type u} [Group G] {Λ : Type w}

/-- The expansion of a legal word spells its value. -/
theorem prod_expWord (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) :
    ∀ w : List (RelLetter G Λ), (∀ a ∈ w, D.IsLetter a) →
      (expWord ex w).prod = RelLetter.listVal w := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons a t ih =>
      intro hletters
      rw [expWord_cons, List.prod_append, hprod a (hletters a (by simp)),
        ih (fun b hb => hletters b (List.mem_cons_of_mem a hb)), OsinComponents.listVal_cons]

/-- Every letter of the expansion of a legal word is a letter of `S`. -/
theorem mem_expWord (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) {S : Set G}
    (hmem : ∀ a : RelLetter G Λ, D.IsLetter a → ∀ s ∈ ex a, s ∈ S) :
    ∀ w : List (RelLetter G Λ), (∀ a ∈ w, D.IsLetter a) → ∀ s ∈ expWord ex w, s ∈ S := by
  intro w
  induction w with
  | nil => intro _ s hs; simp [expWord] at hs
  | cons a t ih =>
      intro hletters s hs
      rw [expWord_cons] at hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hmem a (hletters a (by simp)) s hs
      · exact ih (fun b hb => hletters b (List.mem_cons_of_mem a hb)) s hs

/-! ## The guessed paths -/

/-- A chosen geodesic word of `D` from `x` to `y`. -/
noncomputable def geodWord (D : RelGenSet G Λ) (x y : G) : List (RelLetter G Λ) :=
  Classical.choose (OsinComponents.existsGeodesicWord D x y)

theorem geodWord_spec (D : RelGenSet G Λ) (x y : G) :
    OsinComponents.IsGeodesicWord D x y (geodWord D x y) :=
  Classical.choose_spec (OsinComponents.existsGeodesicWord D x y)

/-- The expanded geodesic from `x` to `y`. -/
noncomputable def guessWord (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) (x y : G) :
    List G :=
  expWord ex (geodWord D x y)

/-- The number of steps of the guessed path. -/
noncomputable def guessLen (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) (x y : G) : ℕ :=
  (guessWord D ex x y).length

/-- **The guessed path from `x` to `y`**: the prefix products of the expanded geodesic. -/
noncomputable def guessPath (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) (x y : G) (j : ℕ) :
    G :=
  x * ((guessWord D ex x y).take j).prod

theorem guessPath_zero (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) (x y : G) :
    guessPath D ex x y 0 = x := by
  simp [guessPath]

theorem guessPath_len (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) (x y : G) :
    guessPath D ex x y (guessLen D ex x y) = y := by
  rw [guessPath, guessLen, List.take_length, guessWord,
    prod_expWord D ex hprod _ (geodWord_spec D x y).1]
  exact (geodWord_spec D x y).2.1

/-- **Consecutive points of a guessed path are adjacent in `Γ(G, S)`.** -/
theorem wordDist_guessPath_succ (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) {S : Set G}
    (hmem : ∀ a : RelLetter G Λ, D.IsLetter a → ∀ s ∈ ex a, s ∈ S) (x y : G) {j : ℕ}
    (hj : j < guessLen D ex x y) :
    wordDist S (guessPath D ex x y j) (guessPath D ex x y (j + 1)) ≤ 1 := by
  have hj' : j < (guessWord D ex x y).length := hj
  have hs := mem_expWord D ex hmem (geodWord D x y) (geodWord_spec D x y).1 _
    (List.getElem_mem hj')
  have h : (guessPath D ex x y j)⁻¹ * guessPath D ex x y (j + 1) = (guessWord D ex x y)[j] := by
    unfold guessPath
    rw [List.prod_take_succ _ _ hj']
    group
  unfold wordDist
  rw [h]
  exact wordNorm_le_one_of_mem hs

/-- **A guessed path is `1`-Lipschitz in its index.** -/
theorem wordDist_guessPath_le (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) {S : Set G}
    (hS : IsSymmetricGeneratingSet S)
    (hmem : ∀ a : RelLetter G Λ, D.IsLetter a → ∀ s ∈ ex a, s ∈ S) (x y : G) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ guessLen D ex x y) :
    wordDist S (guessPath D ex x y i) (guessPath D ex x y j) ≤ j - i := by
  induction j, hij using Nat.le_induction with
  | base =>
      rw [wordDist_self]
      omega
  | succ n hin ih =>
      have hn : n < guessLen D ex x y := by omega
      have hstep := wordDist_guessPath_succ D ex hmem x y hn
      have htri := wordDist_triangle hS (guessPath D ex x y i) (guessPath D ex x y n)
        (guessPath D ex x y (n + 1))
      have hih := ih (by omega)
      omega

/-- **Adjacent endpoints give a short guessed path.** -/
theorem guessLen_le_of_wordDist_le_one (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    {S : Set G} (hS : IsSymmetricGeneratingSet S) (hsub : S ⊆ D.alphabet.carrier) {L : ℕ}
    (hshort : ∀ a : RelLetter G Λ, D.IsLetter a → wordNorm S a.val ≤ 1 → (ex a).length ≤ L)
    {x y : G} (hxy : wordDist S x y ≤ 1) : guessLen D ex x y ≤ L := by
  have hw := geodWord_spec D x y
  have hdd : wordDist D.alphabet.carrier x y ≤ 1 :=
    le_trans (wordNorm_mono hsub (wordLengths_nonempty hS (x⁻¹ * y))) hxy
  have hlen : (geodWord D x y).length ≤ 1 := by
    rw [hw.2.2]
    exact hdd
  unfold guessLen guessWord
  rcases hcase : geodWord D x y with _ | ⟨a, t⟩
  · simp [expWord]
  · have ht : t = [] := by
      rw [hcase] at hlen
      simp only [List.length_cons] at hlen
      exact List.length_eq_zero_iff.mp (by omega)
    subst ht
    have ha : D.IsLetter a := hw.1 a (by rw [hcase]; simp)
    have hval : x * a.val = y := by
      have h := hw.2.1
      rw [hcase] at h
      simpa [RelLetter.listVal] using h
    rw [expWord_cons, expWord_nil, List.append_nil]
    refine hshort a ha ?_
    have h := hxy
    unfold wordDist at h
    rwa [show x⁻¹ * y = a.val by rw [← hval, inv_mul_cancel_left]] at h

/-- **The short-path condition of the guessing criterion.** -/
theorem guessPath_short (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G) {S : Set G}
    (hS : IsSymmetricGeneratingSet S) (hsub : S ⊆ D.alphabet.carrier)
    (hmem : ∀ a : RelLetter G Λ, D.IsLetter a → ∀ s ∈ ex a, s ∈ S) {L : ℕ}
    (hshort : ∀ a : RelLetter G Λ, D.IsLetter a → wordNorm S a.val ≤ 1 → (ex a).length ≤ L)
    (x y : G) (hxy : wordDist S x y ≤ 1) (i : ℕ) (hi : i ≤ guessLen D ex x y) (j : ℕ)
    (hj : j ≤ guessLen D ex x y) :
    wordDist S (guessPath D ex x y i) (guessPath D ex x y j) ≤ L := by
  have hlen := guessLen_le_of_wordDist_le_one D ex hS hsub hshort hxy
  rcases le_total i j with hij | hji
  · have h := wordDist_guessPath_le D ex hS hmem x y hij hj
    omega
  · have h := wordDist_guessPath_le D ex hS hmem x y hji hi
    rw [wordDist_comm hS] at h
    omega

/-! ## The points of a guessed path -/

/-- **At a letter boundary the guessed path is at a vertex of the geodesic word.** -/
theorem guessPath_at_letter (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) (x y : G) (k : ℕ) :
    guessPath D ex x y (expWord ex ((geodWord D x y).take k)).length
      = vertex x (geodWord D x y) k := by
  have hlet : ∀ a ∈ (geodWord D x y).take k, D.IsLetter a :=
    fun a ha => (geodWord_spec D x y).1 a (List.take_subset k _ ha)
  unfold guessPath guessWord
  rw [expWord_take_append ex (geodWord D x y) k, List.take_left' rfl,
    prod_expWord D ex hprod _ hlet, vertex_eq_mul_listVal_take]

/-- **Inside the expansion of a letter the guessed path is at that letter's vertex times a prefix
of its expansion.** -/
theorem guessPath_in_letter (D : RelGenSet G Λ) (ex : RelLetter G Λ → List G)
    (hprod : ∀ a : RelLetter G Λ, D.IsLetter a → (ex a).prod = a.val) (x y : G) {k : ℕ}
    (hk : k < (geodWord D x y).length) {s : ℕ}
    (hs : s ≤ (ex ((geodWord D x y)[k]'hk)).length) :
    guessPath D ex x y ((expWord ex ((geodWord D x y).take k)).length + s)
      = vertex x (geodWord D x y) k * ((ex ((geodWord D x y)[k]'hk)).take s).prod := by
  have hlet : ∀ a ∈ (geodWord D x y).take k, D.IsLetter a :=
    fun a ha => (geodWord_spec D x y).1 a (List.take_subset k _ ha)
  unfold guessPath guessWord
  rw [expWord_take_append ex (geodWord D x y) k, expWord_drop_eq_cons ex (geodWord D x y) hk,
    List.take_append,
    List.take_of_length_le (l := expWord ex ((geodWord D x y).take k)) (Nat.le_add_right _ s),
    Nat.add_sub_cancel_left, List.take_append, Nat.sub_eq_zero_of_le hs, List.take_zero,
    List.append_nil, List.prod_append, prod_expWord D ex hprod _ hlet, vertex_eq_mul_listVal_take,
    mul_assoc]

end Expansion

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.prod_expWord
#audit_axioms GroupApproximation.GGT.HullLemma35.mem_expWord
#audit_axioms GroupApproximation.GGT.HullLemma35.guessPath_len
#audit_axioms GroupApproximation.GGT.HullLemma35.wordDist_guessPath_le
#audit_axioms GroupApproximation.GGT.HullLemma35.guessPath_short
#audit_axioms GroupApproximation.GGT.HullLemma35.guessPath_in_letter
#audit_axioms GroupApproximation.GGT.HullLemma35.exists_letter_block
