import GroupApproximation.GGT.HullLemma35Transitive
import GroupApproximation.GGT.DGOProposition435FiniteLetters
import GroupApproximation.GGT.OsinTheorem54SeparatingCosets
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: local finiteness of the subfamilies

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
cites Hull's Corollary 7.4, whose proof applies Lemma 3.5 (arXiv:1308.4345v2, §3, p. 12):
`{H_i} ↪h G` and `{K_{ij}}_j ↪h H_i` give `{K_{ij}}_{i,j} ↪h G`.

This module proves the local-finiteness clause of that conclusion for the structure
`transitiveRelGenSet D E` of `GGT/HullLemma35Transitive.lean`: if the relative balls of `D` and
of every `E i` are finite, so are those of the transitive structure
(`relBall_finite_transitive`).

Take a path of length at most `n` in `Γ(G, X')` from `1` to an element of `K_{ij}`, where `X'`
is the transitive alphabet.  Assume the path has no edge in the coset `K_{ij}` at a vertex of
`K_{ij}`.  Read the path through `H i`:

* An edge between two vertices of `H i` becomes one letter of `E i`.  The letter is kept when it
  is a letter of `E i`.  Otherwise the edge spells an element of `H i` that is a letter of
  another member `H i'`, and that element lies in `D.relBall i n`.
* An excursion that leaves `H i` and returns spells an element of `D.relBall i n`, since it has
  no edge in `H i` at a vertex of `H i`.

Both kinds lie in the finite set `excursionLetters D i n`.  The path becomes a path of length at
most `n` in `Γ(H i, Y_i ∪ excursionLetters D i n ∪ ⋃_j K_{ij})` with no edge in `K_{ij}` at a
vertex of `K_{ij}` (`exists_enlargedWord`).  That relative ball is finite by the Corollary 4.27
local half, `RelHyp.relBall_finite_adjoinBase'`.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric

universe u v w

variable {G : Type u} [Group G] {Λ : Type v} {M : Λ → Type w}

theorem mem_right_of_mul_mem_subgroup {K : Subgroup G} {x y : G} (hx : x ∈ K)
    (hxy : x * y ∈ K) : y ∈ K := by
  simpa using K.mul_mem (K.inv_mem hx) hxy

/-- **The excursion letters at radius `n`**: the elements of `H i` in the relative ball
`D.relBall i n`, with their inverses. -/
def excursionLetters (D : RelGenSet G Λ) (i : Λ) (n : ℕ) : Set (D.fam i) :=
  {x | (x : G) ∈ D.relBall i n ∨ ((x⁻¹ : D.fam i) : G) ∈ D.relBall i n}

theorem excursionLetters_inv (D : RelGenSet G Λ) (i : Λ) (n : ℕ) :
    ∀ x ∈ excursionLetters D i n, x⁻¹ ∈ excursionLetters D i n := by
  rintro x (hx | hx)
  · show ((x⁻¹ : D.fam i) : G) ∈ D.relBall i n ∨ (((x⁻¹)⁻¹ : D.fam i) : G) ∈ D.relBall i n
    rw [inv_inv]
    exact Or.inr hx
  · exact Or.inl hx

theorem excursionLetters_finite (D : RelGenSet G Λ) {i : Λ} {n : ℕ}
    (hloc : (D.relBall i n).Finite) : (excursionLetters D i n).Finite := by
  have h1 : ((Subtype.val : D.fam i → G) ⁻¹' D.relBall i n).Finite :=
    hloc.preimage (fun _ _ _ _ h => Subtype.val_injective h)
  have h2 : ((fun x : D.fam i => x⁻¹) ⁻¹'
      ((Subtype.val : D.fam i → G) ⁻¹' D.relBall i n)).Finite :=
    h1.preimage (fun _ _ _ _ h => inv_injective h)
  exact (h1.union h2).subset (fun x hx => hx)

/-- **The enlarged structure on `H i`**: `E i` with the excursion letters adjoined to its base. -/
def enlarged (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) (i : Λ) (n : ℕ) :
    RelGenSet (D.fam i) (M i) :=
  RelHyp.adjoinBase (E i) (excursionLetters D i n) (excursionLetters_inv D i n)

/-- A letter of another member `H i'` that lies in `H i` is an excursion letter. -/
theorem mem_excursionLetters_of_ne (D : RelGenSet G Λ) {i i' : Λ} {n : ℕ} (hn : 1 ≤ n)
    (hii : i' ≠ i) {x : G} (hx' : x ∈ D.fam i') (hx : x ∈ D.fam i) :
    (⟨x, hx⟩ : D.fam i) ∈ excursionLetters D i n := by
  show ((⟨x, hx⟩ : D.fam i) : G) ∈ D.relBall i n ∨ _
  left
  refine ⟨hx, [RelLetter.comp i' x], ?_, ?_, ⟨fun h => hii h.1, trivial⟩, by simpa using hn⟩
  · intro a ha
    rw [List.eq_of_mem_singleton ha]
    exact hx'
  · simp [RelLetter.listVal, RelLetter.val]

/-- **One edge between two vertices of `H i` becomes one letter of the enlarged structure**, and
a component letter of `K_{ij}` stays one. -/
theorem exists_enlargedLetter (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {i : Λ} (j : M i) {n : ℕ} (hn : 1 ≤ n) {a : RelLetter G ((i : Λ) × M i)}
    (ha : (transitiveRelGenSet D E).IsLetter a) (hmem : a.val ∈ D.fam i) :
    ∃ b : RelLetter (D.fam i) (M i), (enlarged D E i n).IsLetter b ∧
      ((b.val : D.fam i) : G) = a.val ∧
      ∀ v : D.fam i, RelLetter.IsCompOf j b → v ∈ (E i).fam j →
        RelLetter.IsCompOf (⟨i, j⟩ : (i : Λ) × M i) a ∧
          (v : G) ∈ (transitiveRelGenSet D E).fam ⟨i, j⟩ := by
  cases a with
  | base x =>
      rcases (show x ∈ transitiveBase D E from ha) with hx | hx
      · exact absurd hmem (RelHyp.properBase_disjoint_fam D i hx)
      · obtain ⟨i', e, he, rfl⟩ := Set.mem_iUnion.mp hx
        by_cases hii : i' = i
        · subst hii
          exact ⟨RelLetter.base e, Or.inl he, rfl, fun _ hc _ => (hc : False).elim⟩
        · have hmem' : (e : G) ∈ D.fam i := hmem
          exact ⟨RelLetter.base ⟨(e : G), hmem'⟩,
            Or.inr (mem_excursionLetters_of_ne D hn hii e.2 hmem'), rfl,
            fun _ hc _ => (hc : False).elim⟩
  | comp p h =>
      obtain ⟨i', j'⟩ := p
      obtain ⟨e, he, rfl⟩ := (show h ∈ ((E i').fam j').map (D.fam i').subtype from ha)
      by_cases hii : i' = i
      · subst hii
        refine ⟨RelLetter.comp j' e, he, rfl, fun v hc hv => ⟨?_, Subgroup.mem_map_of_mem _ hv⟩⟩
        obtain rfl : j' = j := hc
        exact rfl
      · have hmem' : (e : G) ∈ D.fam i := hmem
        exact ⟨RelLetter.base ⟨(e : G), hmem'⟩,
          Or.inr (mem_excursionLetters_of_ne D hn hii e.2 hmem'), rfl,
          fun _ hc _ => (hc : False).elim⟩

/-- **A path of the transitive structure between two vertices of `H i` becomes a path of the
enlarged structure.**

The state is a vertex `v` of `H i` and a pending excursion `s`, a word of `D` read from `v`.
Either `s` is empty, or `v * s` has left `H i` and `s` has no edge in `H i` at a vertex of
`H i`. -/
theorem exists_enlargedWord (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {i : Λ} (j : M i) {n : ℕ} :
    ∀ (w : List (RelLetter G ((i : Λ) × M i))) (v : D.fam i) (s : List (RelLetter G Λ)),
      (∀ b ∈ s, D.IsLetter b) → AvoidsFrom D.fam i s 1 →
      (s ≠ [] → (v : G) * RelLetter.listVal s ∉ D.fam i) →
      (∀ a ∈ w, (transitiveRelGenSet D E).IsLetter a) →
      AvoidsFrom (transitiveRelGenSet D E).fam ⟨i, j⟩ w ((v : G) * RelLetter.listVal s) →
      (v : G) * RelLetter.listVal s * RelLetter.listVal w ∈ D.fam i →
      s.length + w.length ≤ n →
      ∃ u : List (RelLetter (D.fam i) (M i)), (∀ b ∈ u, (enlarged D E i n).IsLetter b) ∧
        ((RelLetter.listVal u : D.fam i) : G) = RelLetter.listVal s * RelLetter.listVal w ∧
        AvoidsFrom (E i).fam j u v ∧ u.length ≤ s.length + w.length := by
  intro w
  induction w with
  | nil =>
      intro v s _ _ hsout _ _ hend _
      have hs0 : s = [] := by
        by_contra hne
        apply hsout hne
        rw [RelLetter.listVal_nil, mul_one] at hend
        exact hend
      subst hs0
      exact ⟨[], by simp, by simp [RelLetter.listVal], trivial, by simp⟩
  | cons a w ih =>
      intro v s hs hsav hsout hw hwav hend hlen
      have ha : (transitiveRelGenSet D E).IsLetter a := hw a (by simp)
      have hw' : ∀ b ∈ w, (transitiveRelGenSet D E).IsLetter b :=
        fun b hb => hw b (List.mem_cons_of_mem a hb)
      obtain ⟨hwav1, hwav'⟩ := hwav
      have hv : (v : G) ∈ D.fam i := v.2
      have hend' : (v : G) * RelLetter.listVal s * a.val * RelLetter.listVal w ∈ D.fam i := by
        rw [OsinComponents.listVal_cons, ← mul_assoc] at hend
        exact hend
      simp only [List.length_cons] at hlen
      obtain ⟨b', hb', hb'val⟩ := exists_letter_of_mem_alphabet D
        (transitive_alphabet_subset D E (val_mem_alphabet _ ha))
      by_cases hA : (v : G) * RelLetter.listVal s * a.val ∈ D.fam i
      · by_cases hs0 : s = []
        · subst hs0
          have hmem : a.val ∈ D.fam i := by
            rw [RelLetter.listVal_nil, mul_one] at hA
            exact mem_right_of_mul_mem_subgroup hv hA
          obtain ⟨b, hbE, hbval, hbav⟩ := exists_enlargedLetter D E j (n := n) (by omega) ha hmem
          have hc : ((v * b.val : D.fam i) : G) * RelLetter.listVal ([] : List (RelLetter G Λ)) =
              (v : G) * RelLetter.listVal ([] : List (RelLetter G Λ)) * a.val := by
            simp only [RelLetter.listVal_nil, mul_one, Subgroup.coe_mul, hbval]
          obtain ⟨u, huE, huval, huav, hulen⟩ := ih (v * b.val) [] (by simp) trivial
            (fun h => (h rfl).elim) hw' (by rw [hc]; exact hwav') (by rw [hc]; exact hend')
            (by simp only [List.length_nil] at hlen ⊢; omega)
          refine ⟨b :: u, ?_, ?_, ⟨?_, huav⟩, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hbE
            · exact huE x hx
          · simp only [OsinComponents.listVal_cons, Subgroup.coe_mul, huval, hbval,
              RelLetter.listVal_nil, one_mul]
          · rintro ⟨hc1, hc2⟩
            obtain ⟨h1, h2⟩ := hbav v hc1 hc2
            exact hwav1 ⟨h1, by rw [RelLetter.listVal_nil, mul_one]; exact h2⟩
          · simp only [List.length_cons, List.length_nil] at hulen ⊢
            omega
        · have hout : (v : G) * RelLetter.listVal s ∉ D.fam i := hsout hs0
          have hsHi : RelLetter.listVal s ∉ D.fam i := fun h => hout ((D.fam i).mul_mem hv h)
          have hgHi : RelLetter.listVal s * a.val ∈ D.fam i :=
            mem_right_of_mul_mem_subgroup hv (by rw [← mul_assoc]; exact hA)
          obtain ⟨g, hgval⟩ : ∃ g : D.fam i, (g : G) = RelLetter.listVal s * a.val :=
            ⟨⟨_, hgHi⟩, rfl⟩
          have hball : (g : G) ∈ D.relBall i n := by
            rw [hgval]
            refine ⟨hgHi, s ++ [b'], ?_, ?_, ?_, ?_⟩
            · intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hs x hx
              · rw [List.eq_of_mem_singleton hx]
                exact hb'
            · rw [OsinComponents.listVal_append, OsinComponents.listVal_cons,
                RelLetter.listVal_nil, mul_one, hb'val]
            · rw [OsinComponents.avoidsFrom_append]
              refine ⟨hsav, ⟨?_, trivial⟩⟩
              rintro ⟨-, hm⟩
              exact hsHi (by simpa using hm)
            · simp only [List.length_append, List.length_singleton]
              omega
          have hc : ((v * g : D.fam i) : G) * RelLetter.listVal ([] : List (RelLetter G Λ)) =
              (v : G) * RelLetter.listVal s * a.val := by
            simp only [RelLetter.listVal_nil, mul_one, Subgroup.coe_mul, hgval, mul_assoc]
          obtain ⟨u, huE, huval, huav, hulen⟩ := ih (v * g) [] (by simp) trivial
            (fun h => (h rfl).elim) hw' (by rw [hc]; exact hwav') (by rw [hc]; exact hend')
            (by simp only [List.length_nil]; omega)
          refine ⟨RelLetter.base g :: u, ?_, ?_, ⟨fun h => (h.1 : False), huav⟩, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Or.inr (Or.inl hball)
            · exact huE x hx
          · simp only [OsinComponents.listVal_cons, Subgroup.coe_mul, huval, RelLetter.val, hgval,
              RelLetter.listVal_nil, one_mul, mul_assoc]
          · simp only [List.length_cons, List.length_nil] at hulen ⊢
            omega
      · have hsav' : AvoidsFrom D.fam i (s ++ [b']) 1 := by
          rw [OsinComponents.avoidsFrom_append]
          refine ⟨hsav, ⟨?_, trivial⟩⟩
          rintro ⟨hc, hm⟩
          apply hA
          have hm' : RelLetter.listVal s ∈ D.fam i := by simpa using hm
          have hb'mem : a.val ∈ D.fam i := by
            rw [← hb'val]
            exact val_mem_of_isCompOf D hb' hc
          exact (D.fam i).mul_mem ((D.fam i).mul_mem hv hm') hb'mem
        have hcs : (v : G) * RelLetter.listVal (s ++ [b']) =
            (v : G) * RelLetter.listVal s * a.val := by
          rw [OsinComponents.listVal_append, OsinComponents.listVal_cons, RelLetter.listVal_nil,
            mul_one, hb'val, mul_assoc]
        obtain ⟨u, huE, huval, huav, hulen⟩ := ih v (s ++ [b'])
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hs x hx
            · rw [List.eq_of_mem_singleton hx]
              exact hb')
          hsav' (fun _ => by rw [hcs]; exact hA) hw' (by rw [hcs]; exact hwav')
          (by rw [hcs]; exact hend')
          (by simp only [List.length_append, List.length_singleton]; omega)
        refine ⟨u, huE, ?_, huav, ?_⟩
        · rw [huval, OsinComponents.listVal_append, OsinComponents.listVal_cons,
            OsinComponents.listVal_cons, RelLetter.listVal_nil, mul_one, hb'val, mul_assoc]
        · simp only [List.length_append, List.length_cons, List.length_nil] at hulen ⊢
          omega

/-- **Every relative ball of the transitive structure is the image of a relative ball of the
enlarged structure.** -/
theorem relBall_subset_image (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    (i : Λ) (j : M i) (n : ℕ) :
    (transitiveRelGenSet D E).relBall ⟨i, j⟩ n ⊆
      Subtype.val '' (enlarged D E i n).relBall j n := by
  rintro h ⟨hh, w, hw, hval, hav, hlen⟩
  obtain ⟨e, he, rfl⟩ := (show h ∈ ((E i).fam j).map (D.fam i).subtype from hh)
  obtain ⟨u, huE, huval, huav, hulen⟩ := exists_enlargedWord D E j (n := n) w 1 []
    (by simp) trivial (fun h => (h rfl).elim) hw
    (by
      show AvoidsFrom (transitiveRelGenSet D E).fam ⟨i, j⟩ w ((1 : G) * 1)
      rw [one_mul]
      exact hav)
    (by
      show (1 : G) * 1 * RelLetter.listVal w ∈ D.fam i
      rw [one_mul, one_mul, hval]
      exact e.2)
    (by simpa using hlen)
  refine ⟨e, ⟨he, u, huE, ?_, huav, ?_⟩, rfl⟩
  · rw [RelLetter.listVal_nil, one_mul, hval] at huval
    exact Subtype.ext huval
  · simp only [List.length_nil, zero_add] at hulen
    omega

/-- **Local finiteness of the subfamilies**: the relative balls of the transitive structure are
finite when those of `D` and of every `E i` are. -/
theorem relBall_finite_transitive (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    (hloc : ∀ (i : Λ) (n : ℕ), (D.relBall i n).Finite)
    (hlocE : ∀ (i : Λ) (j : M i) (n : ℕ), ((E i).relBall j n).Finite) :
    ∀ (p : (i : Λ) × M i) (n : ℕ), ((transitiveRelGenSet D E).relBall p n).Finite := by
  rintro ⟨i, j⟩ n
  exact ((RelHyp.relBall_finite_adjoinBase' (E i) (excursionLetters D i n)
    (excursionLetters_inv D i n) (excursionLetters_finite D (hloc i n)) (hlocE i) j n).image
      Subtype.val).subset (relBall_subset_image D E i j n)

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.exists_enlargedWord
#audit_axioms GroupApproximation.GGT.HullLemma35.relBall_finite_transitive
