import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# Osin's `Z`, and the two ball inclusions it turns on

Lemma 5.8 proves local finiteness of the ENLARGED relative metrics by a change
of alphabet.  Put

  `Z = X ∪ ⋃_λ {h ∈ H_λ : d̂^X_λ(1,h) ≤ D}`

and read the same paths in `Γ(G, Z ⊔ ℋ)`.  Every element added to the base
already lay in some `H_λ`, so the alphabet's CARRIER does not change at all:
`Z ∪ ⋃H_λ = X ∪ ⋃H_λ`.  The word metric of the relative Cayley graph is
therefore literally the same, and with it four-point hyperbolicity --- there is
nothing to transfer.  What does change is which letters are peripheral, and
that is exactly what `relBall` sees: an element of `H_λ` reached by a `Z`-letter
crosses no edge of `Γ_{H_λ}`, while the same element read as an `ℋ`-letter
does.  Osin's own phrasing: some edges of `Γ(G, X ⊔ ℋ)` are DOUBLED in
`Γ(G, Z ⊔ ℋ)`.

## What is proved here, and what it costs

Both inclusions between the two relative balls.

* `D.relBall lam k ⊆ (relGenSetZ D Dc).relBall lam k` --- free: every letter of
  `D` is a letter of `D_Z` and `AvoidsFrom` reads only the family, which is
  unchanged.
* `(relGenSetZ D Dc).relBall lam k ⊆ D.relBall lam (Dc * k)` --- the substance.
  Each `Z`-letter is replaced by a path of the original alphabet, and the whole
  point is WHERE the case split falls.

It is not on the letter but on the VERTEX.  A new base letter `x` lies in some
`H_μ`; if `μ ≠ λ` the single `ℋ`-letter `comp μ x` replaces it and can never
traverse `Γ_{H_λ}`.  If `μ = λ` there are two cases, and only the first is the
one Osin's `Z` was built for:

* the current vertex is OUTSIDE `H_λ` --- then the single `ℋ`-letter
  `comp λ x` is admissible after all, since traversing `Γ_{H_λ}` requires the
  vertex to lie in `H_λ`.  Cost one.
* the current vertex is INSIDE `H_λ` --- then the letter's own `d̂^X_λ`-word of
  length at most `Dc` is used, and its admissibility transports along
  `avoidsFrom_smul_left`, whose hypothesis is exactly that the translating
  element lies in `H_λ`.  Cost `Dc`.

Reading the split off the letter instead of the vertex is what makes the lemma
look false: `avoidsFrom` is NOT translation invariant in general, and the
`H_λ`-membership of the vertex is the whole of what licenses the one case where
it is used.

## Why this avoids a citation

Osin gets local finiteness of `d̂^Z` from his Lemma 5.7 (Dahmani--Guirardel--
Osin's Corollary 4.27), which is a citation and is carried in this tree as the
unproved `DGOCorollary427`.  We need only clause (b), and the inclusion above
gives it outright: `relBall^Z(λ,k) ⊆ relBall^X(λ, Dc·k)`, so local finiteness
of the original metrics --- clause (b) of the hypothesis Theorem 5.4 already
makes --- carries over.  The finiteness of `Λ`, which Osin uses to know
`|Z \ X| < ∞`, is not needed either.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The enlarged base -/

/-- **The carrier is unchanged.**  Every element added to the base already lies
in the family, so the union that forms the alphabet is the same set. -/
theorem base_union_fam_union_relBall (D : RelGenSet G Λ) (Dc : ℕ) :
    (D.base ∪ {x : G | ∃ lam : Λ, x ∈ D.relBall lam Dc}) ∪
        ⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)
      = D.base ∪ ⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ((hx | ⟨mu, hmu⟩) | hx)
    · exact Or.inl hx
    · exact Or.inr (Set.mem_iUnion.mpr ⟨mu, hmu.1⟩)
    · exact Or.inr hx
  · rintro x (hx | hx)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx

/-- **Osin's `Z`**: the base enlarged by the `d̂_λ`-balls of radius `Dc`. -/
def relGenSetZ (D : RelGenSet G Λ) (Dc : ℕ) : RelGenSet G Λ where
  base := D.base ∪ {x : G | ∃ lam : Λ, x ∈ D.relBall lam Dc}
  fam := D.fam
  symmetricGenerating := by
    rw [base_union_fam_union_relBall D Dc]
    exact D.symmetricGenerating

@[simp] theorem fam_relGenSetZ (D : RelGenSet G Λ) (Dc : ℕ) :
    (relGenSetZ D Dc).fam = D.fam := rfl

/-- **The two alphabets are the same alphabet.**  So the word metric of the
relative Cayley graph, and every property of it, is unchanged. -/
theorem alphabet_carrier_relGenSetZ (D : RelGenSet G Λ) (Dc : ℕ) :
    (relGenSetZ D Dc).alphabet.carrier = D.alphabet.carrier :=
  base_union_fam_union_relBall D Dc

/-- Every letter of `D` is a letter of `D_Z`. -/
theorem isLetter_relGenSetZ (D : RelGenSet G Λ) (Dc : ℕ)
    {a : RelLetter G Λ} (h : D.IsLetter a) : (relGenSetZ D Dc).IsLetter a := by
  cases a with
  | base x => exact Or.inl h
  | comp mu x => exact h

/-! ## The easy inclusion -/

/-- **`d̂^Z_λ ≤ d̂^X_λ`.**  The same word serves, since `AvoidsFrom` reads only
the family. -/
theorem relBall_subset_relBall_relGenSetZ (D : RelGenSet G Λ) (Dc : ℕ)
    (lam : Λ) (k : ℕ) :
    D.relBall lam k ⊆ (relGenSetZ D Dc).relBall lam k := by
  rintro h ⟨hf, w, hlet, hval, hav, hlen⟩
  exact ⟨hf, w, fun a ha => isLetter_relGenSetZ D Dc (hlet a ha), hval, hav, hlen⟩

/-! ## The substitution -/

/-- **Every `D_Z`-path is a `D`-path `Dc` times as long**, avoidance and
endpoints kept.  The induction carries the vertex, because the replacement of a
new base letter depends on whether that vertex lies in `H_λ`. -/
theorem exists_word_of_word_relGenSetZ (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (lam : Λ) :
    ∀ (w : List (RelLetter G Λ)) (v : G),
      (∀ a ∈ w, (relGenSetZ D Dc).IsLetter a) → AvoidsFrom D.fam lam w v →
      ∃ u : List (RelLetter G Λ), (∀ a ∈ u, D.IsLetter a) ∧
        RelLetter.listVal u = RelLetter.listVal w ∧
        AvoidsFrom D.fam lam u v ∧ u.length ≤ Dc * w.length := by
  intro w
  induction w with
  | nil =>
      intro v _ _
      refine ⟨[], ?_, rfl, trivial, ?_⟩
      · intro b hb
        simp at hb
      · simp
  | cons a t ih =>
      intro v hlet havoid
      obtain ⟨hfirst, hrest⟩ := havoid
      obtain ⟨ut, hutlet, hutval, hutavoid, hutlen⟩ :=
        ih (v * a.val) (fun b hb => hlet b (List.mem_cons_of_mem a hb)) hrest
      obtain ⟨ua, hualet, huaval, huaavoid, hualen⟩ :
          ∃ ua : List (RelLetter G Λ), (∀ b ∈ ua, D.IsLetter b) ∧
            RelLetter.listVal ua = a.val ∧ AvoidsFrom D.fam lam ua v ∧
            ua.length ≤ Dc := by
        by_cases hDa : D.IsLetter a
        · refine ⟨[a], ?_, ?_, ⟨hfirst, trivial⟩, ?_⟩
          · intro b hb
            rw [List.mem_singleton.mp hb]
            exact hDa
          · rw [listVal_cons, RelLetter.listVal_nil, mul_one]
          · rw [List.length_cons, List.length_nil]
            omega
        · cases a with
          | comp mu x => exact absurd (hlet _ List.mem_cons_self) hDa
          | base x =>
              have hx : x ∈ D.base ∪ {y : G | ∃ mu : Λ, y ∈ D.relBall mu Dc} :=
                hlet _ List.mem_cons_self
              rcases hx with hx | ⟨mu, hmu⟩
              · exact absurd hx hDa
              · have hxfam : x ∈ D.fam mu := hmu.1
                by_cases hml : mu = lam
                · by_cases hv : v ∈ D.fam lam
                  · obtain ⟨-, u, hulet, huval, huavoid, hulen⟩ := hmu
                    rw [hml] at huavoid
                    refine ⟨u, hulet, huval, ?_, hulen⟩
                    have hshift :=
                      (avoidsFrom_smul_left (H := D.fam) (lam := lam) hv u 1).mpr
                        huavoid
                    rwa [mul_one] at hshift
                  · refine ⟨[RelLetter.comp mu x], ?_, ?_, ?_, ?_⟩
                    · intro b hb
                      rw [List.mem_singleton.mp hb]
                      exact hxfam
                    · have hcb : (RelLetter.comp mu x : RelLetter G Λ).val
                          = (RelLetter.base x : RelLetter G Λ).val := rfl
                      rw [listVal_cons, RelLetter.listVal_nil, mul_one, hcb]
                    · refine ⟨?_, trivial⟩
                      rintro ⟨-, hvmem⟩
                      exact hv hvmem
                    · rw [List.length_cons, List.length_nil]
                      omega
                · refine ⟨[RelLetter.comp mu x], ?_, ?_, ?_, ?_⟩
                  · intro b hb
                    rw [List.mem_singleton.mp hb]
                    exact hxfam
                  · have hcb : (RelLetter.comp mu x : RelLetter G Λ).val
                        = (RelLetter.base x : RelLetter G Λ).val := rfl
                    rw [listVal_cons, RelLetter.listVal_nil, mul_one, hcb]
                  · refine ⟨?_, trivial⟩
                    rintro ⟨hc, -⟩
                    exact hml hc
                  · rw [List.length_cons, List.length_nil]
                    omega
      refine ⟨ua ++ ut, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with h | h
        · exact hualet b h
        · exact hutlet b h
      · rw [listVal_append, huaval, hutval, listVal_cons]
      · rw [avoidsFrom_append]
        refine ⟨huaavoid, ?_⟩
        rw [huaval]
        exact hutavoid
      · rw [List.length_append, List.length_cons, Nat.mul_succ]
        omega

/-! ## The inclusion that carries local finiteness -/

/-- **`d̂^X_λ ≤ Dc · d̂^Z_λ`.**  Local finiteness of the original relative
metrics therefore gives it for `Z`, with no appeal to Corollary 4.27. -/
theorem relBall_relGenSetZ_subset (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc)
    (lam : Λ) (k : ℕ) :
    (relGenSetZ D Dc).relBall lam k ⊆ D.relBall lam (Dc * k) := by
  rintro h ⟨hf, w, hlet, hval, hav, hlen⟩
  obtain ⟨u, hulet, huval, huavoid, hulen⟩ :=
    exists_word_of_word_relGenSetZ D hDc lam w 1 hlet hav
  refine ⟨hf, u, hulet, ?_, huavoid, ?_⟩
  · rw [huval, hval]
  · have hmul : Dc * w.length ≤ Dc * k := Nat.mul_le_mul_left Dc hlen
    omega

/-- **Local finiteness passes to `Z`.** -/
theorem relBall_relGenSetZ_finite (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc)
    (hfin : ∀ (lam : Λ) (n : ℕ), (D.relBall lam n).Finite) (lam : Λ) (k : ℕ) :
    ((relGenSetZ D Dc).relBall lam k).Finite :=
  (hfin lam (Dc * k)).subset (relBall_relGenSetZ_subset D hDc lam k)

end OsinComponents
end GGT
end GroupApproximation
