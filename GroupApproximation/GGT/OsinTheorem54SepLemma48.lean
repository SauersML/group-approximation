import GroupApproximation.GGT.OsinTheorem54SepLemma45
import GroupApproximation.GGT.OsinTheorem54SepEntrance
import GroupApproximation.GGT.OsinTheorem54SepSixBound

/-!
# Osin's Lemma 4.8, discharged

> For any `f, g ∈ G`, `⪯` is a linear order on `S(f,g;D)` and every geodesic `p`
> from `f` to `g` penetrates all `(f,g,D)`-separating cosets according to the
> order `⪯`.

Osin proves this in one line: it "follows immediately from Lemmas 4.5 and 4.6".
Both halves of `LemmaFourEight` are that line, spelled out.

## The penetration half is Lemma 4.5 at an empty second segment

Lemma 4.5 says the two-segment path `f → h → g` penetrates every separating
coset, whichever geodesics the two segments are.  Take `h := g` and the second
segment empty.  The two-segment path is then the given geodesic itself, and the
disjunction 4.5 concludes has its right branch about the empty word, where
`IsComp` asks for `i < k ≤ 0`.  So the left branch holds, which is exactly
"this geodesic penetrates the coset".

Nothing is lost in the degeneration: 4.5's polygon is already carried as a
quadrilateral with an empty first side, so the second empty side costs nothing
beyond what `isQuasiGeodesicPolygon_triangle` already absorbs, and the constant
enters exactly once, at 4.5's isolation step, through `C * 4 ≤ Dc`.

## The ordering half is Lemma 4.6, and it gives more than an order

Lemma 4.6 pins the entrance index of a coset to the distance from `f` to that
coset, and the distance does not know which geodesic measured it.  So two
geodesics out of `f` penetrating one coset penetrate it at the SAME index
(`entrance_eq_of_isComp`), not merely in the same relative position.  The
ordering clause `i < j ↔ i' < j'` then falls out of `i = i'` and `j = j'`.

That is stronger than what Osin states and it is worth naming
(`penetratesAt_index_eq`): it is the form Lemma 4.9's splice runs on, where the
head of one geodesic is joined to the tail of another and the lengths have to
match on the nose.

Note also which hypotheses each half spends.  The isolated-component bound is
spent only by the penetration half; the ordering half is pure 4.6 and needs no
constant at all.  So `LemmaFourEight` costs exactly what Lemma 4.5 costs.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The empty geodesic -/

/-- **The empty word is a geodesic from a point to itself.**  This is the second
segment of Lemma 4.5's two-segment path in the degenerate case that turns 4.5
into 4.8. -/
theorem isGeodesicWord_nil (D : RelGenSet G Λ) (g : G) :
    IsGeodesicWord D g g ([] : List (RelLetter G Λ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp at ha
  · rw [RelLetter.listVal_nil, mul_one]
  · rw [List.length_nil, wordDist_self]

/-! ## The penetration half -/

/-- **Every geodesic penetrates every separating coset.**  Lemma 4.5 at
`h := g` with an empty second segment: its right branch would be a component of
the empty word, which asks for `i < k ≤ 0`. -/
theorem penetrates_of_mem_sepSet_geodesic (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) {c : G ⧸ D.fam lam}
    (hc : c ∈ sepSet D lam Dc f g) :
    ∃ i k : ℕ, IsComp lam w i k ∧ c = QuotientGroup.mk (vertex f w i) := by
  rcases penetrates_of_mem_sepSet D lam hsymm hbnd hDc hw
      (isGeodesicWord_nil D g) hc with ⟨m, n, hcomp, hmk⟩ | ⟨_, _, hcomp, _⟩
  · exact ⟨m, n, hcomp, hmk.symm⟩
  · exfalso
    have hlt := hcomp.1
    have hle := hcomp.2.1
    rw [List.length_nil] at hle
    omega

/-! ## The ordering half -/

/-- **Two geodesics out of one point penetrate a coset at the same index.**

Lemma 4.6 identifies the entrance index with the distance from `f` to the
coset, and that number is a property of the coset, not of the geodesic.  Note
the endpoints `g` and `g'` are allowed to differ: nothing here compares the two
geodesics beyond their common origin. -/
theorem penetratesAt_index_eq (D : RelGenSet G Λ) (lam : Λ) {Dc : ℕ}
    {f g g' : G} {w w' : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) (hw' : IsGeodesicWord D f g' w')
    {c : G ⧸ D.fam lam} {i i' : ℕ}
    (hi : PenetratesAt D lam Dc f w i c)
    (hi' : PenetratesAt D lam Dc f w' i' c) :
    i = i' := by
  obtain ⟨⟨k, hcomp⟩, hci⟩ := hi
  obtain ⟨⟨k', hcomp'⟩, hci'⟩ := hi'
  exact entrance_eq_of_isComp D lam hw hw' hcomp hcomp' (hci.symm.trans hci')

/-! ## Lemma 4.8 -/

/-- **Osin, Lemma 4.8**, both halves, from the isolated-component bound at
`n ≤ 6` and `C * 4 ≤ Dc`.

The first conjunct is Lemma 4.5 with an empty second segment; the second is
Lemma 4.6, which gives equality of the two entrance indices and so the ordering
clause with room to spare. -/
theorem lemmaFourEight_of_bound (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) :
    LemmaFourEight D lam Dc := by
  refine ⟨fun f g w hw c hc =>
    penetrates_of_mem_sepSet_geodesic D lam hsymm hbnd hDc hw hc, ?_⟩
  intro f g w w' hw hw' c c' i j i' j' hi hj hi' hj'
  have hii' := penetratesAt_index_eq D lam hw hw' hi hi'
  have hjj' := penetratesAt_index_eq D lam hw hw' hj hj'
  omega

/-- **Lemma 4.8 for every peripheral index at once**, the shape the assembly's
`h48` binder asks for. -/
theorem lemmaFourEight_forall_of_bound (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) :
    ∀ lam : Λ, LemmaFourEight D lam Dc :=
  fun lam => lemmaFourEight_of_bound D lam hsymm hbnd hDc

/-! ## From four-point hyperbolicity -/

/-- **Lemma 4.8 holds for every large enough `Dc`**, from `hsymm` and four-point
hyperbolicity of the relative graph alone.

This is the form the assembly wants: the constant `C` comes out of the §4.2
bound first, and `Dc` is chosen afterwards with `C` in hand, so the threshold
`C * 4 ≤ Dc` --- Osin's `D ≥ 3C` of Remark 4.4, widened by the quadrilateral
carriage of the triangle --- costs nothing. -/
theorem exists_lemmaFourEight_of_fourPointHyperbolic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ ∀ Dc : ℕ, C * 4 ≤ Dc → ∀ lam : Λ,
      LemmaFourEight D lam Dc := by
  obtain ⟨C, hCpos, hbnd⟩ :=
    sixBound_one_of_fourPointHyperbolic D hsymm hδ 0 le_rfl
  exact ⟨C, hCpos, fun Dc hDc => lemmaFourEight_forall_of_bound D hsymm hbnd hDc⟩

end OsinComponents
end GGT
end GroupApproximation
