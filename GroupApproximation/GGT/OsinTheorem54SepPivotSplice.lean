import GroupApproximation.GGT.OsinTheorem54SepSplice
import GroupApproximation.GGT.OsinTheorem54SepEntrance

/-!
# The pivot splice: Lemma 4.9's construction

Osin's Lemma 4.9 compares `S(f,g;D)` with `S(f,h;D)` and `S(g,h;D)`, and the
whole comparison is one construction, drawn in his Figure 6.  A geodesic `p`
from `f` to `g` essentially penetrates a coset `C`; a geodesic `r` from `f` to
`h` penetrates a LATER coset `C'` of `p`; and the head of `p` up to `C'` is
glued to the tail of `r` after `C'` by a single `H_λ`-edge across `C'`:

  `t = p₁ a₁ p₂ e r₂`.

Two facts make `t` geodesic.  Lemma 4.6 says `p` and `r` enter `C'` after the
same number of letters --- the entrance index is the distance from `f` to the
coset, and that number does not know which geodesic measured it --- so the head
and the tail have complementary lengths; and the connecting edge is one letter,
because on a geodesic every component is a single letter.

## Why the depth is not lost

`t` carries the component of `C` UNCHANGED: its vertices agree with `p`'s up to
the splice point, so the span of the component is literally the same group
element and the essentiality of the penetration transfers by identity, not by
an estimate.  That is the point of Osin's route through 4.6, and it is why no
constant enters here: the isolated-component bound was already spent, once, in
Lemma 4.5.

## The seam is vacuous

The one clause that has to be checked is maximality where the head meets the
connector.  If the component of `C` ended exactly at the splice point, the
connector --- an `H_μ`-letter for the pivot's index `μ` --- would extend it, and
the run would not be a component of `t`.  It cannot: `p` itself carries an
`H_μ`-letter at that position, and the component of `C` on `p` is maximal, so
`μ ≠ λ`.  The seam closes with the source geodesic's own maximality clause and
no hypothesis of its own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The head with its connector -/

/-- **The head of `p` followed by the connecting edge is geodesic.**  Its
length is `m + 1`, and that is the distance from `f` to the vertex it reaches,
because `r` is geodesic and reaches that vertex in `m + 1` letters. -/
theorem isGeodesicWord_head_connector (D : RelGenSet G Λ) {f h : G}
    {p r : List (RelLetter G Λ)} (hplet : ∀ b ∈ p, D.IsLetter b)
    (hr : IsGeodesicWord D f h r) {m : ℕ} (hmr : m + 1 ≤ r.length)
    (hmp : m ≤ p.length) {a : RelLetter G Λ} (halet : D.IsLetter a)
    (hav : vertex f p m * a.val = vertex f r (m + 1)) :
    IsGeodesicWord D f (vertex f r (m + 1)) (p.take m ++ [a]) := by
  have hlenp : (p.take m).length = m := by
    rw [List.length_take]
    omega
  have hlena : ([a] : List (RelLetter G Λ)).length = 1 := rfl
  have hlenhead : (p.take m ++ [a]).length = m + 1 := by
    rw [List.length_append, hlenp, hlena]
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with h1 | h1
    · exact hplet b (List.take_subset m p h1)
    · rw [List.mem_singleton.mp h1]
      exact halet
  · rw [listVal_append, listVal_cons, RelLetter.listVal_nil, mul_one, ← mul_assoc,
      ← vertex_eq_mul_listVal_take, hav]
  · rw [hlenhead, wordDist_vertex_eq_index D hr (by omega : m + 1 ≤ r.length)]

/-! ## The splice, and what it carries -/

/-- **Osin's Lemma 4.9 construction.**

`p` is a geodesic from `f` to `g` whose component at `[n, n+1)` essentially
penetrates a coset of `H_λ`; `m > n` is the entrance index of a coset of `H_μ`
penetrated by `p` and by the geodesic `r` from `f` to `h` --- at the same index
on both, which is Lemma 4.6 and is why the two are joined by `hcos` alone.

Then the coset penetrated at `n` separates `f` from `h`. -/
theorem sepSet_of_essentiallyPenetrates_of_lt_pivot (D : RelGenSet G Λ)
    (lam mu : Λ) (Dc : ℕ) {f g h : G} {p r : List (RelLetter G Λ)}
    (hp : IsGeodesicWord D f g p) (hr : IsGeodesicWord D f h r) {n m : ℕ}
    (hnm : n < m) (hess : EssentiallyPenetrates D lam Dc f p n (n + 1))
    (hpiv : IsComp mu p m (m + 1)) (hpivr : IsComp mu r m (m + 1))
    (hcos : (QuotientGroup.mk (vertex f p m) : G ⧸ D.fam mu)
      = QuotientGroup.mk (vertex f r m)) :
    (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam) ∈ sepSet D lam Dc f h := by
  obtain ⟨hcomp, hdeep⟩ := hess
  have hmp : m + 1 ≤ p.length := hpiv.2.1
  have hmr : m + 1 ≤ r.length := hpivr.2.1
  -- the connecting edge, an `H_μ`-letter from `p`'s entrance to `r`'s exit
  have hcos2 : (QuotientGroup.mk (vertex f r m) : G ⧸ D.fam mu)
      = QuotientGroup.mk (vertex f r (m + 1)) :=
    mk_vertex_eq_of_isComp D f hr.1 hpivr
  have hmem : (vertex f p m)⁻¹ * vertex f r (m + 1) ∈ D.fam mu :=
    QuotientGroup.eq.mp (hcos.trans hcos2)
  obtain ⟨a, halet, hav, hacomp⟩ : ∃ a : RelLetter G Λ, D.IsLetter a ∧
      vertex f p m * a.val = vertex f r (m + 1) ∧
      ∀ nu : Λ, a.IsCompOf nu → nu = mu := by
    refine ⟨RelLetter.comp mu ((vertex f p m)⁻¹ * vertex f r (m + 1)), hmem,
      ?_, ?_⟩
    · show vertex f p m * ((vertex f p m)⁻¹ * vertex f r (m + 1))
        = vertex f r (m + 1)
      rw [mul_inv_cancel_left]
    · intro nu hnu
      exact hnu.symm
  -- lengths
  have hlenp : (p.take m).length = m := by
    rw [List.length_take]
    omega
  have hlena : ([a] : List (RelLetter G Λ)).length = 1 := rfl
  have hlenhead : (p.take m ++ [a]).length = m + 1 := by
    rw [List.length_append, hlenp, hlena]
  -- the spliced geodesic
  have hA : IsGeodesicWord D f (vertex f r (m + 1)) (p.take m ++ [a]) :=
    isGeodesicWord_head_connector D hp.1 hr hmr (by omega) halet hav
  have hA' : IsGeodesicWord D (vertex f r 0) (vertex f r (m + 1))
      (p.take m ++ [a]) := by
    rw [vertex_zero]
    exact hA
  have ht := isGeodesicWord_splice D hr (Nat.zero_le (m + 1)) hmr hA'
  rw [List.take_zero, List.nil_append] at ht
  have hlenT : ((p.take m ++ [a]) ++ r.drop (m + 1)).length = r.length := by
    rw [List.length_append, hlenhead, List.length_drop]
    omega
  -- vertices of the splice agree with `p`'s up to the splice point
  have hv1 : ∀ i : ℕ, i ≤ m + 1 →
      vertex f ((p.take m ++ [a]) ++ r.drop (m + 1)) i
        = vertex f (p.take m ++ [a]) i := by
    intro i hi
    exact vertex_append_of_le (p.take m ++ [a]) (r.drop (m + 1)) f i
      (by omega)
  have hv2 : ∀ i : ℕ, i ≤ m → vertex f (p.take m ++ [a]) i = vertex f p i := by
    intro i hi
    rw [vertex_append_of_le (p.take m) [a] f i (by omega)]
    exact vertex_take_eq f p m i hi
  have hvT : ∀ i : ℕ, i ≤ m →
      vertex f ((p.take m ++ [a]) ++ r.drop (m + 1)) i = vertex f p i := by
    intro i hi
    rw [hv1 i (by omega), hv2 i hi]
  -- letters of the splice agree with `p`'s before the splice point
  have hsing : ∀ (k : ℕ) (hk : k < ([a] : List (RelLetter G Λ)).length),
      ([a] : List (RelLetter G Λ))[k]'hk = a := by
    intro k hk
    rw [hlena] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  have hl1 : ∀ (i : ℕ) (hi : i < m + 1)
      (hiT : i < ((p.take m ++ [a]) ++ r.drop (m + 1)).length),
      ((p.take m ++ [a]) ++ r.drop (m + 1))[i]'hiT
        = (p.take m ++ [a])[i]'(by omega) := by
    intro i hi hiT
    exact List.getElem_append_left (by omega)
  have hl2 : ∀ (i : ℕ) (hi : i < m) (hi2 : i < (p.take m ++ [a]).length),
      (p.take m ++ [a])[i]'hi2 = p[i]'(by omega) := by
    intro i hi hi2
    rw [List.getElem_append_left (show i < (p.take m).length by omega)]
    simp
  have hlm : ∀ hi2 : m < (p.take m ++ [a]).length,
      (p.take m ++ [a])[m]'hi2 = a := by
    intro hi2
    rw [List.getElem_append_right (show (p.take m).length ≤ m by omega)]
    exact hsing _ _
  -- the component of the separating coset survives the splice
  have hcompT : IsComp lam ((p.take m ++ [a]) ++ r.drop (m + 1)) n (n + 1) := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj1 hj2 hjT
      rw [hl1 j (by omega) hjT, hl2 j (by omega) (by omega)]
      exact hcomp.2.2.1 j hj1 hj2 (by omega)
    · intro j hj hjT
      rw [hl1 j (by omega) hjT, hl2 j (by omega) (by omega)]
      exact hcomp.2.2.2.1 j hj (by omega)
    · intro hk
      rcases Nat.lt_or_ge (n + 1) m with hlt | hge
      · rw [hl1 (n + 1) (by omega) hk,
          hl2 (n + 1) hlt (by omega)]
        exact hcomp.2.2.2.2 (by omega)
      · have hnm' : n + 1 = m := by omega
        subst hnm'
        rw [hl1 (n + 1) (by omega) hk, hlm (by omega)]
        intro hcontra
        have hml : lam = mu := hacomp lam hcontra
        subst hml
        exact hcomp.2.2.2.2 (by omega)
          (hpiv.2.2.1 (n + 1) (le_refl (n + 1)) (by omega) (by omega))
  refine ⟨(p.take m ++ [a]) ++ r.drop (m + 1), n, n + 1, ht,
    ⟨hcompT, ?_⟩, ?_⟩
  · rw [hvT n (by omega), hvT (n + 1) (by omega)]
    exact hdeep
  · rw [hvT n (by omega)]

end OsinComponents
end GGT
end GroupApproximation
