import GroupApproximation.GGT.OsinTheorem54SepLemma45
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GGT.OsinTheorem54SepFinite

/-!
# The short connector between two geodesic entrances

The two triangular estimates used in Osin's equation (38) are instances of one
fact.  If two geodesics leaving the same vertex penetrate the same peripheral
coset, the element joining their entrance points lies in the radius-`Dc`
relative ball, once `Dc` is past the constant in Lemma 4.2.

The proof uses Osin's Lemmas 4.5 and 4.6 exactly as intended.  If the connector
were outside the ball, its one-edge geodesic would make the coset separating
between the two entrance points.  Lemma 4.5, applied through the common origin,
would then put that coset on one of the two geodesic prefixes.  On the reversed
first prefix Lemma 4.6 forces the new component to start at index zero, contrary
to maximality of the original component.  On the second prefix it forces an
entrance index at least the original one, although the prefix ends there.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A prefix of a geodesic word is geodesic between its endpoint vertices.** -/
theorem isGeodesicWord_take (D : RelGenSet G Λ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {i : ℕ}
    (hi : i ≤ w.length) :
    IsGeodesicWord D f (vertex f w i) (w.take i) := by
  have h := isGeodesicWord_segment D hw (i := 0) (j := i) (Nat.zero_le i) hi
  simpa using h

/-- **Entrance points of one coset on two geodesics have a short connector.**

This is the connector estimate used twice in the non-isolated branch of
equation (38).  The constant is the same `C * 4 ≤ Dc` used by Lemma 4.5, whose
geodesic triangle is represented as a degenerate quadrilateral. -/
theorem entranceConnector_mem_relBall_of_bound (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {f g h : G}
    {p q : List (RelLetter G Λ)} (hp : IsGeodesicWord D f g p)
    (hq : IsGeodesicWord D f h q) {i i' j j' : ℕ}
    (hpi : IsComp lam p i i') (hqj : IsComp lam q j j')
    (hcos : (QuotientGroup.mk (vertex f p i) : G ⧸ D.fam lam) =
      QuotientGroup.mk (vertex f q j)) :
    (vertex f p i)⁻¹ * vertex f q j ∈ D.relBall lam Dc := by
  let u := vertex f p i
  let v := vertex f q j
  let e := u⁻¹ * v
  have hefam : e ∈ D.fam lam := by
    exact QuotientGroup.eq.mp hcos
  by_cases he1 : e = 1
  · rw [show (vertex f p i)⁻¹ * vertex f q j = e from rfl, he1]
    exact one_mem_relBall D lam Dc
  have healpha : e ∈ D.alphabet.carrier :=
    Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hefam⟩)
  have huv : u * e = v := by
    dsimp [e, u, v]
    group
  have hedge : IsGeodesicWord D u v [RelLetter.comp lam e] := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have hae : a = RelLetter.comp lam e := List.eq_of_mem_singleton ha
      subst hae
      exact hefam
    · simpa [RelLetter.listVal, RelLetter.val] using huv
    · rw [List.length_singleton, ← huv]
      exact (CayleyGeodesicModel.wordDist_step_eq_one D.alphabet u healpha he1).symm
  have hsingle : IsComp lam [RelLetter.comp lam e] 0 1 := by
    refine ⟨by omega, by simp, ?_, ?_, ?_⟩
    · intro t ht0 ht1 ht
      have htzero : t = 0 := by omega
      subst htzero
      rfl
    · intro t ht
      omega
    · intro ht
      simp at ht
  by_contra hedeep
  have hsep : (QuotientGroup.mk u : G ⧸ D.fam lam) ∈ sepSet D lam Dc u v := by
    refine ⟨[RelLetter.comp lam e], 0, 1, hedge, ⟨hsingle, ?_⟩, ?_⟩
    · simpa [vertex_zero, vertex_cons_succ, RelLetter.val, u, v, e] using hedeep
    · simp [vertex_zero]
  have hip : i ≤ p.length := le_trans (le_of_lt hpi.1) hpi.2.1
  have hjq : j ≤ q.length := le_trans (le_of_lt hqj.1) hqj.2.1
  let P := p.take i
  let Q := q.take j
  have hP : IsGeodesicWord D f u P := by
    simpa [P, u] using isGeodesicWord_take D hp hip
  have hQ : IsGeodesicWord D f v Q := by
    simpa [Q, v] using isGeodesicWord_take D hq hjq
  have hrevP : IsGeodesicWord D u f (revWord P) :=
    isGeodesicWord_revWord D hsymm hP
  rcases penetrates_of_mem_sepSet D lam hsymm hbnd hDc hrevP hQ hsep with
      ⟨m, n, hm, hmcos⟩ | ⟨m, n, hm, hmcos⟩
  · have hm0 : m = 0 := by
      have hmle := entrance_le_of_mem_coset D lam hrevP hm hmcos.symm
      rw [wordDist_self] at hmle
      omega
    subst hm0
    have hnpos : 0 < (revWord P).length := lt_of_lt_of_le hm.1 hm.2.1
    have hletter : ((revWord P)[0]'hnpos).IsCompOf lam :=
      hm.2.2.1 0 le_rfl hm.1 hnpos
    have hPlen : P.length = i := by simp [P, hip]
    have hi0 : 0 < i := by rw [length_revWord, hPlen] at hnpos; exact hnpos
    have hlastP : P.length - 1 < P.length := by omega
    have hlast :=
      (isCompOf_getElem_revWord' P lam hnpos hlastP (by omega)).mp hletter
    have hlastp : i - 1 < p.length := by omega
    have htake : P[P.length - 1]'hlastP = p[i - 1]'hlastp := by
      simp [P, hPlen]
    rw [htake] at hlast
    exact hpi.2.2.2.1 (i - 1) (by omega) hlastp hlast
  · have hQlen : Q.length = j := by simp [Q, hjq]
    have hmj : m < j := by
      have hmn := hm.1
      have hnQ := hm.2.1
      omega
    have hmQ : m ≤ Q.length := by omega
    have hvertex : vertex f Q m = vertex f q m :=
      vertex_take_eq f q j m (by omega)
    have hsame :
        (QuotientGroup.mk (vertex f Q m) : G ⧸ D.fam lam) =
          QuotientGroup.mk (vertex f q j) := hmcos.trans hcos
    have hjle := entrance_le_of_mem_coset D lam hq hqj (by simpa [hvertex] using hsame)
    rw [← hvertex, wordDist_vertex_eq_index D hQ hmQ] at hjle
    omega

end OsinComponents
end GGT
end GroupApproximation
