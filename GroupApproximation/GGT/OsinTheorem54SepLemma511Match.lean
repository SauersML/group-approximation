import GroupApproximation.GGT.OsinTheorem54SepLemma511Intersection
import GroupApproximation.GGT.OsinTheorem54SepGeodesicSides
import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral
import GroupApproximation.GGT.OsinTheorem54SepCorner45

/-!
# The four-gon matching step in Osin's Lemma 5.11

This module proves the last geometric dichotomy behind equation (38).  For the
two occurrences of a shared peripheral coset on `p` and on `k p`, join their
entrance points by one peripheral edge and complete the quadrilateral with a
geodesic from `1` to `k`.

If the joining edge is isolated, Lemma 4.2 bounds it.  Otherwise its connected
component cannot lie on either geodesic prefix: Lemma 4.6 would put an entrance
strictly before the given entrance.  Thus it lies on the fourth side, the
geodesic from `1` to `k`.  The only corner case is when the joining edge merges
directly into the reversed fourth side; then that terminal component is already
the required match.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The isolated-edge/matching-component dichotomy of equation (38).** -/
theorem lemma511FourGonMatchAlternative_of_bound (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) : Lemma511FourGonMatchAlternative D Dc := by
  classical
  intro lam k z p i i' j j' hp hi hj hcos hnot
  let u := vertex (1 : G) p i
  let v := vertex k p j
  let e := u⁻¹ * v
  have hefam : e ∈ D.fam lam := QuotientGroup.eq.mp hcos
  by_cases he1 : e = 1
  · left
    simpa [u, v, e, he1] using one_mem_relBall D lam Dc
  obtain ⟨s, hs⟩ := existsGeodesicWord D 1 k
  have hip : i ≤ p.length := le_trans (le_of_lt hi.1) hi.2.1
  have hjp : j ≤ p.length := le_trans (le_of_lt hj.1) hj.2.1
  let P := p.take i
  let Q := p.take j
  let E : List (RelLetter G Λ) := [RelLetter.comp lam e]
  let R := revWord Q
  let W := P ++ E ++ R ++ revWord s
  have hPlen : P.length = i := by simp [P, hip]
  have hQlen : Q.length = j := by simp [Q, hjp]
  have hRlen : R.length = j := by simp [R, hQlen, length_revWord]
  have hP : IsGeodesicWord D 1 u P := by
    simpa [P, u] using isGeodesicWord_take D hp hip
  have hQ : IsGeodesicWord D 1 (vertex (1 : G) p j) Q := by
    simpa [Q] using isGeodesicWord_take D hp hjp
  have hR : IsGeodesicWord D 1 (RelLetter.listVal R) R := by
    exact isGeodesicWord_one_of D
      (isGeodesicWord_revWord D hsymm hQ)
  have healpha : e ∈ D.alphabet.carrier :=
    Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hefam⟩)
  have huv : u * e = v := by dsimp [e, u, v]; group
  have hE : IsGeodesicWord D 1 e E := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have hae : a = RelLetter.comp lam e := by simpa [E] using ha
      subst hae
      exact hefam
    · simp [E, RelLetter.listVal, RelLetter.val]
    · simp only [E, List.length_singleton]
      have hstep := CayleyGeodesicModel.wordDist_step_eq_one D.alphabet 1 healpha he1
      simpa using hstep.symm
  have hS : IsGeodesicWord D 1 (RelLetter.listVal s) s :=
    isGeodesicWord_one_of D hs
  have hvertexkj : k * vertex (1 : G) p j = v := by
    simpa [v] using (vertex_mul_left k 1 p j).symm
  have hclose : RelLetter.listVal s =
      RelLetter.listVal P * RelLetter.listVal E * RelLetter.listVal R := by
    have hPv : RelLetter.listVal P = u := by simpa [u] using hP.2.1
    have hQv : RelLetter.listVal Q = vertex (1 : G) p j := by simpa using hQ.2.1
    have hRv : RelLetter.listVal R = (RelLetter.listVal Q)⁻¹ := by
      simp [R, listVal_revWord]
    have hSv : RelLetter.listVal s = k := by simpa using hs.2.1
    have hEval : RelLetter.listVal E = e := by
      dsimp [E]
      simp only [listVal_singleton, RelLetter.val]
    have hkexpr : k = u * e * (vertex (1 : G) p j)⁻¹ := by
      calc
        k = v * (vertex (1 : G) p j)⁻¹ := by
          rw [← hvertexkj]
          group
        _ = u * e * (vertex (1 : G) p j)⁻¹ := by rw [huv]
    calc
      RelLetter.listVal s = k := hSv
      _ = u * e * (vertex (1 : G) p j)⁻¹ := hkexpr
      _ = RelLetter.listVal P * RelLetter.listVal E * RelLetter.listVal R := by
        rw [hPv, hEval, hRv, hQv]
  have hpoly : IsQuasiGeodesicPolygon D 1 0 4 1 W := by
    have h := isQuasiGeodesicPolygon_fourGon_of_geodesic D hsymm P E R s
      (isGeodesicWord_one_of D hP) (isGeodesicWord_one_of D hE) hR hS hclose
    simpa [W] using h
  have hEsingle : IsComp lam E 0 1 := by
    refine ⟨by omega, by simp [E], ?_, ?_, ?_⟩
    · intro t ht0 ht1 ht
      have htzero : t = 0 := by omega
      subst htzero
      rfl
    · intro t ht
      omega
    · intro ht
      simp [E] at ht
  have hWlen : W.length = P.length + E.length + R.length + s.length := by
    simp [W, length_revWord, List.length_append, Nat.add_assoc]
  by_cases hpost : ∀ hlt : P.length + 1 < W.length,
      ¬ (W[P.length + 1]'hlt).IsCompOf lam
  · have hWcomp : IsComp lam W P.length (P.length + 1) := by
      refine ⟨by omega, ?_, ?_, ?_, hpost⟩
      · rw [hWlen]
        simp [E]
        omega
      · intro t ht0 ht1 htW
        have ht : t = P.length := by omega
        subst ht
        have hget : W[P.length]'htW = E[0]'(by simp [E]) := by
          simpa [W] using
            (getElem_fourGon_q P E R s (j := 0) (by simp [E]) rfl
              (by simpa [W] using htW))
        rw [hget]
        rfl
      · intro t hEq htW hcomp
        have hPpos : 0 < P.length := by omega
        have ht : t = P.length - 1 := by omega
        subst ht
        have hlastP : P.length - 1 < P.length := by omega
        have hlastp : i - 1 < p.length := by omega
        have hget : W[P.length - 1]'htW = P[P.length - 1]'hlastP := by
          simp [W, List.getElem_append_left, hlastP]
        rw [hget] at hcomp
        have htake : P[P.length - 1]'hlastP = p[i - 1]'hlastp := by
          simp [P, hPlen]
        rw [htake] at hcomp
        exact hi.2.2.2.1 (i - 1) (by omega) hlastp hcomp
    by_cases hiso : IsIsolated D.fam lam 1 W P.length
    · left
      have hb := hbnd 4 (by omega) 1 W hpoly lam P.length (P.length + 1)
        hWcomp hiso
      have hv0 := vertex_fourGon_side P E R s 1 (i := 0) (by simp [E])
      have hv1 := vertex_fourGon_side P E R s 1 (i := 1) (by simp [E])
      have hPv : RelLetter.listVal P = u := by simpa [u] using hP.2.1
      have hE1 : vertex (1 : G) E 1 = e := by simp [E, RelLetter.val]
      have hE0 : vertex (1 : G) E 0 = 1 := by simp
      rw [show P.length = P.length + 0 by omega, hv0, hv1, hPv, hE0,
        hE1, one_mul, mul_one, huv] at hb
      exact relBall_mono_radius D lam hDc hb
    · have hstart : IsCompStart lam W P.length := ⟨P.length + 1, hWcomp⟩
      obtain ⟨n, hnne, hnstart, hcases, x, hx, hxeq⟩ :=
        exists_other_component_fourGon_general D lam P E R s
          (i := 0) (by simp [E]) (by simpa [W] using hstart) (by simpa [W] using hiso)
      have hvertex0 : RelLetter.listVal P * vertex (1 : G) E 0 = u := by
        have hPv : RelLetter.listVal P = u := by simpa [u] using hP.2.1
        simp [hPv]
      have hcosn :
          (QuotientGroup.mk u : G ⧸ D.fam lam) = QuotientGroup.mk (vertex 1 W n) := by
        apply QuotientGroup.eq.mpr
        have hx' : u * x = vertex 1 W n := by
          calc
            u * x = (RelLetter.listVal P * vertex (1 : G) E 0) * x := by
              rw [hvertex0]
            _ = vertex 1 W n := by simpa [W] using hxeq
        rw [← hx']
        simpa using hx
      rcases hcases with hnP | hnE | hnR | hnS
      · have hvn : vertex 1 W n = vertex 1 p n := by
          rw [show W = P ++ (E ++ R ++ revWord s) from by simp [W, List.append_assoc],
            vertex_append_of_le P (E ++ R ++ revWord s) 1 n (by omega),
            vertex_take_eq 1 p i n (by omega)]
        have hle := entrance_le_of_mem_coset D lam hp hi
          (y := vertex 1 p n) (by
          rw [← hvn]
          exact hcosn.symm)
        rw [wordDist_vertex_eq_index D hp (by omega)] at hle
        omega
      · obtain ⟨t, ht, hnt⟩ := hnE
        have ht1 : t = 1 := by
          have htle : t ≤ 1 := by simpa [E] using ht
          have htne : t ≠ 0 := by
            intro ht0
            subst t
            exact hnne (by simpa using hnt)
          omega
        subst t
        have hn : n = P.length + 1 := by simpa using hnt
        subst n
        obtain ⟨n', hn'⟩ := hnstart
        have hlt : P.length + 1 < W.length := lt_of_lt_of_le hn'.1 hn'.2.1
        have hc := hn'.2.2.1 (P.length + 1) le_rfl hn'.1 hlt
        exact False.elim ((hpost hlt) hc)
      · obtain ⟨m, hm, hnm⟩ := hnR
        have hm0 : 0 < m := by
          by_contra hm0
          have hmz : m = 0 := by omega
          subst m
          have hn : n = P.length + 1 := by simpa [E] using hnm
          subst n
          obtain ⟨n', hn'⟩ := hnstart
          have hlt : P.length + 1 < W.length := lt_of_lt_of_le hn'.1 hn'.2.1
          exact (hpost hlt) (hn'.2.2.1 _ le_rfl hn'.1 hlt)
        let t := j - m
        have htj : t < j := by dsimp [t]; omega
        have htQ : t ≤ Q.length := by rw [hQlen]; omega
        have hvn : vertex 1 W n = vertex k p t := by
          have hthird := vertex_fourGon_third P E R s 1 (m := m) (by omega)
          rw [← hnm] at hthird
          have hrev := vertex_revWord_of_end Q 1 t
          have hidx : Q.length - t = m := by rw [hQlen]; dsimp [t]; omega
          rw [hidx] at hrev
          have hrev' : vertex (RelLetter.listVal Q) R m = vertex 1 Q t := by
            simpa [R] using hrev
          have hQt : vertex 1 Q t = vertex 1 p t := vertex_take_eq 1 p j t (by omega)
          have hPv : RelLetter.listVal P = u := by simpa [u] using hP.2.1
          have hEval : RelLetter.listVal E = e := by
            dsimp [E]
            simp only [listVal_singleton, RelLetter.val]
          have hQv : RelLetter.listVal Q = vertex 1 p j := by simpa using hQ.2.1
          have hbase : u * e = k * RelLetter.listVal Q := by
            calc
              u * e = v := huv
              _ = k * vertex 1 p j := hvertexkj.symm
              _ = k * RelLetter.listVal Q := by rw [hQv]
          calc
            vertex 1 W n = RelLetter.listVal P * RelLetter.listVal E *
                vertex 1 R m := by simpa [W] using hthird
            _ = k * vertex (RelLetter.listVal Q) R m := by
              rw [hPv, hEval, vertex_eq_mul_vertex_one R (RelLetter.listVal Q) m]
              rw [hbase]
              group
            _ = k * vertex 1 Q t := by rw [hrev']
            _ = vertex k p t := by
              rw [hQt, vertex_eq_mul_vertex_one p k t]
        have hpk : IsGeodesicWord D k (k * z) p := by
          have h := (isGeodesicWord_mul_left D k 1 z p).mpr hp
          simpa using h
        have hsame :
            (QuotientGroup.mk (vertex k p t) : G ⧸ D.fam lam) =
              QuotientGroup.mk (vertex k p j) := by
          rw [← hvn]
          exact hcosn.symm.trans hcos
        have hle := entrance_le_of_mem_coset D lam hpk hj hsame
        rw [wordDist_vertex_eq_index D hpk (by omega)] at hle
        omega
      · obtain ⟨b, hb, hnb⟩ := hnS
        obtain ⟨n', hn'⟩ := hnstart
        have hnW : n < W.length := lt_of_lt_of_le hn'.1 hn'.2.1
        have hbpos : 0 < b := by
          by_contra hb0
          have hbz : b = 0 := by omega
          subst b
          have hnEq : n = W.length := by
            rw [hnb, hWlen]
            simp [E, hRlen]
          omega
        have hrevlt : s.length - b < (revWord s).length := by
          rw [length_revWord]
          omega
        have hletterW := hn'.2.2.1 n le_rfl hn'.1 hnW
        have hletterRev : ((revWord s)[s.length - b]'hrevlt).IsCompOf lam := by
          have hget := getElem_fourGon_revs P E R s hrevlt hnb hnW
          rw [← hget]
          simpa [W] using hletterW
        have hblast : b - 1 < s.length := by omega
        have hletterS : (s[b - 1]'hblast).IsCompOf lam :=
          (isCompOf_getElem_revWord' s lam hrevlt hblast (by omega)).mp hletterRev
        obtain ⟨a, a', ha, ha', hd⟩ :=
          exists_isComp_of_isCompOf lam s (b - 1) hblast hletterS
        have hab : a ≤ b := by omega
        have hbap : b ≤ a' := by omega
        have hspan : (vertex 1 s a)⁻¹ * vertex 1 s b ∈ D.fam lam :=
          span_mem_fam D lam 1 hs.1 b (by omega) a hab
            (fun t ht1 ht2 ht => hd.2.2.1 t ht1 (by omega) ht)
        have hmkeq :
            (QuotientGroup.mk (vertex 1 s a) : G ⧸ D.fam lam) =
              QuotientGroup.mk (vertex 1 s b) := QuotientGroup.eq.mpr hspan
        right
        refine ⟨s, a, a', hs, hd, ?_⟩
        have hvn : vertex 1 W n = vertex 1 s b := by
          have h := vertex_fourGon_opposite_closed P E R s hclose b
          rw [← hnb] at h
          simpa [W] using h
        exact hcosn.trans ((congrArg
          (fun y : G => (QuotientGroup.mk y : G ⧸ D.fam lam)) hvn).trans hmkeq.symm)
  · push Not at hpost
    obtain ⟨hlt, hnext⟩ := hpost
    have hj0 : j = 0 := by
      by_contra hj0
      have hjpos : 0 < j := by omega
      have hRpos : 0 < R.length := by rw [hRlen]; exact hjpos
      have hget := getElem_fourGon_r P E R s (n := P.length + 1) (j := 0) (by omega)
        (by simp [E]) (by simpa [W] using hlt)
      have hrev0 : ((revWord Q)[0]'(by simpa [R] using hRpos)).IsCompOf lam := by
        simpa [W, R] using hget ▸ hnext
      have hQlast : Q.length - 1 < Q.length := by omega
      have hlastQ :=
        (isCompOf_getElem_revWord' Q lam (by simpa [R] using hRpos) hQlast
          (by omega)).mp hrev0
      have hlastp : j - 1 < p.length := by omega
      have htake : Q[Q.length - 1]'hQlast = p[j - 1]'hlastp := by simp [Q, hQlen]
      rw [htake] at hlastQ
      exact hj.2.2.2.1 (j - 1) (by omega) hlastp hlastQ
    have hR0 : R.length = 0 := by omega
    have hspos : 0 < s.length := by
      rw [hWlen, hR0] at hlt
      simp [E] at hlt
      omega
    have hrev0lt : 0 < (revWord s).length := by rw [length_revWord]; exact hspos
    have hget := getElem_fourGon_revs P E R s (n := P.length + 1) (m := 0)
      hrev0lt (by simp [E, hR0])
      (by simpa [W] using hlt)
    have hrev0 : ((revWord s)[0]'hrev0lt).IsCompOf lam := by
      rw [← hget]
      simpa [W] using hnext
    have hlast : s.length - 1 < s.length := by omega
    have hlastS :=
      (isCompOf_getElem_revWord' s lam hrev0lt hlast (by omega)).mp hrev0
    obtain ⟨a, a', hd, hdcos⟩ :=
      exists_isComp_end_of_isCompOf_last D lam hs hspos hlastS
    right
    refine ⟨s, a, a', hs, hd, ?_⟩
    have hvj : v = k := by simp [v, hj0]
    rw [hdcos, ← hvj]
    exact hcos

end OsinComponents
end GGT
end GroupApproximation
