import GroupApproximation.GGT.OsinTheorem54SepTriangle
import GroupApproximation.GGT.OsinTheorem54SepFourGonBridge
import GroupApproximation.GGT.OsinTheorem54SepCorner45
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# Osin's Lemma 4.5: two geodesic segments penetrate every separating coset

A coset separating `f` from `g` is penetrated by the two-segment path
`f → h → g`, whichever geodesics the two segments are.  This is what lets
Lemma 4.9 compare `S(f,g)` against `S(f,h)` and `S(g,h)` at all.

The polygon is the triangle on the three geodesics, carried as the quadrilateral
with an empty first side, so the isolated-component bound arrives at `n = 4` and
the hypothesis is `4C ≤ Dc` where Osin writes `D ≥ 3C` (Remark 4.4).  `D` is
chosen downstream with `C` in hand, so the larger lower bound costs nothing.

## The shape of the argument

The witness is a geodesic `w : f → g` with a component essentially penetrating
the coset.  Everything then turns on ONE clause: whether that component is still
maximal in the polygon, i.e. whether the letter at its end is peripheral.

* If it is not, the component transfers, and it cannot be isolated --- the bound
  would put its span inside `relBall lam (C*4) ⊆ relBall lam Dc`, contradicting
  essentiality.  So it is connected to another component start, and there are
  three places that start can be, one per block.
* If it is, the run continues past the corner into the next block, and the
  conclusion arrives instead of the argument: that block's side has a peripheral
  letter next to `g`, so it penetrates the coset outright.

## Why the third case is not symmetric with the second

The first block's match is refuted rather than used: two distinct components of
one GEODESIC cannot be connected, which is `not_connected_qBlock_of_isComp`.
The second and third blocks are read backwards --- they are traversed against
their own orientation --- so a match there is converted through
`isCompOf_getElem_revWord'` BEFORE the component of the side is extracted, never
after: the letter across a reversal belongs to a different side, and its index
alone says nothing about which coset of `H_λ` it reads.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The triangle's blocks, specialised from the quadrilateral -/

/-- **A component of the first side is a component of the triangle**, given
maximality at its end in the triangle. -/
theorem isComp_triangle_of_isComp_witness (ws r s : List (RelLetter G Λ))
    (lam : Λ) {i k : ℕ} (hcomp : IsComp lam ws i k)
    (hpost : ∀ hkl : k < (ws ++ r ++ revWord s).length,
      ¬ ((ws ++ r ++ revWord s)[k]'hkl).IsCompOf lam) :
    IsComp lam (ws ++ r ++ revWord s) i k := by
  have h := isComp_fourGon_of_isComp_side_of_post [] ws r s lam (by simp) hcomp
    (by simpa using hpost)
  simpa using h

/-- **A vertex in the first block is a vertex of the first side.** -/
theorem vertex_triangle_witness (ws r s : List (RelLetter G Λ)) (v : G) {t : ℕ}
    (ht : t ≤ ws.length) :
    vertex v (ws ++ r ++ revWord s) t = vertex v ws t := by
  have h := vertex_fourGon_side [] ws r s v ht
  rw [RelLetter.listVal_nil, mul_one] at h
  simpa using h.trans (vertex_eq_mul_vertex_one ws v t).symm

/-- **A vertex in the middle block is a vertex of the second side**, read from
its own basepoint and against its own orientation. -/
theorem vertex_triangle_mid_side (ws zs ys : List (RelLetter G Λ)) {f g hh : G}
    (hwv : f * RelLetter.listVal ws = g) (hzv : hh * RelLetter.listVal zs = g)
    {a : ℕ} (ha : a ≤ zs.length) :
    vertex f (ws ++ revWord zs ++ revWord ys) (ws.length + a)
      = vertex hh zs (zs.length - a) := by
  -- `m` is implicit in `vertex_fourGon_third`; naming the fact FIXES it at `a`.
  -- Passing a `by` block instead leaves `?m ≤ (revWord zs).length` open, and
  -- `rw`'s trailing `rfl` closes that by assigning `?m := (revWord zs).length`.
  have haz : a ≤ (revWord zs).length := by
    rw [length_revWord]
    exact ha
  have h := vertex_fourGon_third [] ws (revWord zs) ys f haz
  rw [RelLetter.listVal_nil, mul_one,
    ← vertex_eq_mul_vertex_one (revWord zs) (f * RelLetter.listVal ws) a] at h
  have hrev := vertex_revWord zs (f * RelLetter.listVal ws) (zs.length - a)
  rw [show zs.length - (zs.length - a) = a from by omega] at hrev
  have hh' : g * (RelLetter.listVal zs)⁻¹ = hh := by
    rw [← hzv]
    group
  have hfin : vertex (f * RelLetter.listVal ws) (revWord zs) a
      = vertex hh zs (zs.length - a) := by
    rw [hrev, hwv, hh', vertex_eq_mul_vertex_one zs hh (zs.length - a)]
  simpa using h.trans hfin

/-- **A vertex in the last block is a vertex of the third side**, read against
its orientation; the closing relation is what cancels the translation. -/
theorem vertex_triangle_last_side (ws zs ys : List (RelLetter G Λ)) {f g hh : G}
    (hwv : f * RelLetter.listVal ws = g) (hzv : hh * RelLetter.listVal zs = g)
    (hyv : f * RelLetter.listVal ys = hh) {b : ℕ} (hb : b ≤ ys.length) :
    vertex f (ws ++ revWord zs ++ revWord ys) (ws.length + zs.length + b)
      = vertex f ys (ys.length - b) := by
  have hclose : RelLetter.listVal ys
      = RelLetter.listVal ([] : List (RelLetter G Λ)) * RelLetter.listVal ws
        * RelLetter.listVal (revWord zs) := by
    have hy' : RelLetter.listVal ys = f⁻¹ * hh := by rw [← hyv]; group
    have hw' : RelLetter.listVal ws = f⁻¹ * g := by rw [← hwv]; group
    have hz' : RelLetter.listVal (revWord zs) = g⁻¹ * hh := by
      rw [listVal_revWord, ← hzv]
      group
    rw [hy', hw', hz', RelLetter.listVal_nil, one_mul]
    group
  have h := vertex_fourGon_opposite_closed_of_basepoint [] ws (revWord zs) ys f
    hclose (ys.length - b)
  rw [show ys.length - (ys.length - b) = b from by omega] at h
  simp only [List.nil_append, List.length_nil, Nat.zero_add,
    length_revWord] at h
  rw [h, vertex_eq_mul_vertex_one ys f (ys.length - b)]


/-- **A letter in the middle block is a letter of `revWord zs`.** -/
theorem getElem_triangle_mid (ws zs ys : List (RelLetter G Λ)) {n a : ℕ}
    (ha : a < (revWord zs).length) (hna : n = ws.length + a)
    (hn : n < (ws ++ revWord zs ++ revWord ys).length) :
    (ws ++ revWord zs ++ revWord ys)[n]'hn = (revWord zs)[a]'ha := by
  have h := getElem_fourGon_r [] ws (revWord zs) ys ha
    (by simpa using hna) (by simpa using hn)
  simpa using h

/-- **A letter in the last block is a letter of `revWord ys`.** -/
theorem getElem_triangle_last (ws zs ys : List (RelLetter G Λ)) {n b : ℕ}
    (hb : b < (revWord ys).length)
    (hnb : n = ws.length + (revWord zs).length + b)
    (hn : n < (ws ++ revWord zs ++ revWord ys).length) :
    (ws ++ revWord zs ++ revWord ys)[n]'hn = (revWord ys)[b]'hb := by
  have h := getElem_fourGon_revs [] ws (revWord zs) ys hb
    (by simpa using hnb) (by simpa using hn)
  simpa using h

/-- **The triangle's length.** -/
theorem length_triangle (ws zs ys : List (RelLetter G Λ)) :
    (ws ++ revWord zs ++ revWord ys).length
      = ws.length + zs.length + ys.length := by
  rw [List.length_append, List.length_append, length_revWord, length_revWord]

/-- **A letter in the first block is a letter of the first side.** -/
theorem getElem_triangle_witness (ws zs ys : List (RelLetter G Λ)) {n : ℕ}
    (hn' : n < ws.length)
    (hn : n < (ws ++ revWord zs ++ revWord ys).length) :
    (ws ++ revWord zs ++ revWord ys)[n]'hn = ws[n]'hn' := by
  have h : (([] : List (RelLetter G Λ)) ++ ws ++ revWord zs ++ revWord ys)[n]'
        (by simpa using hn) = ws[n]'hn' :=
    getElem_fourGon_q [] ws (revWord zs) ys hn' (by simp) (by simpa using hn)
  simpa using h

/-! ## Lemma 4.5 -/

/-- **Osin, Lemma 4.5.**  Every `(f,g;Dc)`-separating coset is penetrated by the
two-segment path `f → hh → g`, whichever geodesics the two segments are. -/
theorem penetrates_of_mem_sepSet (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {f g hh : G} {ys zs : List (RelLetter G Λ)}
    (hy : IsGeodesicWord D f hh ys) (hz : IsGeodesicWord D hh g zs)
    {c : G ⧸ D.fam lam} (hc : c ∈ sepSet D lam Dc f g) :
    (∃ m n : ℕ, IsComp lam ys m n ∧
        (QuotientGroup.mk (vertex f ys m) : G ⧸ D.fam lam) = c)
      ∨ (∃ m n : ℕ, IsComp lam zs m n ∧
        (QuotientGroup.mk (vertex hh zs m) : G ⧸ D.fam lam) = c) := by
  classical
  obtain ⟨ws, i, k, hw, hEP, hcmk⟩ := hc
  have hcomp := hEP.1
  have hdeep := hEP.2
  have hik : i < k := hcomp.1
  have hkw : k ≤ ws.length := hcomp.2.1
  have hlenW := length_triangle ws zs ys
  have hpoly := isQuasiGeodesicPolygon_triangle D hsymm hw hy hz
  have hwv : f * RelLetter.listVal ws = g := hw.2.1
  have hzv : hh * RelLetter.listVal zs = g := hz.2.1
  have hyv : f * RelLetter.listVal ys = hh := hy.2.1
  have hcW : (QuotientGroup.mk (vertex f (ws ++ revWord zs ++ revWord ys) i)
      : G ⧸ D.fam lam) = c := by
    rw [vertex_triangle_witness ws (revWord zs) ys f (by omega : i ≤ ws.length),
      ← hcmk]
  -- The main argument, under maximality of the component in the triangle.
  have main : (∀ hkl : k < (ws ++ revWord zs ++ revWord ys).length,
        ¬ ((ws ++ revWord zs ++ revWord ys)[k]'hkl).IsCompOf lam) →
      (∃ m n : ℕ, IsComp lam ys m n ∧
          (QuotientGroup.mk (vertex f ys m) : G ⧸ D.fam lam) = c)
        ∨ (∃ m n : ℕ, IsComp lam zs m n ∧
          (QuotientGroup.mk (vertex hh zs m) : G ⧸ D.fam lam) = c) := by
    intro hpost
    have hWcomp : IsComp lam (ws ++ revWord zs ++ revWord ys) i k :=
      isComp_triangle_of_isComp_witness ws (revWord zs) ys lam hcomp hpost
    -- Not isolated: the bound would put the span inside the ball.
    have hnotiso : ¬ IsIsolated D.fam lam f (ws ++ revWord zs ++ revWord ys) i := by
      intro hiso
      have hb := hbnd 4 (by omega) f (ws ++ revWord zs ++ revWord ys) hpoly lam i
        k hWcomp hiso
      rw [vertex_triangle_witness ws (revWord zs) ys f (by omega : i ≤ ws.length),
        vertex_triangle_witness ws (revWord zs) ys f hkw] at hb
      exact hdeep (relBall_mono_radius D lam hDc hb)
    have hstart : IsCompStart lam (ws ++ revWord zs ++ revWord ys) i := ⟨k, hWcomp⟩
    have hB : ¬ ∀ j : ℕ, j ≠ i →
        IsCompStart lam (ws ++ revWord zs ++ revWord ys) j →
        ¬ Connected D.fam lam f (ws ++ revWord zs ++ revWord ys) i j :=
      fun hB' => hnotiso ⟨hstart, hB'⟩
    push Not at hB
    obtain ⟨j, hjne, hjstart, hjconn⟩ := hB
    obtain ⟨jk, hjcomp⟩ := hjstart
    have hjlt : j < jk := hjcomp.1
    have hjkw : jk ≤ (ws ++ revWord zs ++ revWord ys).length := hjcomp.2.1
    have hjW : j < (ws ++ revWord zs ++ revWord ys).length := by omega
    have hcj : (QuotientGroup.mk (vertex f (ws ++ revWord zs ++ revWord ys) j)
        : G ⧸ D.fam lam) = c :=
      ((mk_eq_mk_of_connected hjconn).symm).trans hcW
    rcases Nat.lt_or_ge j ws.length with hjw | hjw
    · -- CASE 1: the match lies on the witnessing geodesic itself: impossible.
      exfalso
      have hconnmem : (vertex f (ws ++ revWord zs ++ revWord ys) i)⁻¹ *
          vertex f (ws ++ revWord zs ++ revWord ys) j ∈ D.fam lam := hjconn
      rw [vertex_triangle_witness ws (revWord zs) ys f (by omega : i ≤ ws.length),
        vertex_triangle_witness ws (revWord zs) ys f (by omega : j ≤ ws.length),
        span_eq_span_one ws f i j] at hconnmem
      refine not_connected_qBlock_of_isComp D lam [] ws (revWord zs) ys
        (isGeodesicWord_one_of D hw) hcomp (by omega) hjne ?_ hconnmem ?_
      · have hjcomp' : IsComp lam (ws ++ (revWord zs ++ revWord ys)) j jk := by
          rw [← List.append_assoc]; exact hjcomp
        simpa using ⟨jk, hjcomp'⟩
      · group
    · rcases Nat.lt_or_ge j (ws.length + zs.length) with hjz | hjz
      · -- CASE 2: the match lies on `zs`, read against its orientation.
        right
        have hazr : j - ws.length < (revWord zs).length := by
          rw [length_revWord]
          omega
        have hWj : ((ws ++ revWord zs ++ revWord ys)[j]'hjW).IsCompOf lam :=
          hjcomp.2.2.1 j le_rfl hjlt hjW
        rw [getElem_triangle_mid ws zs ys hazr (by omega) hjW] at hWj
        have hzt : zs.length - 1 - (j - ws.length) < zs.length := by omega
        have hzlast : (zs[zs.length - 1 - (j - ws.length)]'hzt).IsCompOf lam :=
          (isCompOf_getElem_revWord' zs lam hazr hzt rfl).mp hWj
        obtain ⟨m, n, hm1, hm2, hzcomp⟩ := exists_isComp_of_isCompOf lam zs
          (zs.length - 1 - (j - ws.length)) hzt hzlast
        refine ⟨m, n, hzcomp, ?_⟩
        have hvid := vertex_triangle_mid_side ws zs ys hwv hzv
          (a := j - ws.length) (by omega)
        rw [show ws.length + (j - ws.length) = j from by omega] at hvid
        have hspan := span_mem_fam D lam hh hz.1
          (zs.length - (j - ws.length)) (by omega) m (by omega)
          (fun t ht1 ht2 ht => hzcomp.2.2.1 t ht1 (by omega) ht)
        have hmkeq : (QuotientGroup.mk (vertex hh zs m) : G ⧸ D.fam lam)
            = QuotientGroup.mk (vertex hh zs (zs.length - (j - ws.length))) :=
          QuotientGroup.eq.mpr hspan
        rw [hmkeq, ← hvid]
        exact hcj
      · -- CASE 3: the match lies on `ys`, read against its orientation.
        left
        have hbr : j - (ws.length + zs.length) < (revWord ys).length := by
          rw [length_revWord]
          omega
        have hWj : ((ws ++ revWord zs ++ revWord ys)[j]'hjW).IsCompOf lam :=
          hjcomp.2.2.1 j le_rfl hjlt hjW
        rw [getElem_triangle_last ws zs ys hbr
          (by rw [length_revWord]; omega) hjW] at hWj
        have hyt : ys.length - 1 - (j - (ws.length + zs.length)) < ys.length := by
          omega
        have hylast := (isCompOf_getElem_revWord' ys lam hbr hyt rfl).mp hWj
        obtain ⟨m, n, hm1, hm2, hycomp⟩ := exists_isComp_of_isCompOf lam ys
          (ys.length - 1 - (j - (ws.length + zs.length))) hyt hylast
        refine ⟨m, n, hycomp, ?_⟩
        have hvid := vertex_triangle_last_side ws zs ys hwv hzv hyv
          (b := j - (ws.length + zs.length)) (by omega)
        rw [show ws.length + zs.length + (j - (ws.length + zs.length)) = j
          from by omega] at hvid
        have hspan := span_mem_fam D lam f hy.1
          (ys.length - (j - (ws.length + zs.length))) (by omega) m (by omega)
          (fun t ht1 ht2 ht => hycomp.2.2.1 t ht1 (by omega) ht)
        have hmkeq : (QuotientGroup.mk (vertex f ys m) : G ⧸ D.fam lam)
            = QuotientGroup.mk
              (vertex f ys (ys.length - (j - (ws.length + zs.length)))) :=
          QuotientGroup.eq.mpr hspan
        rw [hmkeq, ← hvid]
        exact hcj
  -- The corner: either maximality holds in the triangle, or the run continues.
  by_cases hklt : k < (ws ++ revWord zs ++ revWord ys).length
  · by_cases hWk : ((ws ++ revWord zs ++ revWord ys)[k]'hklt).IsCompOf lam
    · -- The run continues past the corner, so `k` is the end of `ws`.
      have hkws : k = ws.length := by
        by_contra hne
        have hklt' : k < ws.length := by omega
        rw [getElem_triangle_witness ws zs ys hklt' hklt] at hWk
        exact hcomp.2.2.2.2 hklt' hWk
      subst hkws
      have hcg : c = QuotientGroup.mk g := by
        rw [hcmk]
        exact mk_eq_of_isComp_end D lam hw hcomp
      rcases Nat.eq_zero_or_pos zs.length with hz0 | hzpos
      · -- `zs` is empty, so `hh = g` and the corner leads into `revWord ys`.
        left
        have hhg : hh = g := by
          have hzn : zs = [] := List.length_eq_zero_iff.mp hz0
          rw [← hzv, hzn, RelLetter.listVal_nil, mul_one]
        have hbr : 0 < (revWord ys).length := by
          rw [length_revWord]
          omega
        rw [getElem_triangle_last ws zs ys hbr
          (by rw [length_revWord]; omega) hklt] at hWk
        have hyt : ys.length - 1 < ys.length := by omega
        have hylast := (isCompOf_getElem_revWord' ys lam hbr hyt (by omega)).mp hWk
        obtain ⟨m, n, hycomp, hmk⟩ :=
          exists_isComp_end_of_isCompOf_last D lam hy (by omega) hylast
        exact ⟨m, n, hycomp, by rw [hmk, hcg, hhg]⟩
      · -- The corner leads into `revWord zs`.
        right
        have hbr : 0 < (revWord zs).length := by
          rw [length_revWord]
          omega
        rw [getElem_triangle_mid ws zs ys hbr (by omega) hklt] at hWk
        have hzt : zs.length - 1 < zs.length := by omega
        have hzlast := (isCompOf_getElem_revWord' zs lam hbr hzt (by omega)).mp hWk
        obtain ⟨m, n, hzcomp, hmk⟩ :=
          exists_isComp_end_of_isCompOf_last D lam hz (by omega) hzlast
        exact ⟨m, n, hzcomp, by rw [hmk, hcg]⟩
    · exact main (fun _ => hWk)
  · exact main (fun hkl' => absurd hkl' hklt)

end OsinComponents
end GGT
end GroupApproximation
