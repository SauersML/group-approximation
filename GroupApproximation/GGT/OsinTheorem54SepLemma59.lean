import GroupApproximation.GGT.OsinTheorem54SepSegmentVertex
import GroupApproximation.GGT.OsinTheorem54SepOrder

/-!
# Osin's Lemma 5.9: the gap between consecutive separating cosets is clean

> Between two consecutive `(f,g;D)`-separating cosets, the segment of a geodesic
> joining them separates nothing.

Equivalently, and this is how Lemma 5.10 consumes it, the element that segment
spells lies in `Y = {y | S(1,y;D) = ∅}`: consecutive separating cosets are
joined by letters of the enlarged alphabet.

## The proof, and why no estimate enters it

A coset separating the gap is essentially penetrated by the gap segment, which
is a geodesic (`isGeodesicWord_segment`); the penetration sits at some component
`[a,b)` of the segment; and the two ends are impossible:

* `a = 0` would make `w`'s letter at `k` a component letter, contradicting the
  **closing** clause of the first component `[i,k)`;
* `b = |segment|` would make `w`'s letter at `j - 1` a component letter,
  contradicting the **opening** clause of the second component `[j,l)`.

So the penetration is interior, `isComp_of_isComp_segment` carries it to `w`,
and `span_segment` says its span there is *literally the same element*, so it is
still essential.  Its index lies strictly between `i` and `j`, which contradicts
the two cosets being consecutive.

No bound, no span comparison, no §4.2 input: the two components' own maximality
clauses do all the work.  What is used is the **penetration half** of
`LemmaFourEight`, carried as a leading binder, which is what makes the
separating set of the gap independent of the geodesic realising it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Osin, Lemma 5.9.**  Between consecutive separating cosets, the gap
separates nothing.  Conditional on `LemmaFourEight`. -/
theorem sepSet_gap_eq_empty (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    (h48 : LemmaFourEight D lam Dc) {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) {i k j l : ℕ}
    (hc : IsComp lam w i k) (hc' : IsComp lam w j l) (hkj : k ≤ j)
    (hess : (vertex f w i)⁻¹ * vertex f w k ∉ D.relBall lam Dc)
    (hess' : (vertex f w j)⁻¹ * vertex f w l ∉ D.relBall lam Dc)
    (hsucc : SepSucc D lam Dc f g (QuotientGroup.mk (vertex f w i))
      (QuotientGroup.mk (vertex f w j))) :
    sepSet D lam Dc (vertex f w k) (vertex f w j) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro c'' hc''
  obtain ⟨hik, hkw, hrangec, hprec, hpostc⟩ := hc
  obtain ⟨hjl, hlw, hrangec', hprec', hpostc'⟩ := hc'
  have hjw : j ≤ w.length := by omega
  have hseg := isGeodesicWord_segment D hw hkj hjw
  obtain ⟨a, b, hEP, hcc⟩ := h48.1 (vertex f w k) (vertex f w j)
    ((w.drop k).take (j - k)) hseg c'' hc''
  obtain ⟨hcomp, hspan⟩ := hEP
  have hlen : ((w.drop k).take (j - k)).length = j - k :=
    length_segment w k (j - k) (by omega)
  obtain ⟨hab, hblen, hrange, hpre, hpost⟩ := hcomp
  -- the near end: `a = 0` contradicts the first component's closing clause
  have ha0 : 1 ≤ a := by
    by_contra hcon
    have ha : a = 0 := by omega
    subst ha
    have hk0 : (0 : ℕ) < ((w.drop k).take (j - k)).length := by omega
    have hkwlt : k < w.length := by omega
    have hcl := hrange 0 le_rfl hab hk0
    refine hpostc hkwlt ?_
    rw [getElem_segment' w k (j - k) 0 k hk0 hkwlt (by omega)]
    exact hcl
  -- the far end: `b = |segment|` contradicts the second component's opening clause
  have hblt : b < ((w.drop k).take (j - k)).length := by
    by_contra hcon
    have hbe : b = ((w.drop k).take (j - k)).length := by omega
    have hb1 : b - 1 < ((w.drop k).take (j - k)).length := by omega
    have hcl := hrange (b - 1) (by omega) (by omega) hb1
    have hj1w : j - 1 < w.length := by omega
    refine hprec' (j - 1) (by omega) hj1w ?_
    rw [getElem_segment' w k (j - k) (b - 1) (j - 1) hb1 hj1w (by omega)]
    exact hcl
  -- interior: transfer the component and its span to `w`
  have hcompw : IsComp lam w (k + a) (k + b) :=
    isComp_of_isComp_segment lam w ⟨hab, hblen, hrange, hpre, hpost⟩ ha0 hblt
      (by omega)
  have hspanw : (vertex f w (k + a))⁻¹ * vertex f w (k + b)
      ∉ D.relBall lam Dc := by
    rw [← span_segment w f k (j - k) a b (by omega) (by omega)]
    exact hspan
  have hccw : c'' = QuotientGroup.mk (vertex f w (k + a)) := by
    rw [hcc, vertex_segment w f k (j - k) a (by omega)]
  have hmem : c'' ∈ sepSet D lam Dc f g :=
    ⟨w, k + a, k + b, hw, ⟨hcompw, hspanw⟩, hccw⟩
  -- and it sits strictly between the two, contradicting consecutiveness
  obtain ⟨-, hno⟩ := hsucc
  refine hno c'' hmem ⟨?_, ?_⟩
  · exact ⟨w, hw, i, k + a, ⟨⟨k, ⟨⟨hik, hkw, hrangec, hprec, hpostc⟩, hess⟩⟩,
      rfl⟩, ⟨⟨k + b, ⟨hcompw, hspanw⟩⟩, hccw⟩, by omega⟩
  · exact ⟨w, hw, k + a, j, ⟨⟨k + b, ⟨hcompw, hspanw⟩⟩, hccw⟩,
      ⟨⟨l, ⟨⟨hjl, hlw, hrangec', hprec', hpostc'⟩, hess'⟩⟩, rfl⟩, by omega⟩

end OsinComponents
end GGT
end GroupApproximation
