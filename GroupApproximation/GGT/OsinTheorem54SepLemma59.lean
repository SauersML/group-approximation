import GroupApproximation.GGT.OsinTheorem54SepSegmentVertex
import GroupApproximation.GGT.OsinTheorem54SepOrder
import GroupApproximation.GGT.OsinTheorem54SepTransport

/-!
# Osin's Lemma 5.9: the gap between consecutive separating cosets is clean

> Between two consecutive `(f,g;D)`-separating cosets, the segment of a geodesic
> joining them separates nothing.

Equivalently, and this is how Lemma 5.10 consumes it, the element that segment
spells lies in `Y = {y | S(1,y;D) = ∅}`: consecutive separating cosets are
joined by letters of the enlarged alphabet.

## The proof, and where essentiality comes from

A coset separating the gap is essentially penetrated by SOME geodesic between
the gap's endpoints --- that is Definition 4.3, and it is the only place
essentiality is available.  Splice that geodesic into `w` between the two
component endpoints: the result is again a geodesic from `f` to `g`
(`isGeodesicWord_splice`), and it carries the witness's component with its span
untouched, so the coset separates `f` from `g`.

The two neighbouring cosets are then read on that SAME spliced geodesic --- their
components lie in the untouched prefix and suffix --- which puts all three
penetrations in one order and contradicts the two being consecutive.

The earlier proof instead asked `LemmaFourEight` for an essential penetration of
the gap segment.  That is not what 4.8 gives: Osin's 4.8 concludes penetration
by an arbitrary geodesic, and essentiality does not transfer between geodesics
--- two of them enter a coset at the same index, by Lemma 4.6, but with
different spans.  With the splice the hypothesis is not needed at all, and this
lemma is now unconditional.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Osin, Lemma 5.9.**  Between consecutive separating cosets, the gap
separates nothing.

Unconditional: the earlier proof asked `LemmaFourEight` for an ESSENTIAL
penetration of the gap segment, which is not what 4.8 gives.  This one takes
Definition 4.3's own witness for the gap and splices it into `w`, so the
component that witnesses essentiality is carried rather than re-derived --- and
the two neighbouring cosets are read on that same spliced geodesic, which is
what puts all three penetrations in one order. -/
theorem sepSet_gap_eq_empty (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) {i k j l : ℕ}
    (hc : IsComp lam w i k) (hc' : IsComp lam w j l) (hkj : k ≤ j)
    (hsucc : SepSucc D lam Dc f g (QuotientGroup.mk (vertex f w i))
      (QuotientGroup.mk (vertex f w j))) :
    sepSet D lam Dc (vertex f w k) (vertex f w j) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro c'' hc''
  have hmem : c'' ∈ sepSet D lam Dc f g :=
    sepSet_of_sepSet_segment D lam Dc hw hkj (by
      have := hc'.2.1
      have := hc'.1
      omega) hc''
  obtain ⟨u, a, b, hu, hEP, hcc⟩ := hc''
  have hik : i < k := hc.1
  have hjl : j < l := hc'.1
  have hkw : k ≤ w.length := hc.2.1
  have hlw : l ≤ w.length := hc'.2.1
  have hjw : j ≤ w.length := by omega
  have hsplice := isGeodesicWord_splice D hw hkj hjw hu
  have hab : a < b := hEP.1.1
  have hbu : b ≤ u.length := hEP.1.2.1
  have hba : b = a + 1 := isComp_eq_succ_of_isGeodesicWord D lam hu hEP.1
  have hau : a < u.length := by omega
  have hr : RelLetter.listVal u = (vertex f w k)⁻¹ * vertex f w j := by
    rw [← hu.2.1]
    group
  obtain ⟨hvpre, hvmid, hvsuf⟩ := vertex_splice f w u hkw hr
  -- expanded, not just `= w.length`: the bounds below need `u.length` visible
  have hlen' : (w.take k ++ (u ++ w.drop j)).length
      = k + (u.length + (w.length - j)) := by
    rw [List.length_append, List.length_append, List.length_take,
      List.length_drop, Nat.min_eq_left hkw]
  -- the gap's own component, on the spliced geodesic
  have hka : k + a < (w.take k ++ (u ++ w.drop j)).length := by omega
  have hmid : (w.take k ++ (u ++ w.drop j))[k + a]'hka = u[a]'hau := by
    rw [getElem_splice_mid w u (by omega) (by omega) hkw hka]
    exact getElem_congr_idx (by omega)
  have hcof : ((w.take k ++ (u ++ w.drop j))[k + a]'hka).IsCompOf lam := by
    rw [hmid]
    exact hEP.1.2.2.1 a le_rfl hab hau
  have hcomp'' : IsComp lam (w.take k ++ (u ++ w.drop j)) (k + a) (k + a + 1) :=
    isComp_of_isCompOf_geodesic D lam hsplice hka hcof
  have hva : vertex f (w.take k ++ (u ++ w.drop j)) (k + a)
      = vertex (vertex f w k) u a := hvmid a (by omega)
  have hcca : c'' = QuotientGroup.mk
      (vertex f (w.take k ++ (u ++ w.drop j)) (k + a)) := by
    rw [hva]
    exact hcc
  -- the left neighbour, on the same geodesic
  have hiw : i < (w.take k ++ (u ++ w.drop j)).length := by omega
  have hlefti : ((w.take k ++ (u ++ w.drop j))[i]'hiw).IsCompOf lam := by
    rw [getElem_splice_left w u hkw (by omega) hiw]
    exact hc.2.2.1 i le_rfl hik (by omega)
  have hcompi : IsComp lam (w.take k ++ (u ++ w.drop j)) i (i + 1) :=
    isComp_of_isCompOf_geodesic D lam hsplice hiw hlefti
  have hvi : vertex f (w.take k ++ (u ++ w.drop j)) i = vertex f w i :=
    hvpre i (by omega)
  -- the right neighbour, likewise
  have hju : k + u.length < (w.take k ++ (u ++ w.drop j)).length := by omega
  have hrightj :
      ((w.take k ++ (u ++ w.drop j))[k + u.length]'hju).IsCompOf lam := by
    rw [getElem_splice_right w u (by omega) hkw hju,
      getElem_congr_idx (show j + (k + u.length - k - u.length) = j from by
        omega)]
    exact hc'.2.2.1 j le_rfl hjl (by omega)
  have hcompj : IsComp lam (w.take k ++ (u ++ w.drop j)) (k + u.length)
      (k + u.length + 1) :=
    isComp_of_isCompOf_geodesic D lam hsplice hju hrightj
  have hvj : vertex f (w.take k ++ (u ++ w.drop j)) (k + u.length)
      = vertex f w j := by
    have h := hvsuf 0
    rw [Nat.add_zero, Nat.add_zero] at h
    exact h
  -- strictly between the two, contradicting consecutiveness
  obtain ⟨-, hno⟩ := hsucc
  refine hno c'' hmem ⟨?_, ?_⟩
  · exact ⟨w.take k ++ (u ++ w.drop j), hsplice, i, k + a,
      ⟨⟨i + 1, hcompi⟩, congrArg QuotientGroup.mk hvi.symm⟩,
      ⟨⟨k + a + 1, hcomp''⟩, hcca⟩, by omega⟩
  · exact ⟨w.take k ++ (u ++ w.drop j), hsplice, k + a, k + u.length,
      ⟨⟨k + a + 1, hcomp''⟩, hcca⟩,
      ⟨⟨k + u.length + 1, hcompj⟩, congrArg QuotientGroup.mk hvj.symm⟩,
      by omega⟩

end OsinComponents
end GGT
end GroupApproximation
