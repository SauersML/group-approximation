import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.GGT.OsinLemma56PrefixY
import GroupApproximation.GGT.OsinTheorem54SepGeodesicRuns
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex
import GroupApproximation.GGT.OsinTheorem54SepSplice

/-!
# Subgeodesic inheritance of the empty separating set

`GGT/OsinLemma56PrefixY.lean` reduced Osin's Lemma 5.6 to one statement, and
carried it as a hypothesis because the lemma that makes it true had not been
isolated.  It has been:
`OsinTheorem54SepGeodesicRuns.isComp_eq_succ_of_isGeodesicWord` --- a component
of a geodesic word is a single letter.  This module discharges the hypothesis.

## The argument

Suppose some coset `C` separated `1` from a vertex `v = (w.take i).prod` of the
geodesic `w`.  Then some geodesic `q` from `1` to `v` essentially penetrates `C`
at a component `[a,k)`.  Splice: `q ++ t`, with `t` a relative-letter spelling of
`w.drop i`.  Its length is `|q| + (|w| - i)`, and `|q| = i` because the
triangle inequality through `v` is tight on a geodesic, so the splice is again
geodesic --- from `1` to `y`.

What has to survive the splice is the component, and with it the span.  The
range and the predecessor clause of `IsComp` are unaffected, both reading letters
below `k ≤ |q|`.  The successor clause is the seam: at `k = |q|` the letter
following the component belongs to `t`, and nothing about `q` constrains it.

**It is constrained by the splice being geodesic.**  In a geodesic word an index
carrying an `H_mu`-letter *is* a component, since components are single letters
--- that is `OsinTheorem54SepSplice.isComp_of_isCompOf_geodesic`.  So `q[a]`
being a `mu`-letter hands over the component `[a, a+1)` of `q ++ t` outright, and
`[a,k)` is single for the same reason applied to `q`, so `k = a + 1` and the two
are the same component.  Its successor clause is exactly the seam condition,
discharged by the lemma that produced the component rather than checked
separately.

The span is then identical rather than re-measured: both endpoints have index at
most `|q|`, so `vertex_append_of_le` reads them off `q`.  Essentiality passes by
equality, and `C` separates `1` from `y` --- against the hypothesis.

## What the seam looked like before the lemma existed

The depth arithmetic permits the seam: `s ∉ relBall mu Dc` together with
`s * t ∈ relBall mu Dc` is consistent for a left-invariant `d_mu`, and the
sharpest that route yields is that such a run would span at most `Dc` letters.
No estimate closes it.  What closes it is that geodesic words have no two
adjacent letters of one index, so the configuration never arises.  That is worth
keeping in view: the obstruction was in the shape of the words, not in the size
of the constants.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Nothing separating `1` from `y` leaves nothing separating `1` from a
vertex of a geodesic to `y`.**

This is `SepPrefixInheritance`, discharged. -/
theorem sepPrefixInheritance (D : RelGenSet G Λ) (Dc : ℕ) :
    SepPrefixInheritance D Dc := by
  intro y hy w hlet hprod hlen i hi mu
  rw [Set.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨q, a, k, hq, hEP, hcq⟩ := hc
  obtain ⟨hcomp, hspan⟩ := hEP
  -- the tail, lifted to relative letters
  obtain ⟨t, htlet, htval, htlen⟩ :=
    exists_relWord D (w.drop i) (fun x hx => hlet x (List.drop_subset i w hx))
  have hsplit : (w.take i).prod * (w.drop i).prod = y := by
    rw [← List.prod_append, List.take_append_drop, hprod]
  -- the prefix realises its distance, so the splice is geodesic
  have hdistpre : wordDist D.alphabet.carrier 1 ((w.take i).prod) ≤ i := by
    have hword : IsWord D.alphabet.carrier (w.take i) ((w.take i).prod) :=
      ⟨fun x hx => hlet x (List.take_subset i w hx), rfl⟩
    have h := wordNorm_le_length hword
    have hlt : (w.take i).length = i := Hyperbolic.length_take_of_le hi
    rw [wordDist_one_left]
    omega
  have hdistsuf : wordDist D.alphabet.carrier ((w.take i).prod) y
      ≤ w.length - i := by
    have hword : IsWord D.alphabet.carrier (w.drop i) ((w.drop i).prod) :=
      ⟨fun x hx => hlet x (List.drop_subset i w hx), rfl⟩
    have h := wordNorm_le_length hword
    rw [List.length_drop] at h
    have heq : ((w.take i).prod)⁻¹ * y = (w.drop i).prod := by
      rw [← hsplit]
      exact inv_mul_cancel_left _ _
    show wordNorm D.alphabet.carrier (((w.take i).prod)⁻¹ * y) ≤ w.length - i
    rw [heq]
    exact h
  have hqlen : q.length = i := by
    have htri := wordDist_triangle D.alphabet.symmetricGenerating 1
      ((w.take i).prod) y
    have hql : q.length = wordDist D.alphabet.carrier 1 ((w.take i).prod) :=
      hq.2.2
    omega
  have hqv : RelLetter.listVal q = (w.take i).prod := by
    have h := hq.2.1
    rw [one_mul] at h
    exact h
  have hW : IsGeodesicWord D 1 y (q ++ t) := by
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact hq.1 b h
      · exact htlet b h
    · rw [listVal_append, htval, one_mul, hqv, hsplit]
    · rw [List.length_append, hqlen, htlen, List.length_drop]
      omega
  -- the component survives, with the same span
  have hak : k = a + 1 := isComp_eq_succ_of_isGeodesicWord D mu hq hcomp
  have hkq : k ≤ q.length := hcomp.2.1
  have haW : a < (q ++ t).length := by
    rw [List.length_append]
    omega
  have haq : a < q.length := by omega
  have hca : ((q ++ t)[a]'haW).IsCompOf mu := by
    rw [List.getElem_append_left haq]
    exact hcomp.2.2.1 a le_rfl hcomp.1 haq
  have hcompW : IsComp mu (q ++ t) a k := by
    have h := isComp_of_isCompOf_geodesic D mu hW haW hca
    rw [← hak] at h
    exact h
  -- the endpoints of the component are read off `q`
  have hva : vertex (1 : G) (q ++ t) a = vertex (1 : G) q a :=
    vertex_append_of_le q t 1 a (by omega)
  have hvk : vertex (1 : G) (q ++ t) k = vertex (1 : G) q k :=
    vertex_append_of_le q t 1 k (by omega)
  have hmem : c ∈ sepSet D mu Dc 1 y := by
    refine ⟨q ++ t, a, k, hW, ⟨hcompW, ?_⟩, ?_⟩
    · rw [hva, hvk]
      exact hspan
    · rw [hcq, hva]
  rw [hy mu] at hmem
  exact hmem

/-- **Osin's Lemma 5.6, unconditionally.**

`OsinLemma56PrefixY.exists_boundedDetour_of_sepPrefixInheritance` took the
inheritance as a hypothesis; it is now a theorem, so the `hM` binder of
`sepDataFam_of_binders_of_lemma510` is discharged outright.  Nothing beyond the
enlargement's own construction is assumed --- in particular not `h48`. -/
theorem exists_boundedDetour (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    ∃ M : ℕ, ∀ b ∈ (enlargedY D hDc hsymm).alphabet.carrier,
      ∀ w : List G, (∀ x ∈ w, x ∈ D.alphabet.carrier) → w.prod = b →
      w.length = wordDist D.alphabet.carrier 1 b →
      ∀ i ≤ w.length,
        wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
          (w.take i).prod ≤ M :=
  exists_boundedDetour_of_sepPrefixInheritance D hDc hsymm
    (sepPrefixInheritance D Dc)

end OsinEnlargement
end GGT
end GroupApproximation
