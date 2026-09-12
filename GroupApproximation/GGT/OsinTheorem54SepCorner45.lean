import GroupApproximation.GGT.OsinTheorem54SepEntrance
import GroupApproximation.GGT.OsinTheorem54SepRuns

/-!
# The corner case of Lemma 4.5

Lemma 4.5's argument runs a witnessing component of the geodesic `w : f → g`
against the isolated-component bound, and that needs the component to stop short
of the end of `w`.  When it does not --- when the run reaches `g` --- the
conclusion arrives instead of the argument, and this module is that branch.

Two facts, and the second is the one to be careful with.

* A component reaching the end of `w` names the coset of the ENDPOINT: its two
  vertices differ by an element of `H_λ`, so `c = mk g`.
* A geodesic whose LAST letter is an `H_λ`-letter penetrates the coset of its
  own endpoint, and the component that does it is the maximal run ending there.

Put together: if the run continues past the corner, the next block's letter is
an `H_λ`-letter, so the side it belongs to has an `H_λ`-letter at the end
adjacent to `g`, and that side penetrates `mk g = c`.

## Why the coset is read off the run and not off the index

The letter across the corner belongs to a different side, and nothing about its
INDEX says which coset it reads --- a priori it could be a different coset of the
same `H_λ`.  What pins it is that the run is one component of the polygon word,
so consecutive vertices along it differ by `H_λ`-letters and every vertex of the
run lies in one coset.  Both lemmas below take the coset from
`mk_vertex_eq_of_isComp`, which is that fact, rather than from any index
coincidence.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A component reaching the end of a geodesic names the endpoint's coset.** -/
theorem mk_eq_of_isComp_end (D : RelGenSet G Λ) (lam : Λ) {f g : G}
    {ws : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g ws) {i : ℕ}
    (hcomp : IsComp lam ws i ws.length) :
    (QuotientGroup.mk (vertex f ws i) : G ⧸ D.fam lam) = QuotientGroup.mk g := by
  have h := mk_vertex_eq_of_isComp D f hw.1 hcomp
  rwa [IsGeodesicWord.vertex_length_eq hw] at h

/-- **A geodesic whose last letter is peripheral penetrates its endpoint's
coset.**

The witness is the maximal run ending at the last letter; its far end is the
endpoint itself, so the coset it names is the endpoint's. -/
theorem exists_isComp_end_of_isCompOf_last (D : RelGenSet G Λ) (lam : Λ)
    {f g : G} {ws : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g ws)
    (hpos : 0 < ws.length)
    (hlast : (ws[ws.length - 1]'(by omega)).IsCompOf lam) :
    ∃ i k : ℕ, IsComp lam ws i k ∧
      (QuotientGroup.mk (vertex f ws i) : G ⧸ D.fam lam)
        = QuotientGroup.mk g := by
  obtain ⟨i, k, hik, hjk, hcomp⟩ :=
    exists_isComp_of_isCompOf lam ws (ws.length - 1) (by omega) hlast
  have hkw : k ≤ ws.length := hcomp.2.1
  have hk : k = ws.length := by omega
  subst hk
  exact ⟨i, ws.length, hcomp, mk_eq_of_isComp_end D lam hw hcomp⟩

end OsinComponents
end GGT
end GroupApproximation
