import GroupApproximation.GGT.OsinTheorem54SepReversal
import GroupApproximation.GGT.OsinTheorem54SepComponents
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex

/-!
# Reversing a path reverses its components, and keeps their cosets

The index half of `sep_comm`.  `GGT/OsinTheorem54SepCommRefuted.lean` shows the
field is false at an asymmetric base, and `exists_symmetric_base'` removes that
obstruction; what is left is the bookkeeping of *which* component of the
reversed path corresponds to a given component of the original, and *which
coset* it records.  Both answers are exact, and neither needs a hypothesis:

* `isComp_revWord` --- the component `[i,k)` of `w` becomes the component
  `[|w| - k, |w| - i)` of `revWord w`.  The five clauses of `IsComp` map across
  with the two maximality clauses **exchanged**: the letter before the reversed
  run is the letter at `k`, and the letter at the end of the reversed run is the
  letter before `i`.
* `vertex_revWord_of_end` --- reading `revWord w` from the far endpoint
  `f · listVal w` lands on the vertices of `w` themselves, in reverse order:
  `vertex (f * listVal w) (revWord w) (|w| - j) = vertex f w j`.
* `mk_vertex_revWord_eq` --- so the coset the reversed path records at its
  component is `mk (vertex f w k)`, the *far* endpoint of the original run,
  and that is the **same coset** as `mk (vertex f w i)`, the two differing by
  the span of the component, which lies in `H_λ`.

That last point is the one worth stating plainly: reversal does not move the
coset, it only changes which end of the run names it.  So on a symmetric base,
where `revWord` of a geodesic is again a geodesic, `S(g,f;D)` and `S(f,g;D)`
have the same members --- not merely the same cardinality.

Nothing here consumes `OsinComponents.LemmaFourEight` or
`OsinComponents.IsolatedComponentBound`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Letters of the reversed word -/

/-- **The letter of `revWord w` at `m` is the inverse of the letter of `w` at
`|w| - 1 - m`.** -/
theorem getElem_revWord (w : List (RelLetter G Λ)) {m : ℕ}
    (hm : m < (revWord w).length) (hm' : w.length - 1 - m < w.length) :
    (revWord w)[m]'hm = invLetter (w[w.length - 1 - m]'hm') := by
  have hlen : (w.map invLetter).length = w.length := List.length_map _
  have hmw : m < w.length := by
    rw [length_revWord] at hm
    exact hm
  have h1 : ((w.map invLetter).reverse)[m]'hm
      = (w.map invLetter)[(w.map invLetter).length - 1 - m]'(by omega) :=
    List.getElem_reverse _
  have h2 : (w.map invLetter)[(w.map invLetter).length - 1 - m]'(by omega)
      = (w.map invLetter)[w.length - 1 - m]'(by omega) :=
    getElem_congr_idx (by omega)
  have h3 : (w.map invLetter)[w.length - 1 - m]'(by omega)
      = invLetter (w[w.length - 1 - m]'hm') := List.getElem_map _
  show ((w.map invLetter).reverse)[m]'hm = _
  exact h1.trans (h2.trans h3)

/-- **Reversal preserves being a component letter.** -/
theorem isCompOf_getElem_revWord (w : List (RelLetter G Λ)) (lam : Λ) {m : ℕ}
    (hm : m < (revWord w).length) (hm' : w.length - 1 - m < w.length) :
    ((revWord w)[m]'hm).IsCompOf lam
      ↔ (w[w.length - 1 - m]'hm').IsCompOf lam := by
  rw [getElem_revWord w hm hm']
  exact isCompOf_invLetter _ lam

/-- **Reversal preserves being a component letter, at a named index.**

The index is supplied as a parameter with an equation rather than computed in
place.  Rewriting `w.length - 1 - m` to a name *inside* a `getElem` breaks the
motive, the proof argument `w[·]'h` depending on the index; carrying the
equation as a hypothesis and discharging it with `subst` avoids the rewrite
entirely. -/
theorem isCompOf_getElem_revWord' (w : List (RelLetter G Λ)) (lam : Λ)
    {m t : ℕ} (hm : m < (revWord w).length) (ht : t < w.length)
    (hmt : t = w.length - 1 - m) :
    ((revWord w)[m]'hm).IsCompOf lam ↔ (w[t]'ht).IsCompOf lam := by
  subst hmt
  exact isCompOf_getElem_revWord w lam hm ht

/-! ## Components of the reversed word -/

/-- **The component `[i,k)` of `w` is the component `[|w| - k, |w| - i)` of
`revWord w`.**

The two maximality clauses are exchanged: what bounds the reversed run at its
start is the letter of `w` at `k`, and what bounds it at its end is the letter
of `w` at `i - 1`. -/
theorem isComp_revWord (lam : Λ) (w : List (RelLetter G Λ)) {i k : ℕ}
    (h : IsComp lam w i k) :
    IsComp lam (revWord w) (w.length - k) (w.length - i) := by
  obtain ⟨hik, hkw, hrange, hpre, hpost⟩ := h
  have hrl : (revWord w).length = w.length := length_revWord w
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hj
    have hjw : j < w.length := by omega
    have hidx : w.length - 1 - j < w.length := by omega
    rw [isCompOf_getElem_revWord w lam hj hidx]
    exact hrange (w.length - 1 - j) (by omega) (by omega) hidx
  · intro j hji hj hc
    have hkw' : k < w.length := by omega
    rw [isCompOf_getElem_revWord' w lam hj hkw' (by omega)] at hc
    exact hpost hkw' hc
  · intro hk hc
    have hi1 : i - 1 < w.length := by omega
    rw [isCompOf_getElem_revWord' w lam hk hi1 (by omega)] at hc
    exact hpre (i - 1) (by omega) hi1 hc

/-! ## Vertices, and the coset the reversed path records -/

/-- **Reading the reversed word from the far endpoint retraces the vertices.**
-/
theorem vertex_revWord_of_end (w : List (RelLetter G Λ)) (f : G) (j : ℕ) :
    vertex (f * RelLetter.listVal w) (revWord w) (w.length - j) = vertex f w j := by
  rw [vertex_revWord w (f * RelLetter.listVal w) j,
    vertex_eq_mul_vertex_one w f j]
  group

/-- **Reversal does not move the coset.**

The reversed path records its component at the *far* endpoint of the original
run, `vertex f w k`; that differs from `vertex f w i` by the span of the
component, which lies in `H_λ` by `span_mem_fam_of_isComp`.  So the coset is the
same one. -/
theorem mk_vertex_revWord_eq (D : RelGenSet G Λ) (lam : Λ) (f : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) :
    (QuotientGroup.mk (vertex (f * RelLetter.listVal w) (revWord w)
        (w.length - k)) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex f w i) := by
  rw [vertex_revWord_of_end w f k]
  exact (mk_eq_mk_of_connected
    (span_mem_fam_of_isComp D f hlet hcomp : Connected D.fam lam f w i k)).symm

/-! ## The reversal of a geodesic word -/

/-- **The reversal of a geodesic word is a geodesic word**, on a symmetric
base.

This is the other half of `sep_comm`.  With `isComp_revWord` and
`mk_vertex_revWord_eq` it says that a separating coset of `S(f,g;D)` is
witnessed in `S(g,f;D)` by the reversed geodesic --- at the reversed indices,
and at the same coset.

The symmetry of the base is not a restriction imposed here: it is free by
`exists_symmetric_base'`, and without it `sep_comm` is outright false, as
`GGT/OsinTheorem54SepCommRefuted.lean` shows at `X = {t}`, `H = G`. -/
theorem isGeodesicWord_revWord (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) :
    IsGeodesicWord D g f (revWord w) := by
  obtain ⟨hlet, hprod, hlen⟩ := hw
  refine ⟨isLetter_of_mem_revWord D hsymm hlet, ?_, ?_⟩
  · rw [listVal_revWord, ← hprod]
    group
  · rw [length_revWord, hlen, wordDist_comm D.alphabet.symmetricGenerating f g]

end OsinComponents
end GGT
end GroupApproximation
