import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic

/-!
# A component of a segment is a component of the word

The second fact Lemma 5.9 needs, and the one where its two boundary cases live.

A component `[a,b)` of the segment `(w.drop k).take m` sits at `[k+a, k+b)` in
`w`, but it is a *maximal* run there only when its two bounding letters are
still inside the segment.  That is exactly `1 ≤ a` and `b < |segment|`, and
under those two conditions all five clauses transfer, the bounding letters being
the segment's own and the span being literally the same element.

## Why Lemma 5.9 needs no more than this

In 5.9 the segment runs from the END `k` of one component to the START `j` of
the next, and the two excluded cases are impossible there --- not delicate, but
ruled out by the two components' own maximality:

* `a = 0` would put a component start at `w`'s letter `k`, and the FIRST
  component's closing clause says that letter is not a component letter;
* `b = |segment|` would put a component letter at `w`'s index `j - 1`, and the
  SECOND component's opening clause says that letter is not one.

So no merge can occur at either end, and no comparison of spans across a merge
is needed --- which is what I had expected to need and do not.

Unconditional.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **Reading a letter of the word as a letter of a segment**, with the index
supplied by an equation rather than computed in place --- rewriting an index
inside a `getElem` breaks the motive. -/
theorem getElem_segment' (w : List (RelLetter G Λ)) (i m a t : ℕ)
    (ha : a < ((w.drop i).take m).length) (ht : t < w.length) (hti : t = i + a) :
    w[t]'ht = ((w.drop i).take m)[a]'ha := by
  subst hti
  exact (getElem_segment w i m a ha ht).symm

omit [Group G] in
/-- **A component of a segment, not touching either end of it, is a component of
the whole word.** -/
theorem isComp_of_isComp_segment (lam : Λ) (w : List (RelLetter G Λ))
    {k m a b : ℕ} (hcomp : IsComp lam ((w.drop k).take m) a b)
    (ha : 1 ≤ a) (hb : b < ((w.drop k).take m).length)
    (hkm : k + m ≤ w.length) :
    IsComp lam w (k + a) (k + b) := by
  obtain ⟨hab, hbl, hrange, hpre, hpost⟩ := hcomp
  have hseg : ((w.drop k).take m).length = min m (w.length - k) := by
    rw [List.length_take, List.length_drop]
  have hml : ((w.drop k).take m).length ≤ m := by
    rw [hseg]
    omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro t ht1 ht2 ht
    have hts : t - k < ((w.drop k).take m).length := by omega
    rw [getElem_segment' w k m (t - k) t hts ht (by omega)]
    exact hrange (t - k) (by omega) (by omega) hts
  · intro t hteq ht hc
    have hts : a - 1 < ((w.drop k).take m).length := by omega
    rw [getElem_segment' w k m (a - 1) t hts ht (by omega)] at hc
    exact hpre (a - 1) (by omega) hts hc
  · intro hkb hc
    rw [getElem_segment' w k m b (k + b) hb hkb rfl] at hc
    exact hpost hb hc

end OsinComponents
end GGT
end GroupApproximation
