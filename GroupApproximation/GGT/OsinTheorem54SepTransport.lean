import GroupApproximation.GGT.OsinTheorem54SepRuns

/-!
# Enlarging the base inside the family: the conversion step

`GGT/OsinTheorem54SepSymmetric.lean` symmetrises the relative generating set, and
`alphabet_eq_of_symmetrizedBase` shows the alphabet does not change, so the
hyperbolicity clause of `↪_h` transports for free.  What still has to move is
local finiteness of `d̂_λ`, the relative balls growing with the base.  This module
proves the step on which that rests.

## The only obstruction is a new letter read inside `H`

Let `X ⊆ X' ⊆ X ∪ N` with `N ⊆ H`.  An avoiding path for `X'` uses letters that
are either letters for `X` already, or elements of `N`.  An `N`-letter is an
element of `H`, so it is *also* available to `X` --- not as a base letter, but as
an `H`-letter.  Reading it that way is legal at every vertex outside `H`, and
illegal at a vertex of `H`; and that is the whole difference between the two
relative metrics.

`exists_dWord_of_noNewLetterInFam` is that observation: a `D'`-avoiding word that
never reads a new letter at a vertex of `H` converts, letter by letter and with
no change of length or value, into a `D`-avoiding word.  Each new base letter is
demoted to the `H`-letter with the same value, which the hypothesis places
outside `H`, so the avoidance condition survives; every other letter is carried
across unchanged.

`mem_relBall_of_mem_relBall'` reads that off at the balls: such a witness puts
its element in `D.relBall`, at the same radius.

## What is left of the transport

A general `D'`-avoiding path may of course read a new letter inside `H`, and then
this lemma does not apply.  The remaining argument splits the path at exactly
those letters: each is an element of the finite set `N`, and between consecutive
ones the path runs from a vertex of `H` to a vertex of `H` reading no new letter
inside `H`, so its value lies in `D.relBall` by the lemma above.  A path of
length at most `n` is cut into at most `n` such pieces, so its value is a product
of at most `n` factors drawn from `N ∪ D.relBall () n` --- a finite set, since
`N` is finite by `finite_base_asymmetry` and `D.relBall () n` is finite by local
finiteness for `D`.  That decomposition is the next write; the conversion here is
the step that makes each piece land in `D.relBall`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u

variable {G : Type u} [Group G]

/-! ## Demoting the new base letters -/

/-- **A `D'`-avoiding word that reads no new letter inside `H` is a `D`-avoiding
word.**

The new base letters --- those in `N` and not in `D.base` --- are elements of
`H`, so `D` has them as `H`-letters; reading one that way is forbidden only at a
vertex of `H`, which is exactly what the hypothesis excludes.  Every other letter
crosses unchanged, and the length and the value are untouched. -/
theorem exists_dWord_of_noNewLetterInFam (D D' : RelGenSet G Unit)
    (hfam : D'.fam = D.fam) {N : Set G}
    (hN : N ⊆ ((D.fam () : Subgroup G) : Set G))
    (hbase : D'.base ⊆ D.base ∪ N) :
    ∀ (w : List (RelLetter G Unit)) (v : G),
      (∀ a ∈ w, D'.IsLetter a) →
      AvoidsFrom D'.fam () w v →
      (∀ (j : ℕ) (hj : j < w.length) (x : G),
        (w[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base →
          vertex v w j ∉ D.fam ()) →
        ∃ w' : List (RelLetter G Unit),
          (∀ a ∈ w', D.IsLetter a) ∧
          RelLetter.listVal w' = RelLetter.listVal w ∧
          AvoidsFrom D.fam () w' v ∧ w'.length = w.length := by
  intro w
  induction w with
  | nil =>
      intro v _ _ _
      exact ⟨[], by simp, rfl, trivial, rfl⟩
  | cons a t ih =>
      intro v hlet hav hnew
      obtain ⟨hhead, htail⟩ := hav
      have hlet' : ∀ b ∈ t, D'.IsLetter b :=
        fun b hb => hlet b (List.mem_cons_of_mem a hb)
      have hnew' : ∀ (j : ℕ) (hj : j < t.length) (x : G),
          (t[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base →
            vertex (v * a.val) t j ∉ D.fam () := by
        intro j hj x hx hxN hxb
        have hj' : j + 1 < (a :: t).length := by
          simp only [List.length_cons]
          omega
        have hget : ((a :: t)[j + 1]'hj') = RelLetter.base x := by
          rw [List.getElem_cons_succ]
          exact hx
        have hstep := hnew (j + 1) hj' x hget hxN hxb
        rwa [vertex_cons_succ] at hstep
      obtain ⟨t', hlt', hvt', havt', hlent'⟩ := ih (v * a.val) hlet' htail hnew'
      -- the head letter, demoted if it is new
      have hhead' : ∃ b : RelLetter G Unit, D.IsLetter b ∧ b.val = a.val ∧
          ¬ (b.IsCompOf () ∧ v ∈ D.fam ()) := by
        cases a with
        | comp lam y =>
            have hy : y ∈ D.fam () := by
              have hy' : y ∈ D'.fam lam := hlet _ List.mem_cons_self
              rw [hfam] at hy'
              exact hy'
            have hvnot : v ∉ D.fam () := by
              intro hv
              refine hhead ⟨Subsingleton.elim lam (), ?_⟩
              rw [hfam]
              exact hv
            exact ⟨RelLetter.comp () y, hy, rfl, fun hc => hvnot hc.2⟩
        | base x =>
            have hx : x ∈ D'.base := hlet _ List.mem_cons_self
            rcases hbase hx with hxD | hxN
            · exact ⟨RelLetter.base x, hxD, rfl, fun hc => hc.1⟩
            · by_cases hxb : x ∈ D.base
              · exact ⟨RelLetter.base x, hxb, rfl, fun hc => hc.1⟩
              · have hvnot : v ∉ D.fam () :=
                  hnew 0 (by simp) x rfl hxN hxb
                exact ⟨RelLetter.comp () x, hN hxN, rfl, fun hc => hvnot hc.2⟩
      obtain ⟨b, hbD, hbval, hbav⟩ := hhead'
      refine ⟨b :: t', ?_, ?_, ⟨hbav, ?_⟩, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with hceq | hc'
        · rw [hceq]
          exact hbD
        · exact hlt' c hc'
      · rw [listVal_cons, listVal_cons, hbval, hvt']
      · rw [hbval]
        exact havt'
      · rw [List.length_cons, List.length_cons, hlent']

/-- **The ball inclusion at such a witness.**  An element of `D'.relBall` whose
witnessing path reads no new letter inside `H` lies in `D.relBall`, at the same
radius. -/
theorem mem_relBall_of_noNewLetterInFam (D D' : RelGenSet G Unit)
    (hfam : D'.fam = D.fam) {N : Set G}
    (hN : N ⊆ ((D.fam () : Subgroup G) : Set G))
    (hbase : D'.base ⊆ D.base ∪ N) {n : ℕ} {h : G} (hh : h ∈ D.fam ())
    {w : List (RelLetter G Unit)} (hlet : ∀ a ∈ w, D'.IsLetter a)
    (hval : RelLetter.listVal w = h) (hav : AvoidsFrom D'.fam () w 1)
    (hlen : w.length ≤ n)
    (hnew : ∀ (j : ℕ) (hj : j < w.length) (x : G),
      (w[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base →
        vertex 1 w j ∉ D.fam ()) :
    h ∈ D.relBall () n := by
  obtain ⟨w', hlt', hvt', havt', hlent'⟩ :=
    exists_dWord_of_noNewLetterInFam D D' hfam hN hbase w 1 hlet hav hnew
  refine ⟨hh, w', hlt', ?_, havt', ?_⟩
  · rw [hvt', hval]
  · rw [hlent']
    exact hlen

end OsinComponents
end GGT
end GroupApproximation
