import GroupApproximation.GGT.OsinTheorem54SepTransport

/-!
# The conversion step at a general family

`GGT/OsinTheorem54SepTransport.lean` proves, for a one-member family, that a
`D'`-avoiding word reading no new letter inside `H` converts into a `D`-avoiding
word.  Osin's Theorem 5.4 is stated for a finite collection `{H_λ}`, and
hull-relator2's model has two peripheral subgroups, so the same step is needed at
a general index type.  This module is that statement; the primed names are the
general-`Λ` variants of the unprimed ones next door.

## What changes, and what does not

`d̂_λ` is measured one `λ` at a time, while a new base letter lies in `H_μ` for
*some* `μ`.  So the hypothesis on `N` weakens from `N ⊆ H` to
`∀ x ∈ N, ∃ μ, x ∈ H_μ`, and the demotion sends such an `x` to `comp μ x`.

The gain is that **a cross-family letter is free**.  If `x ∉ H_λ`, then the `μ`
the hypothesis supplies is not `λ`, so `comp μ x` is not a `λ`-letter at all;
`AvoidsFrom … λ` never constrains it, and the demotion is legal at *every*
vertex.  Only a new letter that lies in `H_λ` itself can obstruct.  That is why
`noNew` below carries `x ∈ D.fam lam` as an antecedent: the one-member version
had no such distinction to make, and asking for the vertex condition at every
new letter would be strictly stronger than the argument needs --- and stronger
than the peel in `GGT/OsinTheorem54SepFiniteFam.lean` can supply, since the
letter it cuts at must lie in `H_λ` for the cut vertex to stay in the coset.

The `comp` case is simpler here than at `Unit`: the letter is carried across
unchanged, where the one-member version had to rebuild it at the sole index.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The conversion, at a general family.**  A `D'`-avoiding word that reads no
new `H_lam`-letter at a vertex of `H_lam` converts, letter by letter and with no
change of length or value, into a `D`-avoiding word.

A new base letter lying in `H_lam` is demoted to `comp lam x`, which the
hypothesis places outside `H_lam`; one lying outside `H_lam` is demoted to
`comp mu x` for the `mu` that `hN` supplies, and that letter is not a
`lam`-letter, so avoidance never looks at it. -/
theorem exists_dWord_of_noNewLetterInFam' (D D' : RelGenSet G Λ) (lam : Λ)
    (hfam : D'.fam = D.fam) {N : Set G}
    (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu)
    (hbase : D'.base ⊆ D.base ∪ N) :
    ∀ (w : List (RelLetter G Λ)) (v : G),
      (∀ a ∈ w, D'.IsLetter a) →
      AvoidsFrom D'.fam lam w v →
      (∀ (j : ℕ) (hj : j < w.length) (x : G),
        (w[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base → x ∈ D.fam lam →
          vertex v w j ∉ D.fam lam) →
        ∃ w' : List (RelLetter G Λ),
          (∀ a ∈ w', D.IsLetter a) ∧
          RelLetter.listVal w' = RelLetter.listVal w ∧
          AvoidsFrom D.fam lam w' v ∧ w'.length = w.length := by
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
          (t[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base → x ∈ D.fam lam →
            vertex (v * a.val) t j ∉ D.fam lam := by
        intro j hj x hx hxN hxb hxlam
        have hj' : j + 1 < (a :: t).length := by
          simp only [List.length_cons]
          omega
        have hget : ((a :: t)[j + 1]'hj') = RelLetter.base x := by
          rw [List.getElem_cons_succ]
          exact hx
        have hstep := hnew (j + 1) hj' x hget hxN hxb hxlam
        rwa [vertex_cons_succ] at hstep
      obtain ⟨t', hlt', hvt', havt', hlent'⟩ := ih (v * a.val) hlet' htail hnew'
      have hhead' : ∃ b : RelLetter G Λ, D.IsLetter b ∧ b.val = a.val ∧
          ¬ (b.IsCompOf lam ∧ v ∈ D.fam lam) := by
        cases a with
        | comp mu y =>
            have hy : y ∈ D.fam mu := by
              have hy' : y ∈ D'.fam mu := hlet _ List.mem_cons_self
              rw [hfam] at hy'
              exact hy'
            refine ⟨RelLetter.comp mu y, hy, rfl, ?_⟩
            rintro ⟨hc, hv⟩
            refine hhead ⟨hc, ?_⟩
            rw [hfam]
            exact hv
        | base x =>
            have hx : x ∈ D'.base := hlet _ List.mem_cons_self
            rcases hbase hx with hxD | hxN
            · exact ⟨RelLetter.base x, hxD, rfl, fun hc => hc.1⟩
            · by_cases hxb : x ∈ D.base
              · exact ⟨RelLetter.base x, hxb, rfl, fun hc => hc.1⟩
              · by_cases hxlam : x ∈ D.fam lam
                · have hvnot : v ∉ D.fam lam :=
                    hnew 0 (by simp) x rfl hxN hxb hxlam
                  exact ⟨RelLetter.comp lam x, hxlam, rfl, fun hc => hvnot hc.2⟩
                · obtain ⟨mu, hmu⟩ := hN x hxN
                  have hmune : mu ≠ lam := by
                    intro hml
                    rw [hml] at hmu
                    exact hxlam hmu
                  exact ⟨RelLetter.comp mu x, hmu, rfl, fun hc => hmune hc.1⟩
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

/-- **The ball inclusion at such a witness**, at a general family. -/
theorem mem_relBall_of_noNewLetterInFam' (D D' : RelGenSet G Λ) (lam : Λ)
    (hfam : D'.fam = D.fam) {N : Set G}
    (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu)
    (hbase : D'.base ⊆ D.base ∪ N) {n : ℕ} {h : G} (hh : h ∈ D.fam lam)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D'.IsLetter a)
    (hval : RelLetter.listVal w = h) (hav : AvoidsFrom D'.fam lam w 1)
    (hlen : w.length ≤ n)
    (hnew : ∀ (j : ℕ) (hj : j < w.length) (x : G),
      (w[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base → x ∈ D.fam lam →
        vertex 1 w j ∉ D.fam lam) :
    h ∈ D.relBall lam n := by
  obtain ⟨w', hlt', hvt', havt', hlent'⟩ :=
    exists_dWord_of_noNewLetterInFam' D D' lam hfam hN hbase w 1 hlet hav hnew
  refine ⟨hh, w', hlt', ?_, havt', ?_⟩
  · rw [hvt', hval]
  · rw [hlent']
    exact hlen

end OsinComponents
end GGT
end GroupApproximation
