import GroupApproximation.Sofic.NonCrossingEdgeBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The degree bound: in a non-crossing chord diagram, some face has degree ≤ 4

`NonCrossingEdgeBound` proves the outerplanar edge bound `|E| + 3 ≤ 2·|S|` and
isolates the arithmetic it feeds.  This file joins the two by the missing step,
which is double counting: **summing the degrees of a set of vertices counts each
chord at most twice.**

## The statement

`exists_degree_le_four` — let `E` be a non-crossing set of chords on a finite
`S ⊆ ℕ`, and let `V₀` be nonempty with one point of `S` fewer.  Then some
`v ∈ V₀` meets at most four chords.

Read on the run graph of a conjugate-product diagram: the vertices are the
blocks, `V₀` the relator blocks, the one omitted point the boundary block, the
chords the maximal runs.  **Some relator block meets at most four runs.**  That
is the degree bound the curvature count has been missing, and combined with

    a relator block with a boundary run and at most three other runs is a shell

it is exactly `CurvatureAssembly.ShellGate`'s hypothesis (D).

## Why four, and why that is the right number

Four, not three.  A relator block meeting four runs one of which is the boundary
run has three interior runs, and three is what `CurvatureAssembly.length_arc_of_shell`
subtracts: `|δ| > (1 − 3λ)|r|`.  A block with four runs and *no* boundary run is
not a shell, but it also cannot occur once `C'(1/6)` is read: its whole boundary
would be covered by four pieces, each shorter than `λ·|r| ≤ |r|/6`, so
`|r| < 4|r|/6`.  `MatchingRunPiece.six_mul_length_lt_of_relator_run` is that
bound, and `no_interior_block_of_few_runs` below is the arithmetic.

So "degree at most four" plus "`C'(1/6)` on the interior runs" is a shell, and
the count needs nothing sharper.

## The proof

Two lines of double counting and then `NonCrossingEdgeBound`:

* `sum_degree_le` — `∑_{v ∈ V₀} deg(v) ≤ 2·|E|`, because for a fixed chord the
  vertices it is incident to form a subset of a two-element set.  This is the
  handshake inequality; equality would need `V₀ = S`, which is exactly what is
  given up by omitting the boundary.
* if every `v ∈ V₀` had `deg(v) ≥ 5` then `5·|V₀| ≤ 2·|E| ≤ 4·|S| − 6 =
  4·|V₀| − 2`, and `ℕ` refuses.

Nothing here mentions a group, a word or a matching.  What is still missing for
`ShellGate` is the construction of the run graph — that the maximal runs of the
cancellation matching are a non-crossing chord set on the blocks — not the
counting that runs on it.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

namespace NonCrossing

/-! ## 1.  Incidence -/

/-- **The chords at a vertex.**  A chord counts once even if it is a loop, which
cannot happen here since chords are ordered strictly. -/
def star (E : Finset (ℕ × ℕ)) (v : ℕ) : Finset (ℕ × ℕ) :=
  E.filter fun p => p.1 = v ∨ p.2 = v

theorem mem_star {E : Finset (ℕ × ℕ)} {v : ℕ} {p : ℕ × ℕ} :
    p ∈ star E v ↔ p ∈ E ∧ (p.1 = v ∨ p.2 = v) := by
  rw [star, Finset.mem_filter]

/-- **The handshake inequality.**  Summing the degrees over any set of vertices
counts each chord at most twice, because a chord is incident to at most two
vertices.

Stated as an inequality rather than the usual equality: the vertex set is a
*subset*, so chords with an endpoint outside it are counted once or not at
all. -/
theorem sum_degree_le (E : Finset (ℕ × ℕ)) (V₀ : Finset ℕ) :
    ∑ v ∈ V₀, (star E v).card ≤ 2 * E.card := by
  have hcongr : ∀ v ∈ V₀, (star E v).card
      = ∑ p ∈ E, if p.1 = v ∨ p.2 = v then 1 else 0 := by
    intro v _
    rw [star, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hbound : ∀ p ∈ E, (∑ v ∈ V₀, if p.1 = v ∨ p.2 = v then 1 else 0) ≤ 2 := by
    intro p _
    have hrw : (∑ v ∈ V₀, if p.1 = v ∨ p.2 = v then 1 else 0)
        = (V₀.filter fun v => p.1 = v ∨ p.2 = v).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hrw]
    have hsub : (V₀.filter fun v => p.1 = v ∨ p.2 = v) ⊆ ({p.1, p.2} : Finset ℕ) := by
      intro v hv
      obtain ⟨-, hv'⟩ := Finset.mem_filter.mp hv
      rcases hv' with h | h
      · rw [← h]
        exact Finset.mem_insert_self _ _
      · rw [← h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    rw [Finset.card_singleton]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_comm]
  calc (∑ p ∈ E, ∑ v ∈ V₀, if p.1 = v ∨ p.2 = v then 1 else 0)
      ≤ ∑ _p ∈ E, 2 := Finset.sum_le_sum hbound
    _ = E.card * 2 := Finset.sum_const_nat fun _ _ => rfl
    _ ≤ 2 * E.card := by omega

/-! ## 2.  The degree bound -/

/-- **Some face has degree at most four.**

`E` is a non-crossing set of chords on the finite set `S ⊆ ℕ`, and `V₀` is
nonempty with one point of `S` fewer — the omitted point being the boundary
block, in the intended reading.  Then some point of `V₀` meets at most four
chords.  Nonemptiness is not decoration: for `V₀ = ∅` the conclusion is false and
the hypotheses hold.

If not, summing the degrees over `V₀` alone gives `5·|V₀| ≤ 2·|E|`, while
`NonCrossingEdgeBound.two_mul_card_le` gives `2·|E| + 6 ≤ 4·|S| = 4·|V₀| + 4`.
Together `5·|V₀| + 6 ≤ 4·|V₀| + 4`, which `ℕ` refuses outright. -/
theorem exists_degree_le_four {S : Finset ℕ} {E : Finset (ℕ × ℕ)} {V₀ : Finset ℕ}
    (hord : ∀ p ∈ E, p.1 < p.2)
    (hmem : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S)
    (hnc : ∀ p ∈ E, ∀ q ∈ E, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))
    (hcard : V₀.card + 1 = S.card) (hF : 1 ≤ V₀.card) :
    ∃ v ∈ V₀, (star E v).card ≤ 4 := by
  by_contra hcon
  have hall : ∀ v ∈ V₀, 5 ≤ (star E v).card := by
    intro v hv
    by_contra hlt
    exact hcon ⟨v, hv, by omega⟩
  have h5 : 5 * V₀.card ≤ ∑ v ∈ V₀, (star E v).card := by
    have hle : (∑ _v ∈ V₀, 5) ≤ ∑ v ∈ V₀, (star E v).card := Finset.sum_le_sum hall
    have hc : (∑ _v ∈ V₀, 5) = V₀.card * 5 := Finset.sum_const_nat fun _ _ => rfl
    omega
  have hsum := sum_degree_le E V₀
  have hedge := two_mul_card_le S E hord hmem hnc (by omega)
  omega

end NonCrossing

/-! ## 3.  Four runs and no boundary run is impossible -/

/-- **A relator block all of whose runs are pieces has at least seven of them.**

The runs partition the block's boundary, so their lengths sum to `|r|`; each is a
piece, so `6·|run| < |r|`.  With `d` runs, `6·|r| = 6·∑ < d·|r|`, so `6 < d`.

Stated on the sums so that the diagram half can hand over exactly what it has:
`total` is `|r|` and `d` the number of runs; positivity of `total` is not needed,
since `6 * total < d * total` already forces it. -/
theorem seven_le_of_all_pieces {d total : ℕ}
    (hsum : 6 * total < d * total) : 7 ≤ d := by
  rcases Nat.lt_or_ge d 7 with h | h
  · exfalso
    have hle : d * total ≤ 6 * total := Nat.mul_le_mul_right total (by omega)
    omega
  · exact h

/-- **So a block of degree at most four meets the boundary.**  Contrapositive of
the previous statement, in the form the shell argument reads it: a relator block
with at most four runs, all of them pieces, cannot exist. -/
theorem no_interior_block_of_few_runs {d total : ℕ}
    (hsum : 6 * total < d * total) (hd : d ≤ 4) : False := by
  have := seven_le_of_all_pieces hsum
  omega

end SmallCancellationRouter
end GroupApproximation
