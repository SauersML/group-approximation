---
rg: 2
id: akkstv-expansion-parallel-repetition-citation
kind: route
title: Import Theorems 4.1 and 4.3 and Lemma 4.2 of Arora--Khot--Kolla--Steurer--Tulsiani--Vishnoi, Unique Games on Expanding Constraint Graphs are Easy (STOC 2008)
target: akkstv-expansion-parallel-repetition-bound
requires: []
---

This is a literature import, and credit is the authors' in full. The source is
S. Arora, S. A. Khot, A. Kolla, D. Steurer, M. Tulsiani and N. K. Vishnoi,
*Unique Games on Expanding Constraint Graphs are Easy*, STOC'08. The same
extended abstract is imported in `unique-games-on-expanding-constraint-graphs-are-easy-citation`.

The quotations are from text extracted with `pypdf` on 2026-09-18 from
`dsteurer.org/paper/ugexpansion.pdf`. Line breaks and hyphenation are undone,
and symbols are transcribed.

* **Setting (Section 4).** "In this section, we give an upper bound on the
  amortized value ω(U) = sup_r opt(U^⊗r)^(1/r) of bipartite unique game U in
  terms of the expansion of its constraint graph. Here U^⊗r denotes the game
  obtained by playing the game U for r rounds in parallel. We follow an approach
  proposed by Feige and Lovász [9]. Their approach is based on the SDP in
  Figure 3, which is a relaxation for the value of a bipartite unique game. Let
  σ(U) denote the value of this SDP relaxation. The following theorem is a
  consequence of the fact σ(U^⊗r) = σ(U)^r."
* **Theorem 4.1 ([9]).** "For every bipartite unique game U, ω(U) ≤ σ(U)."
* **Lemma 4.2.** "If σ(U) = 1 − η then the value of the SDP in Figure 1 is at
  least 1 − 2η."
* **Figure 3 (Feige--Lovász SDP for Unique Games).** "Maximize
  E_((v,w)∈E) E_(i∈[k]) ⟨v_i, w_(π_vw(i))⟩ Subject to ∀ v∈V, w∈W, i,j∈[k]
  ⟨v_i, w_j⟩ ≥ 0; ∀ v∈V, v′∈V Σ_(i,i′) |⟨v_i, v′_i′⟩| ≤ k;
  ∀ w∈W, w′∈W Σ_(j,j′) |⟨w_j, w′_j′⟩| ≤ k."
* **Theorem 4.3.** "If U is 2-prover 1-round unique game on alphabet [k] with
  value at most 1−ε, then the value U played in parallel for r rounds is at
  most (1 − Ω(ε·λ/log 1/ε))^r, where G is the graph corresponding to the
  questions to the two provers. In particular, the amortized value w(U) is at
  most 1 − Ω(ε·λ/log 1/ε)."
* **Proof of Theorem 4.3.** "Following the approach in [9], it is sufficient to
  show σ(U) ≤ 1 − Ω(ελ/log 1/ε). Suppose that σ(U) = 1−η. Then by Lemma 4.2,
  the value of the SDP in Figure 1 is at least 1 − 2η. By Theorem 2.4, it
  follows that opt(U) ≥ 1 − O(η log(λ/η)/λ). On the other hand, opt(U) ≤ 1−ε.
  Hence, ε = O(η log(λ/η)/λ) and therefore η = Ω(λε/log 1/ε), as claimed."

**Reading.**

1. `λ` is the paper's global notation, "the second smallest eigenvalue of the
   normalized Laplacian of a graph G, denoted by λ := λ_2(G)" (Section 1, quoted
   in `unique-games-on-expanding-constraint-graphs-are-easy-citation`). The
   normalized Laplacian `I − D^(-1/2) A D^(-1/2)` has the spectrum of `I` minus
   the constraint walk. So `λ` is `1 − λ_2(walk)`, and "the walk has at most one
   eigenvalue above `1 − λ`" is the same condition.
2. The final step, "ε = O(η log(λ/η)/λ) and therefore η = Ω(λε/log 1/ε)",
   inverts `x ↦ x log(λ/x)`. That inversion is meaningful for `ε` bounded away
   from 1. The downstream claim therefore uses the theorem only for `ε <= 1/e`,
   where `ln(1/ε) >= 1`.
3. The `Ω(.)` is read as one absolute constant `c_R > 0`. It may be decreased at
   will, since a smaller rate gives a weaker true bound. So `c_R <= 1/2` may be
   assumed. The bound `(1 − x)^r` is then meaningful, with `x = c_R ε λ/ln(1/ε)`
   in `[0,1]`, because `λ <= 2` and `ε/ln(1/ε) <= 1/e` on `(0, 1/e]`.
4. Theorem 4.1 gives `opt(U^⊗r) <= ω(U)^r <= σ(U)^r` directly from the
   definition of `ω` as a supremum.
