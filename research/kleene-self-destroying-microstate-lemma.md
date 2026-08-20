---
rg: 2
id: kleene-self-destroying-microstate-lemma
kind: claim
title: A constant-gap halting-to-microstate compiler self-instantiates to a nonhyperlinear group
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
distinct_from:
  perfect-lcs-gap-implies-nonhyperlinear: that starts from one already constructed perfect LCS gap; this manufactures one fixed bad group from a uniform MACHINE-INDEXED compiler by Kleene self-reference.
  word-problem-of-finite-presentation-is-re: that enumerates proofs that a fixed word is trivial; this enumerates finite-dimensional attacks on its own compiled presentation.
---

Suppose a total computable compiler maps each Turing machine `M` to a finite
presentation `G_M=<S_M|R_M>` and a word `w_M`, with universal computable
rational constants

```text
delta > 0,                    0 < alpha < sqrt(2),
```

such that

```text
M does not halt  =>  w_M != 1 in G_M,                              (KSD1)

M halts          =>  every finite-dimensional unitary tuple U with
                     Def_R_M(U) < delta satisfies
                     ||w_M(U)-1||_2 <= alpha.                       (KSD2)
```

Then one can effectively produce a single finitely presented nonhyperlinear
group.

More precisely, choose computable `delta_0,beta` with
`0<delta_0<delta` and `alpha<beta<sqrt(2)`.  Kleene's recursion theorem gives
a machine which computes its own `(G_M,w_M)` and halts exactly when a search
finds a finite-dimensional unitary tuple in the open window

```text
Def_R_M(U) < delta_0,             ||w_M(U)-1||_2 > beta.             (KSD3)
```

The strict window makes the search semidecidable using a computable dense
family of finite-dimensional unitary tuples.  Halting would make its witness
contradict `(KSD2)`, so the fixed-point machine never halts.  By `(KSD1)` its
word is nontrivial.  Hyperlinearity would give microstates whose relator defect
tends to zero and whose marked-word distance tends to `sqrt(2)`, eventually
entering `(KSD3)` and making the search halt.  Hence the fixed-point group is
not hyperlinear.

The constraint `alpha<sqrt(2)` is part of the theorem: without a soundness
cutoff below the canonical separation of a nonidentity group element, the
claimed contradiction with hyperlinearity does not follow.
