---
rg: 2
id: boone-higman-via-infinite-shift-compiler
kind: route
title: Pad Clapham's envelope by an infinite cyclic factor before shift compilation
target: boone-higman-conjecture
requires: [infinite-shift-higman-compiler, clapham-fp-embedding-preserves-word-problem, mallery-zaremsky-shift-similar-envelope, fp-strongly-shift-similar-admits-type-a-action, type-a-action-gives-boone-higman-for-subgroups]
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Let `G` be finitely generated with solvable word problem.

1. By [[clapham-fp-embedding-preserves-word-problem]], embed `G <= P_0`,
   where `P_0` is finitely presented and has decidable word problem.
2. Put `P=P_0 x Z`.  If `P_0=<X|R>`, then

   ```text
   P=<X,t | R, [t,x] (x in X)>.
   ```

   Thus `P` is finitely presented and infinite, and `P_0 -> P`,
   `p |-> (p,0)`, is injective.  Its word problem is decidable: commute all
   `t` letters to one side, compute their exponent sum, and invoke the word-
   problem algorithm in `P_0` on the projected `X`-word.
3. Apply [[infinite-shift-higman-compiler]] to choose `nu:P->N` for which
   `E_nu(P)` is finitely presented.
4. By [[mallery-zaremsky-shift-similar-envelope]], `E_nu(P)` is strongly
   shift-similar and contains `P`.
5. By [[fp-strongly-shift-similar-admits-type-a-action]], its natural action
   is of type (A).  By [[type-a-action-gives-boone-higman-for-subgroups]],
   every subgroup of `E_nu(P)`, hence `G`, embeds in a finitely presented
   simple group.

Therefore the infinite-input compiler implies the Boone--Higman conjecture.
`∎`

The `x Z` padding is load-bearing only for cardinality and costs neither
finite presentation nor decidability.
