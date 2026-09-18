---
rg: 2
id: oligomorphic-fp-infinity-actor-without-thompson-f
kind: claim
title: Some group acts oligomorphically on an infinite set with all finite-set stabilizers of type FP_∞ and contains no copy of Thompson's group F (FFKLZ Question 2.4)
root: true
distinct_from:
  thompson-f-has-infinite-cohomological-dimension: that records one property of F; this asks for a group with F's oligomorphic finiteness behaviour but without F, which must have infinite cohomological dimension.
  extensions-with-f-free-outer-kernel-contain-thompson-f: that shows non-faithful actions through Thompson-like quotients cannot answer this question unless the kernel's Out contains F; this is the question itself.
---

**OPEN.** Fournier-Facio--Kropholler--Lyman--Zaremsky, *Finiteness properties of stabilisers
of oligomorphic actions*, arXiv:2506.02319v2 (to appear in Publ. Mat.), TeX
`oligomorphic.tex` l.282--284:

> "Does there exist a group $G$ satisfying the hypotheses of Lemma~\ref{lem:converse} (with
> $S$ infinite) that does not contain a copy of Thompson's group $F$?"

Lemma 2.3 (l.271--274): "Let $G$ be a group acting oligomorphically on a set $S$. If the
stabiliser in $G$ of every non-empty finite subset of $S$ is of type $\FP_\infty$, then $G$
is of type $\FP_\infty$." Faithfulness is not assumed. Call such a pair `(G, S)` with `S`
infinite and `G` free of copies of `F` a **witness**.

**Known constraints (FFKLZ, l.286--293).**
- By their Theorem 1.1 (l.155--158) no witness lies in Kropholler's class `HF`. So there
  is none among linear groups, soluble groups, groups of finite vcd, or Kac--Moody lattices
  over finite fields (which act with finite stabilizers on the product of their two
  buildings).
- A witness has infinite cohomological dimension.
- A torsion-free finitely presented witness would answer Witzel's question.
- Branch groups cannot act oligomorphically.

## Attempts

1. **Closure, exclusions and hiding F in a kernel (2026-09-18, lane bh-free-24; elementary
   lane lemmas, not reviewed).**
   - **Closure under stabilizers.** If `(G, S)` is a witness and `A ⊂ S` is finite, then
     `(G_A, S∖A)` is a witness.
     - It is oligomorphic, because `G_A`-orbits of `k`-subsets `B` of `S∖A` inject into
       `G`-orbits of pairs `(A', B')` of disjoint sets of sizes `|A|` and `k`.
     - `(G_A)_B` is commensurable with `G_{A∪B}`, and FP_∞ is a commensurability invariant
       (FFKLZ l.160).
   - **Residually finite witnesses suffice.** A residually finite group has no copy of `F`,
     because `F'` is infinite and simple. So any residually finite group satisfying Lemma 2.3's
     hypotheses with `S` infinite is a witness. By FFKLZ Theorem 1.1 it lies outside `HF`, so
     it is not linear.
   - **Non-faithful actions do not help.** Let the action have kernel `K`, and suppose
     `Out(K)` contains no `F`, for example when `K` is finite, finitely generated abelian, or
     has residually finite `Out`. Then `G` contains `F` as soon as `G/K` does
     (`extensions-with-f-free-outer-kernel-contain-thompson-f`). In particular no central
     extension of `F`, `T`, `V` or another Thompson-like actor acting through the quotient is
     a witness (`central-extensions-of-thompson-f-contain-f`). A witness must therefore come
     from a faithful `F`-free oligomorphic action `G/K ↷ S`, unless `Out(K)` contains `F`.
   - **Finitary extensions reduce to the base.** `H = FSym(S) ⋊ G` acts highly transitively
     and contains `F` exactly when `G` does, because `F ∩ FSym(S) = 1`. `H` has finite
     subgroups of unbounded order. So if `H` were of type FP_∞, Kropholler's bounded-torsion
     theorem for `HF` groups of type FP_∞ would put `H` outside `HF`. That theorem is cited
     from memory, not read.
     - By extension-closure of `HF`, this needs `G ∉ HF`.
     - The known finiteness criterion (`finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`)
       asks for oligomorphic behaviour of `G` itself.
     - So finitary extensions do not create witnesses from `HF` bases.
   - **Gap.** A faithful oligomorphic action of an `F`-free group outside `HF` with FP_∞
     finite-set stabilizers. FFKLZ (l.288--291) list only two sources of `F`-free groups
     outside `HF`: small-cancellation groups with fixed-point properties (not FP_2), and
     groups with jump rational cohomology such as Grigorchuk's group.
   - **A finitely presented example.** Grigorchuk's group has a finitely presented ascending
     HNN extension (Grigorchuk, via Lysenok's presentation; cited from memory, not read).
     - It lies outside `HF`, because it contains Grigorchuk's group.
     - It contains no `F`: its base is a directed union of conjugates of a torsion group,
       so a copy of `F` would meet it trivially and embed in `Z`.
     - Its finiteness beyond FP_2 and its oligomorphic actions were not examined.
