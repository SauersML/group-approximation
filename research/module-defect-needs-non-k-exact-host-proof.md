---
rg: 2
id: module-defect-needs-non-k-exact-host-proof
kind: route
title: Half-exactness of topological K-theory turns Baum--Connes with coefficients into K-exactness, and Higson--Kasparov prunes the a-T-menable hosts
target: module-defect-needs-non-k-exact-host
requires:
  - amenable-kernel-bc-transfer-and-ktop-half-exactness
  - osajda-monster-hosts-for-bc-module-route
---

**Part 1: Baum--Connes with coefficients implies K-exactness.**

Let `0 -> I -> A -> A/I -> 0` be a short exact sequence of `G`-algebras. By item 3 of
`amenable-kernel-bc-transfer-and-ktop-half-exactness`, the functor `B ↦ K^top_*(G; B)` is
half exact: the sequence

```text
K^top_j(G; I)  ->  K^top_j(G; A)  ->  K^top_j(G; A/I)
```

is exact at the middle, and assembly `mu_(G, -)` is natural in the coefficient algebra. Assume
`G` satisfies Baum--Connes with coefficients, so `mu_(G, I)`, `mu_(G, A)`, `mu_(G, A/I)` are all
isomorphisms. Naturality gives a commuting ladder

```text
K^top_j(G;I) --> K^top_j(G;A) --> K^top_j(G;A/I)
     |mu             |mu               |mu
     v               v                 v
K_j(I⋊_rG) --> K_j(A⋊_rG) --> K_j((A/I)⋊_rG)
```

whose vertical maps are isomorphisms and whose top row is exact at the middle. A middle-exact
row transported across vertical isomorphisms stays middle-exact, so the bottom row is exact at
`K_j(A ⋊_r G)`. As the sequence was arbitrary, `G` is K-exact. (No exactness of the C*-sequence
of crossed products is used: the argument is entirely on `K^top` and its assembly image.)

**Part 2: the contrapositive for a module triple.**

Take `A = C(X)`, `I = C_0(U)`, `A/I = C(Z)` with `X = V^`, `Z = W^perp`, `U = X \ Z` (the module
triple). Part 1 says: if `G` satisfies Baum--Connes with coefficients then this particular
sequence is middle-exact, i.e. there is no defect. Contrapositive: **a middle K-defect for the
module triple forces `G` to fail Baum--Connes with coefficients.**

A K-defect also forces `G` **non-exact**, by a separate and independent argument. If `G` is
exact then, by Kirchberg--Wassermann, the reduced crossed-product functor takes every short exact
sequence of `G`-algebras to a short exact sequence of C*-algebras; a short exact sequence of
C*-algebras has a six-term exact K-theory sequence, so `K_j(I ⋊_r G) -> K_j(A ⋊_r G) ->
K_j((A/I) ⋊_r G)` is exact at the middle and there is no defect. Hence a defect forces `G`
non-exact.

So a defect forces **both** conditions. They are logically independent inputs:
`exact => K-exact` (this paragraph) and `Baum--Connes-with-coefficients => K-exact` (Part 1),
and neither of `exact`, `Baum--Connes-with-coefficients` implies the other. In particular
non-exactness does **not** imply failure of Baum--Connes with coefficients -- Part 3 exhibits
groups that are non-exact yet satisfy it -- so the failure of Baum--Connes with coefficients is
the binding condition, not merely a restatement of non-exactness.

**Part 3: the a-T-menable non-exact hosts are pruned.**

By `osajda-monster-hosts-for-bc-module-route`:
- item (3): Osajda (arXiv:1406.5015, Theorem 6.3) gives finitely generated groups acting
  properly on CAT(0) cubical complexes without property A; a proper action on a CAT(0) cube
  complex yields the Haagerup property, so these groups are a-T-menable and non-exact;
- item (5): Higson--Kasparov (Invent. Math. 144 (2001)) makes every a-T-menable group satisfy
  Baum--Connes with coefficients.

Combining, these groups satisfy Baum--Connes with coefficients, hence by Part 1 are K-exact,
hence by Part 2 host no module defect. This is the witness that non-exactness does not imply
failure of Baum--Connes with coefficients, and that the correct necessary host condition is the
latter.

**Remark.** Parts 1--2 are the same Higson--Lafforgue--Skandalis diagram chase as in
`k-inexact-module-triple-refutes-trivial-coefficient-bc-proof`, read one level up: there the
hypothesis was surjectivity of one map and injectivity of another; here it is the full
isomorphism statement for all three coefficient algebras, giving the cleaner two-sided
conclusion "K-exact".
