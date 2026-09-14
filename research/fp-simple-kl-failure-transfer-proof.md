---
rg: 2
id: fp-simple-kl-failure-transfer-proof
kind: route
title: Kuznetsov's semi-decision procedure down, normal-form transport of the certificate up
target: fp-simple-kl-failure-transfers-through-decidable-groups
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

## Item 1

Let `S = <X | R>` with `X, R` finite, `S` simple, and suppose failure occurs
over `S`.  Then `S != 1`, since the trivial group has no nontrivial element to
lose.  Kuznetsov's argument, as written in
`research/artifacts/boone-higman-audit-2026-08-17.md` §B.1, decides the word
problem.  Given `v in F(X)`, run two procedures in parallel:
- enumerate products of conjugates of `R^(±1)`, halting if `v` appears;
- enumerate consequences of `R ∪ {v}`, halting once every `x in X` has been
  derived.

The first halts exactly when `v = 1` in `S`.  If `v != 1`, then `<<v>>` is a
nontrivial normal subgroup of the simple group `S`, so it is `S` and the second
halts.  If `v = 1`, then `<X | R, v> = S != 1`, so the second never halts.
Exactly one procedure halts, which decides `v = 1`.

So `S` is a finitely generated group with solvable word problem over which
failure occurs.

## Item 2

Let `1 != a in P` die in `P_w` for some `w in P * <t>` with `deg_t(w) in D`,
and let `P <= S`.  The identity

    a = prod_j u_j w^(e_j) u_j^(-1)

holds in `P * <t>`, which is a subgroup of `S * <t>` by the normal form theorem
for free products.  So it holds in `S * <t>`, and `a` dies in `S_w`.  The word
`w`, read over `S`, has the same `t`-exponent sum, and `a != 1` in `S` because
`P -> S` is injective.

## Item 3

Assume `boone-higman-conjecture`.  If failure occurs over a finitely generated
`P` with solvable word problem, embed `P` in a finitely presented simple group
and apply item 2.  The converse is item 1.

The remark about hyperlinearity and MF uses only the two established theorems
named on the claim: a finitely presented simple counterexample violates both.
