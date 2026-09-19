---
rg: 2
id: involution-mark-difference-codes-have-uniform-clique-bound
kind: claim
title: Bounded-area conjugacy-difference codes for an involution mark have uniformly bounded cliques in every finitely presented group
distinct_from:
  nested-prefix-clique-forces-centralizer-area-divergence: that refutes one explicit infinite Leavitt clique, using the edge word c_1 itself as the FMC anchor, so its constant grows with |c_1|; this conjugates every triangle back to the fixed mark z, so one constant bounds every clique of every code in every finitely presented group.
  leavitt-chromatic-tables-have-area-divergence: that freezes one column of two explicit Leavitt tables; this is presentation- and group-independent and rules out arbitrarily large finite cliques as well as infinite ones.
  finite-mark-centralizer-commutator-area-is-proper: that is the properness input; this is its graph-theoretic consequence for conjugacy-difference codes.
  literal-one-cell-carmichael-cliques-are-uniformly-finite: that bounds one-cell Carmichael templates in the free group; this allows arbitrary diagrams and concerns involution conjugacy differences, not order-three Carmichael vertices.
artifacts:
  - research/involution-mark-clique-bound-proof.md
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be finitely presented and let `z` be a
fixed word with `z^2=1!=z` in `Gamma`.  Put `K=<z>` and `s=Area_R(z^2)`.
For every `A` there is

```text
omega(A) <= 2 |Ball_(K\Gamma)(rho_A)|,
rho_A = (10A + 5s + B_z)/A_z,                            (ICB1)
```

where `A_z,B_z` are the `(FMC1)` constants for `beta=z`, with the following
property.  Suppose `Lambda` carries vertex words `b_v` and edge conjugators
`a_(v,w)` with

```text
Area_R(b_v^(-1)b_w a_(v,w) z^(-1) a_(v,w)^(-1)) <= A      (CDC2)
```

on every oriented edge.  Then for every edge `uv`, the common neighbours of
`u` and `v` take at most `omega(A)-2` distinct values `b_w in Gamma`.  In
particular every clique of `Lambda` has at most `omega(A)` vertices.

The bound depends only on the presentation, the word `z` and `A`.  It does
not depend on `Lambda`, on the edge, or on the lengths of `b_v` or `a_(v,w)`.
So a family of finite graphs with growing clique number, such as `K_M` for
`M->infinity` or disjoint unions of them, cannot carry a uniformly
bounded-area involution-mark code in any finitely presented group.

Obstruction invariant: the twisted Schreier-chain norm of `(FMC1)`,
anchored at the fixed mark `z`.  The code dies at the step where a triangle
`(u,v,w)` gives two commuting conjugates of `z`, and conjugating by `a_(u,v)`
turns that commutation into a centralizer element of `z` of bounded
commutator area.

Surviving designs must be locally sparse.  In each vertex link, value-wise
degrees are bounded by `omega(A)-2`, as in shift graphs, Mycielski graphs,
or Kneser graphs with bounded clique number.  Combined with
`chromatic-mark-codes-are-metric-agnostic`, even these survivors exist only
in a nonhyperlinear group.

DERIVATION
involution-mark-clique-bound-proof
