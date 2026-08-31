---
rg: 2
id: bcv-canonical-readable-growth-diagonal-proof
kind: route
title: Deduce canonical readable growth from the arbitrary-strategy BCV diagonal theorem
target: bcv-canonical-readable-growth-no-computable-bound
requires:
  - bcv-no-computable-perfect-halt-readable-bound
  - bcv-arbitrary-perfect-halt-readable-diagonal-proof
---

The strategy `S_M^can` is an attained-perfect finite-dimensional ZPC
strategy for `G_M`. Apply
`bcv-no-computable-perfect-halt-readable-bound` to this particular
strategy. Its universal estimate is exactly

```text
dim D_infinity(S_M^can)
  >= product_(0<=j<h_M) 2^(2^(lambda T_j))
  >= 2^h_M,                                              (CRG2)
```

so the canonical lower bound follows immediately.

If a total computable `B` satisfied `(CRG3)`, compute

```text
r=floor(log_2(max(1,B(M))))+1
```

and simulate `M` for `T_r` steps. If it has not halted but later halts
at `N`, then `N>T_r`, hence `h_M>r`, and `(CRG2)` contradicts
`dim D_infinity(S_M^can)<=B(M)`. Thus such a `B` would decide HALT.

The full work is in
`bcv-arbitrary-perfect-halt-readable-diagonal-proof`: it uses Lemma 2.59
clause 2 for exact game equality at each pre-halting level, clause 1 to
carry the detyped bipartite support and zero-answer anchor through every
recursive source level, and the exact inverse of all Compression wrappers
to obtain the tensor inclusion

```text
ell^infinity(F_2^(2^(lambda T_j)))
  tensor D_infinity(S_(j+1))
  subseteq D_infinity(S_j).
```

Accordingly, the earlier restriction of this route to BCV's honest forward
strategy is obsolete. The stronger result refutes the proposed uniform
HALT-side bound; it does not create the finite-readable NONHALT witness
needed by the groupification route and does not solve the root
nonhyperlinear-group problem.
