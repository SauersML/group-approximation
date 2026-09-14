---
rg: 2
id: kms-arbitrarily-hard-fp-rf-groups-citation
kind: route
title: Import Kharlampovich-Myasnikov-Sapir Theorem 4.21 and its quantitative hardness definition
target: kms-arbitrarily-hard-fp-rf-groups
requires: []
artifacts:
  - research/artifacts/boone-higman-complexity-wall-2026-09-11.md
---

[Kharlampovich--Myasnikov--Sapir, *Algorithmically complex residually finite
groups*](https://link.springer.com/article/10.1007/s13373-017-0103-z), Bull.
Math. Sci. **7** (2017), 309--352, Theorem 4.21: for every recursive
membership problem `X` there is a finitely presented residually finite group,
solvable of class three, whose word problem is at least as hard as `X`.

Their Definition 2.2(a) fixes the quantitative meaning of "at least as hard",
which is the form `(KMS1)` records: a time-`T` algorithm for the harder
problem supplies an algorithm for the other in time `C*T(C*n) + C*n + C`.

Decidability of the word problem is automatic: a finitely presented
residually finite group has solvable word problem, by enumerating proofs from
the presentation and finite quotients in parallel.

The closure statement `(KMS2)` is elementary. If `g` is non-decreasing and
`T(n) = C_1*g(C_1*n) + C_1*n + C_1`, then substituting into `(KMS1)` gives a
bound of the same shape with a larger constant, since
`C*T(C*n) + C*n + C <= C_2*g(C_2*n) + C_2*n + C_2` for
`C_2 = C*C_1 + C + C_1`. Hence `F(g)` is closed under the substitution, and a
problem outside `F(g)` forces the group's word problem outside `F(g)`.

This route records an import plus that one-line closure check. The same
theorem is already consumed inline by
`kms-complexity-excludes-rational-embeddings-proof`; it is stated as its own
claim here because `uniform-wp-bound-excludes-bh-targets-proof` applies it to
an arbitrary target class rather than to rational homeomorphism groups.
