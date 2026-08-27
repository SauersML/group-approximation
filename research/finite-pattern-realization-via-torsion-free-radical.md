---
rg: 2
id: finite-pattern-realization-via-torsion-free-radical
kind: route
title: Kill the torsion radical, then embed the recursive presentation
target: finite-torsion-free-pattern-realizable-finitely-presented
requires: [torsion-free-universal-quotient-recursively-presented, torsion-free-higman-embedding]
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

Let `P` be finitely presented, `W` a finite subset of `P \ {1}`, and
`f : P -> G` a homomorphism into a torsion-free group with `f(w) != 1` for
all `w` in `W`.

Form `Ptf = P/Tor_oo(P)`.  By the first hypothesis it is torsion-free,
recursively presented, and universal: since `G` is torsion-free, `f` factors
as `P -> Ptf -> G`.  Consequently no `w` in `W` dies in `Ptf` -- if it did,
`f(w)` would be `1`.

By the second hypothesis the recursively presented torsion-free group `Ptf`
embeds in a finitely presented torsion-free group `H`.  Let `j` be the
composite `P -> Ptf -> H`.  Every `w` in `W` survives to `Ptf` and the second
map is injective, so `j(w) != 1`.

## The matrix corollary

Given torsion-free `G`, `A` in `GL_n(ZG)` and `B = A^-1`: take formal
generators for the finitely many group elements occurring in `A` and `B`,
impose the finitely many relations recording which products of them coincide
in `G`, and let `W` be the finitely many quotients of occurring products that
are nontrivial in `G`.  The resulting `P` is finitely presented and maps to
`G` with `W` surviving, so the theorem gives finitely presented torsion-free
`H` and `j : P -> H` keeping `W` nontrivial.  The relations force products
equal in `G` to be equal in `H`, and `W` forces products distinct in `G` to
stay distinct, so the partition of occurring products into equality classes
is identical on both sides and every coefficient of `AtildeBtilde` collects
exactly as in `AB`.  Hence `AtildeBtilde = BtildeAtilde = I_n`.

Both hypotheses come from the same paper (Chiodo, arXiv:1107.1489v4:
Proposition 3.8 and Theorem 2.2 respectively), and both are read from source
in the audit artifact.  Until 2026-08-17 the second was carried in this graph
as unverified, which is why this statement was not available before.
