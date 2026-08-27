---
rg: 2
id: uniform-power-return-self-hash
kind: claim
title: Finitely compile every conjugacy-to-power challenge with one operator-norm budget
root: true
distinct_from:
  self-hashing-expander-collision-presentation: that asks for recursive Pauli packets, cross-edge checks and an expander checksum; this asks only for one cursor and one uniformly certified family of power returns.
  coprime-power-pair-phase-hnn-is-residually-finite: those exact power-conjugacy cells still have finite models and therefore do not provide a uniform relator-area bound over all exponents.
  conjugacy-addressed-opnorm-challenges-are-lossless: literal conjugacy has zero loss, but the missing semantic comparison to `w^m` is exactly this node.
---

Construct a finite presentation `Gamma=<S|R>`, a nontrivial zero-abelianization
cursor `w`, words `a_m`, and one finite constant `C` such that for every
dimension, unitary tuple and `m>=2`,

```text
||a_m(U) w(U) a_m(U)^-1 - w(U)^m||_op <= C Def_R(U).
```

This is OPEN.  Abstract identities such as those in `Aff(Q)` do not suffice:
their derivation constants may grow with `m`, and amenable finite models show
that some growth must occur there.  A successful construction must make the
terminal return certificate a depth-independent self-hash, ideally a literal
conjugate of one of finitely many root checks.  The cursor must have zero free
abelianization; otherwise a uniformly bounded root certificate is obstructed
by the exponent vector `(1-m)[w]_ab`.

## Attempts

Exact affine and Baumslag--Solitar-style power conjugacies fail because their
finite models force the derivation constants to grow with the exponent.
Repeated squaring reduces execution depth but still leaves unbounded proof
area.  The active route replaces replay by a proof-carrying terminal port;
`proof-carrying-power-return-terminal-authentication` records the missing
finite syntax theorem.
