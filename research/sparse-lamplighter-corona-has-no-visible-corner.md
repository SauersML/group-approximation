---
rg: 2
id: sparse-lamplighter-corona-has-no-visible-corner
kind: claim
title: A faithful weak-MF embedding can defeat every invariant corner
distinct_from:
  weak-mf-embedding-not-reusable: That theorem treats changing the metric, identity padding, and amplification of a fixed embedding; this theorem allows every invariant projection in the relative commutant and proves that all of their intrinsic corner traces still miss one nontrivial element.
  mf-invariant-corner-visibility: That open claim may choose a convenient faithful weak-MF realization separately for the marked element; this theorem fixes one hostile realization of a group which also has other, trace-visible realizations.
  bounded-rank-corners-excluded: That theorem excludes bounded-rank detecting corners using a Kazhdan hypothesis; this theorem needs no property (T) and excludes detecting corners of every rank in one explicit realization by a shift-orbit trace estimate.
artifacts:
  - research/artifacts/weak-mf-hs-profile-audit-2026-08-30.md
---

Let

```text
L = (directSum_(j in Z) C_2) semidirect Z
```

be the binary lamplighter group, let `a` be the lamp at `0`, and let `s` be
the shift.  There is an explicit faithful homomorphism

```text
u : L -> U(Q),       Q = prod_(n>=1) M_n / directSum_(n>=1) M_n,
```

such that `u(a) != 1`, but for every nonzero projection

```text
P in u(L)' cap Q
```

and every projection lift `q_n` of `P`, with `r_n=rank(q_n)>0` on the
infinite index set `I_q={n:q_n!=0}`, the intrinsic corner traces satisfy

```text
lim_(n->infinity, n in I_q) Re tr_(r_n)(q_n u_n(a) q_n) = 1.  (LC1)
```

At quotient level `P u(a) P` is a unitary in the corner.  Its coordinate
compressions are asymptotically unitary, and any polar-unitary corrections
`w_n` satisfy `||w_n-q_n u_n(a)q_n||_op->0`; their normalized traces have
the same limit in `(LC1)`.

Equivalently, no invariant corner of this faithful weak-MF embedding sees
the nontrivial lamp `a` with a positive normalized trace gap.  This remains
true for corners of arbitrary, possibly vanishing ambient density and for
bounded or unbounded positive rank on `I_q`.

The quantifier over the realization is essential.  The group `L` is
residually finite, so it has other exact finite-quotient models in which the
same element `a` has regular trace zero.  Thus this theorem does not refute
`mf-invariant-corner-visibility`; it proves that that claim, if true, must
select a new realization and cannot be obtained by taking a corner in an
arbitrary given weak-MF embedding.
