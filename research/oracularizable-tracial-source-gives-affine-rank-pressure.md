---
rg: 2
id: oracularizable-tracial-source-gives-affine-rank-pressure
kind: claim
title: An oracularizable tracial gap source yields exact local packets with uniform affine game-loss pressure
distinct_from:
  taller-vidick-lcs-re-hardness: that is the published complexity theorem with imperfect LCS completeness; this retains every failed verifier check as an allowed Clifford sector and proves exactness only for the enlarged local packet algebra.
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that requires one shared LCS tuple satisfying every equation in the tracial model; here Alice's context observables and Bob's query observables remain distinct and their disagreement is itself rank-tagged.
  uniform-affine-lcs-rank-return: that must make the local pressure pay in one finite group presentation; this establishes the local exact model and positive finite-dimensional pressure before any return is attached.
artifacts:
  - research/artifacts/taller-vidick-lcs-rank-pressure-2026-08-20.md
---

Assume `oracularizable-tracial-nonru-game-exists`.  Then there is a fixed
finite Taller--Vidick LCS game `L` and a fixed finite local packet extension
`P(L)` with a central involution `J` such that:

1. `P(L)` has an exact tracial representation with `J=-1`;
2. every finite-dimensional strategy for `L` has positive average mass in the
   packet rank-jump sectors,

```text
q >= q_0>0;                                                  (TAP1)
```

3. each hot sector is detected by the same two-pair Clifford packet, with an
   affine commutator coefficient.

Apply the finite projection, repetition, and Taller--Vidick long-code
construction to the source in `(OTN1)`, obtaining a fixed LCS game with
finite-dimensional value at most `s<1`.  A verifier round has Alice's three
commuting answer bits `a_1,a_2,a_3`, Bob's bit `c`, a selected coordinate `i`,
and two affine failure bits

```text
r_par = a_1+a_2+a_3+b_omega,
r_con = a_i+c.                                               (TAP2)
```

The round loses exactly when at least one is one.  Attach one copy of the
packet `diag(1,r)` to each bit in `(TAP2)`.  The controlled Pauli lift exists
on every joint spectral atom, so no outcome is killed.  Oracularizable perfect
commuting completeness and the algebraic Taller--Vidick construction extend
to an exact tracial representation of all local packet relations with `J=-1`,
including mask-failure atoms.

Conversely, a finite-dimensional realization of the measurement contexts is a
finite-dimensional strategy for `L`.  If `q` is the expectation of
`r_par+r_con`, then pointwise

```text
r_par+r_con >= 1_(round loses).
```

The value bound gives

```text
q >= 1-s=:q_0.                                               (TAP3)
```

By `(PSD1)` these are genuine positive failure projections, and by `(TXR1)`
they are exactly the extra-rank carriers.  This does not identify Alice's
context copies with Bob's query copy: that overlap transport is intentionally
left to the global return theorem.

## Attempts

- Identifying Alice's and Bob's copies by scalar group relations would require
  perfect finite-dimensional consistency and collapses back to the unresolved
  perfect-completeness LCS route.
- Leaving the copies unrelated preserves the exact tracial packet lift but
  gives no common multiplicity wire; local rank pressure alone can be absorbed
  by direct sums.
- A Bass--Serre graph of the local packets has stationary representation-ring
  flow, so it cannot turn `(TAP3)` into normalized-HS energy without an
  additional return/holonomy cell.
