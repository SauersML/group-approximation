---
rg: 2
id: relative-pauli-child-split-gives-one-exit-copy
kind: claim
title: The named relative Pauli pair splits every forbidden packet into one active and one exit copy
distinct_from:
  predicate-rank-gate-doubles-restriction-multiplicity: that counts two baseline simples abstractly by dimension; this names two equal-trace spectral projections and a packet word which swaps them.
  every-forbidden-atom-has-fixed-schur-pauli-words: that names the two relative generators and proves they anticommute; this extracts their equal-trace spectral halves as the child balance needed by the branching-with-exits ledger.
  branching-plus-first-hit-exits-forces-hs-floor: that assumes at most one exit copy per source; this proves that hypothesis on every exact forbidden Schur block.
---

Fix a forbidden selector atom `a` of a Schur--Clifford packet and let
`P_a,Q_a` be its named corrected relative involutions.  On a full-packet
simple with external multiplicity `m`,

```text
H_a = S_a tensor C^2 tensor C^m,
P_a Q_a = -Q_a P_a.                                    (PCS1)
```

Put

```text
E_+=(I+Q_a)/2,       E_-=(I-Q_a)/2.                    (PCS2)
```

Both projections commute with the baseline packet `A_f`, and

```text
P_a E_+ P_a^*=E_-,
rank E_+=rank E_-=dim(S_a)m.                           (PCS3)
```

Consequently each range is exactly one copy of the baseline `A_f` packet per
full-packet multiplicity coordinate.  Designating one range active and the
other as the first-hit exit gives the exact balance

```text
two child copies = one active copy + one exit copy,
exit mass = source fixed-scale multiplicity mass.       (PCS4)
```

In particular the exit cannot consume more than one child copy.  This is the
zero-defect content of `(BFE2)` with `zeta_n=0`; it is not a dimension-counting
assumption or a choice of an unobservable multiplicity basis.  Both child
projections are spectral projections of fixed packet words.

For an approximate normalized-HS packet, first apply
`finite-schur-clifford-packet-flexible-hs-exactification`.  Equations
`(PCS1)--(PCS4)` then hold exactly in the enlarged representation, while the
compressed input projections and their traces change by the packet's
dimension-independent exactification loss.  Thus the approximate version of
`(BFE2)` costs only a fixed local packet error; conjugating the named words to
level `n` introduces only the polynomial word-transport loss already allowed
in `(BFE7)`.
