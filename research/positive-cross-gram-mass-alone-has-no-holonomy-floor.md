---
rg: 2
id: positive-cross-gram-mass-alone-has-no-holonomy-floor
kind: claim
title: Positive cross-Gram mass alone has no holonomy or return floor
distinct_from:
  one-cross-gram-moment-extracts-the-common-polar-gauge: that obtains a common unitary gauge when the cross-Gram moment is near the whole source mass; this shows why a merely positive moment cannot give that conclusion.
  pauli-overlap-yields-positive-spectral-corner: that extracts a positive spectral corner from a quantitative overlap; this gives exact models on which the extracted corner still carries no contradiction.
---

Fix `0<gamma<1`.  There are finite-dimensional exact packet intertwiners
with common source, common target, and

```text
||T_2^*T_1||_2^2=gamma tau(p),                            (PON1)
```

while every packet and self-Gram defect is zero and the relative polar gauge
is arbitrary.

Indeed, let `alpha:G->U(H)` be any finite packet representation, put

```text
K=H direct_sum H,
beta=alpha direct_sum alpha,
T_1 xi=(xi,0),
T_2 xi=(sqrt(gamma) V xi,sqrt(1-gamma) xi),               (PON2)
```

where `V in alpha(G)'` is any unitary.  Then both `T_i` are exact isometric
intertwiners and

```text
T_2^*T_1=sqrt(gamma) V^*.                                 (PON3)
```

Thus the spectral cut of `(T_2^*T_1)^*(T_2^*T_1)` at any threshold below
`gamma` is the entire source, yet the two ranges retain an orthogonal
component of squared mass `1-gamma`.  In particular

```text
inf_(W unitary) ||T_1-T_2W||_2^2
 =2(1-sqrt(gamma))tau(p),                                 (PON4)
```

which does not tend to zero at fixed `gamma<1`.  The unitary `V` can range
over the whole packet commutant without altering any packet relation or the
overlap scalar.

The construction is stable under arbitrary amplification and under direct
sum with any exact marked representation.  It follows that a positive
cross-Gram lower bound, by itself, cannot imply a marked-word Hilbert--Schmidt
floor, cannot produce the near-full alignment `(CGP5)--(CGP6)`, and cannot
select a nontrivial holonomy.  Some mixed relation must inspect the overlap.

The minimal useful repair is not necessarily near-full overlap.  It is enough
to impose a phase or representation mismatch on the two ranges: then the
cross-Gram operator is an approximate intertwiner between disjoint types and
its **positive** Hilbert--Schmidt mass directly pays the mismatch energy.  The
three-book HNN construction in
`three-book-hnn-antiphase-charges-every-cross-gram` implements that repair for
the equal-rank Fanizza return sources.
