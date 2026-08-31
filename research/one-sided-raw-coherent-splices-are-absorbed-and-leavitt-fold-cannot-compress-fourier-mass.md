---
rg: 2
id: one-sided-raw-coherent-splices-are-absorbed-and-leavitt-fold-cannot-compress-fourier-mass
kind: claim
title: One-sided raw coherent splices are absorbed, while the Leavitt two-to-one fold cannot compress Fourier trace
artifacts:
  - research/raw-coherent-splice-and-leavitt-fold-trace-proof.md
distinct_from:
  g2-one-raw-letter-sign-atlas-is-residually-finite: that proves residual finiteness of the two one-orientation groups; this upgrades it to arbitrary finite linear-combination moment packets and tests the coherent complementary-edge splice.
  three-carrier-hidden-line-join-crosses-target-but-has-no-range: that constructs the bounded-below two-sided source; this gives a dimension-free leakage floor and proves that every target-contained correction deletes the Hall excess.
  qutrit-full-leavitt-prefix-conjugator-realizes-phase-star: that constructs a rectangular Leavitt conjugator and identifies hidden output characters; this proves the general trace reason why a rectangular coordinate equivalence cannot become a two-to-one Fourier transport.
---

Let Gamma be residually finite and let A_1,...,A_m be finite linear
combinations of its group elements.  For every degree N there is a finite
quotient regular representation which matches exactly every canonical
trace moment of degree at most N in the A_j.  Thus residual finiteness
absorbs coherent sums, not merely individual group words.

In particular this applies to either established one-sided Leavitt
envelope
```text
Lambda_T<=GL_28(F_2<q,T>),
Lambda_S<=GL_28(F_2<S,q,qT>).
```
Adding arbitrary finite-head coefficients on either side of a raw T
transporter, or on either side of a raw S transporter, and then taking
any finite complex linear combination remains exactly
finite-moment-approximable by finite quotient regular representations.
One raw orientation plus a complementary D16, S4, or qutrit edge whose
outer coefficients lie in that finite head cannot create a
normalized-Hilbert--Schmidt obstruction.

The two-sided three-line selector is the sharp next boundary.  Write
```text
X=X_0+(1/4)X_1+(1/16)X_2,
P=supp(R G_(sigma,+) R).
```
There is a constant gamma>0 determined by the fixed finite head such that
```text
(XR)^*(XR)>=(gamma/256)P.                                (RCS1)
```
Its source traces are 5/72 and 1/16, while every proposed target
Q_b=Ee_b has trace 1/18.  Therefore
```text
||(1-Q_b)g_2XR||_2^2 >=gamma/18432       if sigma=+,
||(1-Q_b)g_2XR||_2^2 >=gamma/36864       if sigma=-.      (RCS2)
```
If a coherent finite-head correction cancels this outside-target
amplitude, it must pay the same energy.  If the corrected operator has
range in Q_b, it cannot remain bounded below on all of P: its kernel in P
has trace at least 1/72 or 1/144.  This is finite-von-Neumann rank
balance, so interference cannot evade it.

The tempting literal Leavitt matrix
```text
F=[[0,0,t_0],
   [0,0,t_1],
   [s_0,s_1,0]]
```
does satisfy
```text
F^2=1,
F diag(1,1,0)=diag(0,0,1)F.                             (RCS3)
```
But (RCS3) is a rectangular ring-module equivalence between coordinate
idempotents, not a unitary group relation between intrinsic Fourier
projections.  If a unitary group element f satisfied fP=Qf for
projections P,Q, every trace would have tau(P)=tau(Q); even range
containment QfP=fP forces tau(P)<=tau(Q).  Hence f cannot send
```text
P=e_0+e_1,       tau(P)=2/9
```
into
```text
Q=e_b,           tau(Q)=1/9.
```
Stabilizing F and factoring it into elementary Leavitt generators does
not occurrence-type the singular coordinate idempotents.  Any
finite-subgroup encoding necessarily introduces hidden character sectors
or deletes half the source.

Therefore the mixed coherent splice has an exact trichotomy:

- one raw orientation: residually finite absorber;
- both orientations without target authentication: bounded-below source
  with quantitative leakage;
- target-contained correction: loss of at least the full Hall excess.

The non-IBN Leavitt fold does not furnish a fourth case.
