---
rg: 2
id: occurrence-conditioned-balanced-polar-discards-the-hall-excess
kind: claim
title: The occurrence-conditioned 1/18 polar discards the Hall excess, and the surviving GL Hecke face is head-trivial
artifacts:
  - research/balanced-target-polar-and-quasiregular-hecke-absorber-proof.md
distinct_from:
  one-sided-raw-coherent-splices-are-absorbed-and-leavitt-fold-cannot-compress-fourier-mass: that proves the raw-orientation RF firewall and the unequal-trace leakage bound; this analyzes the exact equal-trace polar obtained after target compression.
  binary-jacobson-naive-head-polar-is-balanced-return: that constructs one specific balanced raw return; this proves the universal finite-unitary dilation and applies it to the three-line qutrit target.
  binary-jacobson-balanced-center-fold-authenticates-two-rows: that authenticates two Q-labelled covariance rows; this explains why balanced support leaves a commutant gauge and cannot imply the missing T-labelled rows.
---

Let A have initial support P in a finite tracial matrix algebra and let Q
be a target projection with
```text
tau(P)=p>=q=tau(Q).
```
If T=QA has full range Q, then its polar V satisfies
```text
V^*V=P_0<=P,          VV^*=Q,          tau(P_0)=q.       (BHP1)
```
It necessarily discards initial trace p-q.  Conversely every such
balanced partial isometry is the polar of QUP for some finite-dimensional
unitary U; U sends P-P_0 into 1-Q.  Thus a target-contained balanced polar
and macroscopic leakage of the original occurrence coexist exactly.

Apply this to
```text
A=g_2 X(e_0+e_1),          Q=Ee_b,
```
where X is the bounded-below three-line S/T selector.  If QA fills Q,
its polar has source and range trace exactly 1/18, but it discards
```text
5/72-1/18=1/72
```
or
```text
1/16-1/18=1/144
```
of the established source.  If QA does not fill Q, the polar is smaller.
The prior leakage lower bound is paid by the discarded complement; it
does not survive as a defect of the balanced polar.

Full range is also insufficient for a uniform approximate polar:
nonzero singular values may tend to zero.  And the tautological source
rows V^*D_jV are unitarily equivalent to the target rows, so they have the
same polynomial-identity degree.  A degree-two-to-degree-four
contradiction still requires the independently named Jacobson source
tuple and all of its covariance rows.

The remaining finite-head Hecke face has an exact absorber.  For
```text
K=GL_28(F_2) < F=GL_(28N)(F_2),
pi=Ind_K^F(1),
```
let p be the projection onto K-fixed vectors orthogonal to the F-fixed
vectors.  Then p is nonzero, but every nontrivial K-character projection
and every negative K-involution cut annihilates it:
```text
e_chi p=0,                  (1-z)p/2=0.                  (BHP2)
```
Consequently both the qutrit source atoms and the negative head target
kill the K-fixed/F-orthogonal mode.  A raw transporter can only send it
through the other finite K-double-coset sectors.  In the left regular
model the Reynolds difference has trace
```text
1/|K|-1/|F|,
```
and in the quasiregular model normalized rank
```text
(|K backslash F/K|-1)/[F:K].
```
So the Hom_K/Hom_F survivor is finitely absorbed and is invisible to the
selected compiler corner.

Therefore the equal-1/18 occurrence is not a capacity breakthrough.  A
successful continuation must add a genuinely mixed S/T relation which
does two jobs simultaneously: give a uniform lower singular bound after
target compression and intertwine the independently occurrence-typed
degree-two source tuple with the literal degree-four target tuple.
Balanced support and finite-head Hecke data alone cannot do either.
