---
rg: 2
id: fpbs-global-pivotal-tail-at-uniqueness-proof
kind: route
title: Close endpoint bridges and charge their finite sides to finite-cluster tails
target: fpbs-global-pivotal-tail-at-uniqueness
requires:
  - fpbs-uniqueness-pivotals-are-dangling-bridges
  - fpbs-supercritical-finite-susceptibility
artifacts:
  - research/artifacts/fpbs/docs/global-pivotal-tails-and-volume-defect.md
---

Sections 2--3 give the complete surgery argument. Closing one bridge
which cuts its root off from infinity changes its cylinder weight by
(1-p)/p. Sum over edges to identify the expected weighted count of
finite bridge sides with p/(1-p) times the expected boundary contact
count of a finite root cluster. The latter count is at most d|C_o|.
This proves E N_o<=dp chi_f/(1-p) using the supplied susceptibility input.
The supplied dangling-bridge lemma bounds global pivotals on infinite
connections by N_v+N_w; finite connections contribute at most |C_v|-1.

For the exponential statement, the route also imports the stronger
published conclusion of Hermon--Hutchcroft, Theorem 1.1,
https://arxiv.org/html/1904.10448#S1 : for each fixed p>p_c there exists
a>0 with E_p[|C_o| exp(a|C_o|); |C_o|<infinity]<infinity. This exact
extra input is stated and checked in artifact Section 1, rather than
being inferred from the weaker susceptibility claim. The finite sides
of bridges cutting o off from infinity are strictly nested along any
infinite ray from o, so N_o>=m forces a side of size at least m.
The weighted surgery identity then gives an exponential tail for N_o.
Apply a union bound and the finite-cluster tail to Z(v,w). Uniqueness
and FKG give P_p(v connected to w)>=theta(p)^2, providing the claimed
conditional bound. All constants retain their dependence on p.
