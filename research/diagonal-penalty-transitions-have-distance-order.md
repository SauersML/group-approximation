---
rg: 2
id: diagonal-penalty-transitions-have-distance-order
kind: claim
title: Diagonal code penalties delay virtual transitions to Hamming-distance order with a norm-convergent tail bound
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
distinct_from:
  distance-code-local-tests-are-label-diagonal: That concerns first-order compression on the exact code; this includes virtual excursions through the complement via a diagonal resolvent.
---

Let P be a computational-basis code projector (with arbitrary auxiliary
identity), Q=I-P, and H_pen be diagonal in the data label, zero on P,
and >=Delta Q on Q. Let V be a sum of Hermitian terms each changing
at most k>=1 data bits. Put v=||V|| for the entire perturbation,
a=Delta-|z| for real z, and assume a>v>0.
The exact Schur effective operator is
F(z)=PVP-PVQ[Q(H_pen+V-zI)Q]^(-1)QVP.

For codewords at distance d, r=ceil(d/k)>=2, every expansion term
with fewer than r perturbation factors has zero connecting block.
The off-diagonal block of F(z) has norm at most
v(v/a)^(r-1)/(1-v/a).
The statement permits quantum auxiliary blocks but requires a
data-label-diagonal penalty and a bound on the total norm, not just
individual terms. It does not exclude nonperturbative gadgets.

