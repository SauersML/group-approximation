---
rg: 2
id: leavitt-d4-latin-triangle-reduction
kind: claim
title: The degree-four shared-carrier triangle reduces to one Latin boundary
artifacts:
  - research/leavitt-d4-latin-triangle-reduction-proof.md
  - research/artifacts/search-degree4-latin-triangle-boundary.py
distinct_from:
  leavitt-d4-direct-flux-fence: that forbids making two residuals coefficient identities; this retains carrier variables in all three residuals and eliminates them only around a triangle.
---

In the degree-four length-ten `(1,3,3,3)` cyclic cover, a shared-carrier
triangle can be realized exactly by the ten cyclic coefficient slots.  The
three post-pivot residual relators eliminate their three carrier variables
and force one coefficient boundary

```text
F=H^-1 B0 H^-1 B1 H^-1 B2
```

to be the identity.  The complete cyclic slot equations reduce to four free
coefficient units `a,b,c,d`; `H` and the three `Bi` are the four cyclic Latin
rows displayed in the proof.

Thus a choice with `F=h_j` for nonidentity `h` in one coefficient copy would
be an explicit Kervaire--Laudenbach counterexample.  Unlike the direct carrier
design, this family passes the first copy-retraction rank filter; the sharper
metacyclic and full-word obstruction is recorded separately.
