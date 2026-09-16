---
rg: 2
id: stw64-unital-z-maps-rc-shift-close
kind: claim
title: Unital Jiang-Su Cuntz maps into one algebra lie within shift distance rc(A) of each other
distinct_from:
  stw63-strict-comparison-sr1-uniqueness: that derives approximate unitary equivalence of embeddings from strict comparison and stable rank one; this is a Cu-level statement about arbitrary unit-preserving Cu-morphisms into any unital A, bounding their mutual shift distance by rc(A) and making no return to embeddings.
  stw64-z-maps-avoid-supersoft-classes: that compares one morphism with the canonical supersoft family under stable rank one; this compares two morphisms with each other, with no stable rank one hypothesis.
artifacts:
  - research/artifacts/stw64-z-scales-rc-offset-2026-09-16.md
---

Let A be any unital C*-algebra, with u=[1_A]. Let rc(A) be the radius of
comparison in the form of APRT 8.6: the infimum of r in (0,infinity] such
that lambda(x)+r<=lambda(y) for all lambda in F_u(Cu(A)) implies x<=y.
Write Cu(Z)=N disjointUnion (0,infinity], and write t' for the soft class
at level t. Let f,h:Cu(Z)->Cu(A) be unit-preserving Cu-morphisms.

1. If 0<a<=b<infinity and b-a>=rc(A), then h(a')<=f(b').
2. If rc(A)=0, then f=h.
3. Define delta(f,h) as the infimum of those R>=0 such that, for every
   finite a>0, both h(a')<=f((a+R)') and f(a')<=h((a+R)'). The infimum
   of the empty set is infinity. When delta(f,h) is finite it is
   attained. It is an extended metric on unit-preserving Cu-morphisms,
   so delta(f,h)=0 iff f=h. Moreover delta(f,h)<=rc(A).
4. If f(a')=h(a') for all a in (0,epsilon), for some epsilon>0, then f=h.
   If Cu(A) has weak cancellation, then for each finite a>0 and each integer
   n>=0, f(a')=h(a') iff f((a+n)')=h((a+n)'). So a disagreement level
   stays a disagreement level under every integer translation.

No simplicity, stable rank one, nuclearity or quasitrace-uniqueness
hypothesis is used. Novelty is not asserted. Shift-type distances between
Cu-morphisms are used in the classification of homomorphisms out of
C_0(0,1]. Whether this Cu(Z) version appears there was not checked.

This does not decide whether f and h can differ, and it does not compute
Cu(A) for any Villadsen or Toms algebra.
