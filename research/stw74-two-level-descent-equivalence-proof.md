---
rg: 2
id: stw74-two-level-descent-equivalence-proof
kind: route
title: Corner isomorphisms from orthogonal isometries reduce any matrix threshold to level two
target: stw74-lxxiv-hinge-is-two-level-descent
requires:
  - stw74-simple-infinite-projections-are-properly-infinite
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Full proof: Section 2 of the artifact, using Lemmas 1--3 of Section 1
(item 4 of the claim is the artifact's item 3').

* **Lemma 1 (fullness normal form).**  In a unital simple algebra, for
  `0!=a>=0` there are `y_1,...,y_k` with `sum y_i* a^2 y_i=1`, so the column
  `v=(a y_i)_i` has `v*v=1` and `vv*` is a nonzero projection in
  `M_k(Her(a))`.  Hence a least projection level `m` exists.
* **Lemma 3 (corner isomorphism).**  For `t_i*t_j=delta_ij 1`,
  `Phi([c_ij])=sum t_i c_ij t_j*` is a \*-isomorphism `M_n(A) -> PAP` with
  `Phi(M_n(Her(a)))=Her(sum t_i a t_i*)`, and entrywise
  `M_2(M_n(Her(a))) ~= M_2(Her(sum t_i a t_i*))`.

(1)=>(2) is trivial; (2)=>(3) is Lemma 3 with `n=2`; (3)=>(4) needs one pair
of isometries with orthogonal ranges, which exists because the unit is
properly infinite (required claim) and properly infinite projections carry
such pairs (Lemma 2).  For (4)=>(1): if `Her(a)` is projectionless with least
level `m>=2`, put `n=m-1`, `w_i=t_2^(i-1)t_1` (orthonormal isometries) and
`b=sum_(i<=n) w_i a w_i*`.  Then `Her(b) ~= M_n(Her(a))` has no nonzero
projection, while `M_2(Her(b)) ~= M_(2n)(Her(a)) superset M_m(Her(a))` has
one because `2n>=m`; applying (4) to `b` gives a contradiction.  The same
computation proves the "moreover" clause.
