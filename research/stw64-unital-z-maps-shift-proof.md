---
rg: 2
id: stw64-unital-z-maps-shift-proof
kind: route
title: Equal Jiang-Su ranks plus any admissible comparison constant bound the shift distance
target: stw64-unital-z-maps-rc-shift-close
requires: []
artifacts:
  - research/artifacts/stw64-z-scales-rc-offset-2026-09-16.md
---

This is a direct proof from two literature inputs:

- Robert's computation of Cu(Z) (Section 6.3, as already imported in
  stw63-strict-comparison-cu-collapse-proof);
- the Cu-form of Toms's radius of comparison in APRT, arXiv:1809.03984v3,
  paragraph 8.6.

Full details are in Section 1 of the artifact.

**Cu(Z) relations.**

- Cu(Z) is N disjointUnion (0,infinity].
- n+t'=(n+t)' and t'+r'=(t+r)'.
- n<=t' iff n<t, and t'<=n iff t<=n.
- t'<=r' iff t<=r.
- t'=sup of r' along any increasing sequence r increasing to t.
- infinity=sup_n n.

A unit-preserving Cu-morphism preserves 0, sums, order, increasing suprema
and compact containment. So it sends n to n*u and infinity to sup_n n*u,
for every such morphism.

**(R) Ranks.** Let lambda be any functional on Cu(A) and t>0 finite. Put
m=ceil(nt) for large n. Then (m-1)<=(nt)'<=m in Cu(Z). Applying f gives
(m-1)u<=n*f(t')<=m*u. Applying lambda and dividing by n gives
lambda(f(t'))=t*lambda(u). This also covers lambda(u) equal to 0 or
infinity.

**(U) Upward closure.** If r is admissible for rc(A) and r''>=r, then
lambda(x)+r''<=lambda(y) implies lambda(x)+r<=lambda(y). So r'' is
admissible, and every finite R>rc(A) is admissible.

**Item 1.** Suppose b-a>rc(A). Then R=b-a is admissible. By (R), every
lambda in F_u satisfies lambda(h(a'))+R=a+R=b=lambda(f(b')). Hence
h(a')<=f(b').

Suppose instead b-a=rc(A). Take a_k increasing to a. Then
h(a_k')<=f(b') for every k, and h(a')=sup_k h(a_k')<=f(b').

**Item 2.** Item 1 with a=b gives h(a')<=f(a'). By symmetry f(a')<=h(a').
The compact classes and infinity have the same images under both maps.

**Item 3.**

- *Upward closure.* Increasing R preserves both inequalities, because
  f((a+R)') increases in R.
- *Attainment.* Let R_k decrease to R_0 and fix a''<a. Choose k with
  R_k<=R_0+(a-a''). Then h(a'')<=f((a''+R_k)')<=f((a+R_0)'). Taking the
  supremum over a'' increasing to a gives h(a')<=f((a+R_0)'). The other
  inequality is symmetric.
- *Bound.* If rc(A)<infinity, item 1 with b=a+rc(A) shows that R=rc(A)
  works. Hence delta(f,h)<=rc(A).
- *Zero distance.* If R=0 works, then f and h agree on soft classes, hence
  everywhere as in item 2.
- *Symmetry and triangle inequality.* Symmetry is built into the
  definition. Suppose h(a')<=f((a+R_1)') and f(r')<=k((r+R_2)') for all
  a,r. Then h(a')<=k((a+R_1+R_2)'). The reverse inequality is obtained in
  the same way.

**Item 4.**

- *Germ at zero.* Every finite t>0 is j*(t/j) with t/j<epsilon. Both maps
  are additive, so f(t')=j*f((t/j)')=j*h((t/j)')=h(t').
- *Integer translates.* Weak cancellation implies cancellation of compact
  elements (APRT Section 2): x+z<=y+z with z<<z implies x<=y. Suppose
  f((a+n)')=h((a+n)'). Then f(a')+n*u=h(a')+n*u, and n*u is compact, so
  f(a')=h(a'). The converse is additivity. This holds for each n
  separately. The input used is APRT, arXiv:1809.03984v3, paragraph 2.5
  and the remark after its lemma on equivalent forms of weak cancellation
  (text checked 2026-09-16).
