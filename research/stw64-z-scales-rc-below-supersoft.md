---
rg: 2
id: stw64-z-scales-rc-below-supersoft
kind: claim
title: Every unital Jiang-Su scale meets the supersoft scale at offset exactly the radius of comparison
distinct_from:
  stw64-z-maps-avoid-supersoft-classes: that shows only f(t) differs from s_t when rc(A)>0; this computes every order and compact-containment relation between f-values and the s_c, with the exact offset rc(A), and shows that none of them depends on f.
  stw64-supersoft-gap-is-comparison-radius: that concerns compact containment among the s_c alone and makes no assertion at the boundary; this concerns comparisons between Jiang-Su image classes and the s_c, and decides the boundary case for <=.
artifacts:
  - research/artifacts/stw64-z-scales-rc-offset-2026-09-16.md
---

Let A satisfy the hypotheses of stw64-supersoft-calculus. Put u=[1_A]
and s_c=alpha(c*u-hat) for finite c>0. Use Robert's computation
Cu(Z)=N disjointUnion (0,infinity], and write t' for the soft class at
level t. Let f be any unit-preserving Cu-morphism Cu(Z)->Cu(A), and let
a,b,d>0 be finite. Then:

- (a) f(b') <= s_a iff b <= a.
- (b) s_a <= f(b') iff b-a >= rc(A). This never holds if rc(A)=infinity.
- (c) s_a << f(b') iff b-a > rc(A).
- (d) f(b') << s_a iff b < a.
- (e) Let f_1,...,f_k be unit-preserving Cu-morphisms, possibly distinct,
  and let a_1,...,a_k>0 be finite. Then s_d <= sum_i f_i(a_i') iff
  sum_i a_i - d >= rc(A).

So for R<rc(A) no finite t satisfies s_t<=f((t+R)'). The least shift that
carries the supersoft scale below a unital Jiang-Su scale is rc(A), for
every such scale and at every level.

**Invisibility.** Write nu for n[1_A]. Evaluate the formal labels 0, n, t',
[s_c] and infinity as 0, nu, f(t'), s_c and sup_n nu. The addition table
on these labels does not depend on f. The same holds for every <= relation
and every << relation between two labels. In particular:

- f(t')+s_c = s_{t+c} and nu+s_c = s_{n+c};
- nu <= s_c iff n<c;
- s_c <= nu iff n-c >= rc(A);
- s_c << infinity iff rc(A)<infinity.

A second unit-preserving morphism therefore cannot be detected by comparing
values of one morphism with integers or with the canonical supersoft
classes. It also cannot be detected by comparing a canonical supersoft class
with a finite sum of values of possibly different morphisms, as in (e).
These results say nothing about mixed comparisons of values of two
different morphisms, such as h(a')<=f(b') or nu+h(a')<=f(b'). Those are
exactly the undetermined comparisons.

This computes no Cuntz semigroup of a Villadsen or Toms algebra. It neither
constructs nor excludes a second unit-preserving morphism, and it does not
resolve STW LXIV or LXIII.
