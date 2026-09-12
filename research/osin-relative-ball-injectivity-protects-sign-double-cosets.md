---
rg: 2
id: osin-relative-ball-injectivity-protects-sign-double-cosets
kind: claim
title: Relative ball injectivity protects prescribed sign double cosets
distinct_from:
  relative-c-sixth-protects-sign-double-cosets: that gives the elementary free-product C-prime one-sixth criterion with minimum relator length eight; this uses Osin's more general relatively hyperbolic filling theorem and isolates the protected-radius hypothesis.
  colored-cayley-pauli-incidence-separation: that must construct the base address group and all occurrence cosets; this preserves sign separation once the two equality groups are peripheral and the short Pauli templates have already been absorbed in the base.
  gsc-does-not-separate-sign-double-cosets: that shows ordinary letter-metric graphical small cancellation is insufficient; this counts equality-subgroup elements as peripheral letters in the relative metric.
artifacts:
  - research/artifacts/relative-small-cancellation-occurrence-support-2026-08-21.md
---

Let `G` be hyperbolic relative to subgroups `H_X,H_Z` with finite relative
generating set `X`.  Let `P_0,P_1` be finite subsets of `X` and assume in the
base group

```text
H_X P_0 H_Z intersect H_X P_1 H_Z = empty.            (ORB1)
```

Fix Osin's constants for relative radius `N=4` in Lemma 5.1 of
arXiv:math/0411039.  If a finite symmetrized relator family satisfies the
corresponding `C(epsilon,mu,lambda,c,rho)` condition, and

```text
gamma:G -> G_1=G/<<R>>,
```

then

```text
gamma(H_X) gamma(P_0) gamma(H_Z)
 intersect
gamma(H_X) gamma(P_1) gamma(H_Z) = empty.              (ORB2)
```

Indeed a collision produces a nontrivial base element

```text
h_X p_0 h_Z p_1^(-1)                                  (ORB3)
```

of relative length at most four which `gamma` kills.  Osin's lemma says that
`gamma` is injective on the entire relative ball of radius four.

If the sign representatives have relative length at most `L` instead of
being relative generators, radius `2L+2` suffices.  The same observation
protects any finite list of named left or right cosets by choosing the radius
larger than the finitely many corresponding boundary lengths.

The peripheral hypothesis is load-bearing.  Mere finite generation of
`H_X,H_Z` does not make arbitrary subgroup words length one, and no theorem
checked in this audit preserves all cosets of arbitrary finitely generated
subgroups under an unrelated small-cancellation quotient.

