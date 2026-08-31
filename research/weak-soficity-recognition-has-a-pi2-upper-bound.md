---
rg: 2
id: weak-soficity-recognition-has-a-pi2-upper-bound
kind: claim
title: Weak soficity is Pi-zero-two for recursive presentations, so its recognition is either trivial or Pi-zero-two complete
distinct_from:
  sofic-recognition-has-a-pi2-upper-bound: that certifies with permutations and a Hamming defect; this certifies with an arbitrary finite group and a bounded-area non-membership, since weak soficity has no canonical metric, and the upper bound comes from Glebsky's algebraic characterization rather than from a model with defects.
  glebsky-weak-soficity-is-metric-free: that records Glebsky's Lemma 1.2 as a source finding; this uses clause (3) of that lemma to arithmetize weak soficity.
  approximation-property-recognition-dichotomy: that leaves the weakly sofic row at "Pi-zero-two hard"; this supplies the membership half, making the row a completeness dichotomy.
---

ESTABLISHED.  For a finitely generated recursive presentation `<X | R>` of
`K`, with `N` the normal closure of `R` in `F = F(X)`:

```text
K is weakly sofic   iff   for every finite list W of words and every
   finite template T = (r_1^{e_1}, ..., r_m^{e_m}) of signed relators:
      (some w in W is trivial in K)                      [Sigma^0_1]
   or (there is a finite group H and h : X -> H such that for every
       w in W and all c_1, ..., c_m in H,
       w(h) != prod_j c_j r_j(h)^{e_j} c_j^{-1}).         [decidable]   (WS1)
```

Hence `WEAKLY-SOFIC_rec` is `Pi^0_2`, and by
[[second-level-rice-theorem-for-local-approximation-properties]] the
dichotomy of [[approximation-property-recognition-dichotomy]] for weak
soficity reads: either every group is weakly sofic, or weak soficity is
`Pi^0_2`-complete on two-generator recursive presentations.  The same
holds for finite presentations as membership (`Pi^0_2`) and for the
`Sigma^0_1`-hard side.

The dichotomy has one fixed target. For the two-generator finitely presented
group `V` of
[[universal-local-approximation-fixed-two-generator-test-group]],

```text
V is weakly sofic
  <=> every group is weakly sofic
  <=> weak soficity is closed under arbitrary quotients.
```

Consequently the trivial side occurs exactly when `V` is weakly sofic, and
the `Pi^0_2`-complete side occurs exactly when `V` is not weakly sofic.
This is an exact reduction, not a claim that either value of `V` is known;
the quotient equivalence is
[[fixed-finite-relator-quotient-tests-local-permanence]].

The certificate is a finite group in which the listed nontrivial words
avoid every product of `m` conjugates of the listed relator instances: a
bounded-area non-membership statement, checkable by finite enumeration.
