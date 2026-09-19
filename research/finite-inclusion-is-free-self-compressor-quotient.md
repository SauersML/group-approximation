---
rg: 2
id: finite-inclusion-is-free-self-compressor-quotient
kind: claim
title: Every finite subgroup inclusion is the quotient shadow of a proper free-group self-compressor
distinct_from:
  termwise-finite-reynolds-holonomy-has-zero-rank-gap: That rules out conjugating the two finite groups themselves; this realizes their inclusion only as the two quotient shadows of an infinite one-sided self-copy.
  compressor-covariant-packet-reynolds-return: That must localize a quotient shadow on the predicate carrier with quantitative matrix control; this supplies the previously missing abstract self-compressor with the prescribed parent and child quotient images.
  single-free-endomorphism-has-marked-finite-quotients: That periodizes a given free-group endomorphism in finite quotients; this constructs an injective endomorphism whose image under a prescribed finite quotient is a prescribed subgroup.
---

Let `A<=B` be an inclusion of finite groups.  There are a finite-rank free
group `F`, an epimorphism

```text
theta:F->B,
```

and an injective proper endomorphism `alpha:F->F` such that

```text
theta(alpha(F))=A.                                      (FQS1)
```

The construction is quantitatively injective: for one basis of `F` there is
`c>0` such that

```text
|alpha(w)|>=c|w|                                        (FQS1a)
```

for every reduced word `w`.  Moreover `ker(theta)` is the normal closure of
a finite explicit list of words.  Hence carrier-localized factorization
through `B` never requires authenticating an infinite relation list.

Precisely, if `r_1,...,r_s` normally generate `ker(theta)`, `sigma` is a
unitary representation of `F`, and a projection `E` reduces `sigma(F)`, then

```text
(sigma(r_j)-1)E=0 for every j
  implies (sigma(n)-1)E=0 for every n in ker(theta).    (FQS1b)
```

For a fixed expression

```text
n=product_l h_l r_(j_l)^(epsilon_l) h_l^(-1),
```

telescoping gives the quantitative estimate

```text
||(sigma(n)-1)E||_2
 <=sum_l ||(sigma(r_(j_l)^(epsilon_l))-1)E||_2
   +2 sum_l ||[E,sigma(h_l)]||_2.                      (FQS1c)
```

Consequently the ascending HNN extension

```text
E=<F,t | t x t^(-1)=alpha(x), x in a finite basis of F>
```

contains the base `F` and its proper conjugate `tFt^(-1)=alpha(F)`, while
the quotient chart `theta` sees their images as the prescribed pair

```text
B  and  A.                                              (FQS2)
```

The chart is deliberately not asserted to extend through `t`: if `A<B`, a
finite-dimensional unitary cannot conjugate the complete `B` action onto the
smaller `A` action without compensation.  The point of `(FQS1)` is that this
rank curvature can now be placed behind an honest injective self-copy rather
than an impossible termwise conjugacy of finite groups.

This is an algebraic interface, not yet a matrix obstruction.  To use a
predicate packet, one must still make the kernel of `theta` act trivially on
the relevant forbidden carrier, with normalized-HS cost controlled by a
fixed finite presentation.  Without that carrier-localized factorization,
an arbitrary representation of `F` need not see either finite quotient.
