---
rg: 2
id: odd-maslov-ucp-retract-must-hide-generator-defect
kind: claim
title: Every odd-Maslov ucp retract into an even amplification must hide generator defect in its positive kernel
invalidates:
  - odd-maslov-llp-via-faithful-non-equivariant-retract
distinct_from:
  finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres: that rules out finite generator-equivariant Morita shifts by their cocycle difference; this treats arbitrary non-equivariant split ucp maps and locates the only possible escape in the positive kernel of the retraction.
  maslov-generator-complete-order-model-is-llp-strength: that says a generic liftable complete-order model already proves LLP; this proves that any complete-order retract through an even Maslov amplification must be strongly nonmultiplicative and nonfaithful.
  braid-prefix-label-space-has-no-ucp-expectation: that rules out one explicit diagonal-bimodule expectation by a finite Gram witness; this is an abstract multiplicative-domain obstruction coming from Deligne finite-dimensional invisibility.
---

**ESTABLISHED.**  Let `A_alpha` be an odd Maslov fibre, with

```text
alpha in {1/3,2/3,1/6,5/6},
```

and let `A_epsilon` be an even fibre with `epsilon in {0,1/2}`.  Suppose
there are ucp maps

```text
i:A_alpha -> M_n(A_epsilon),       r:M_n(A_epsilon)->A_alpha,
r i = id_(A_alpha).                                      (OUR1)
```

For every canonical projective generator `u_s` put

```text
d_s^L=1-i(u_s)^*i(u_s),       d_s^R=1-i(u_s)i(u_s)^*.
```

Then

```text
d_s^L,d_s^R >= 0,             r(d_s^L)=r(d_s^R)=0.       (OUR2)
```

At least one of these positive defects is nonzero.  Consequently the
retraction `r` is not faithful.  In particular `(OUR1)` cannot exist with
any of the following additional properties:

1. `r` is a faithful ucp map (hence not a faithful conditional expectation);
2. every `i(u_s)` is unitary;
3. `i` is a unital order-zero map;
4. the range inclusion is a star-homomorphism and `r` is a conditional
   expectation onto it.

Thus a genuinely non-equivariant ucp-retract attack is not formally dead,
but its escape is sharp: it must push a positive multiplicative defect of at
least one canonical generator into the positive kernel of a nonfaithful
retraction.  Ordinary finite Morita equivalence, faithful corner compression,
and generator-unitary models cannot do this.

The proof is `odd-retract-positive-kernel-proof`.

