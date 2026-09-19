---
rg: 2
id: exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss
kind: claim
title: Every exact dyadic conductor band loses a uniform fraction under one parahoric depth shift
distinct_from:
  depth-shifted-regular-overlap-is-exactly-one-sixteenth: that computes the sharp overlap for regular congruence modules; this treats every representation supported on irreducibles of one exact conductor, with a weaker but uniform one-eighth loss.
  regular-congruence-depth-mixtures-remain-folner: that constructs cross-conductor Folner profiles; this proves that such cross-conductor routing is necessary by excluding asymptotically full overlap inside each individual conductor band.
  bounded-conductor-width-pays-uniform-first-exit: that is an abstract marginal estimate depending on the number of occupied depths; this is an arithmetic irreducible-restriction estimate independent of multiplicities and conductor depth.
---

Let `a>=4`, `Q_a=SL_3(Z/2^a Z)`, and let `Lambda_0`, the two quotient
maps `alpha_a,beta_a:Lambda_0->Q_a`, and their kernels `K_A(a),K_B(a)`
be the two depth-shifted parahoric maps of
`two-power-sector-conjugator-dichotomy`.  Let `pi` be any representation of
`Q_a` all of whose irreducible constituents have minimal congruence
conductor exactly `a`.  For any representation `theta` of `Q_a`, the
maximal common subrepresentation of

```text
pi o alpha_a       and       theta o beta_a
```

has dimension at most

```text
(7/8) dim(pi).                                           (DCL1)
```

The same conclusion holds with the two sides reversed.  Consequently a
unitary parahoric intertwiner whose defect tends to zero on a sequence of
positive-conductor congruence representations cannot route asymptotically
all of an exact-conductor band to the same conductor.  More precisely, if
`kappa_0` is a Kazhdan constant for the fixed generators of `Lambda_0`, then
every unitary between two equal-dimensional exact-conductor-`a` modules
satisfies

```text
max_s ||theta(beta_a(s))V-V pi(alpha_a(s))||_2
 >= kappa_0/sqrt(8).                                    (DCL2)
```

At least one eighth of the band must exit to another conductor or pay this
uniform intertwining defect.

Thus the unbounded dyadic enemy is forced into genuinely cross-conductor
transport.  Same-level multiplicities, however large, cannot realize it.
This does not close the branch: triangular mixtures over unboundedly many
conductors can route the lost mass into neighboring bands, as in
`regular-congruence-depth-mixtures-remain-folner`.
