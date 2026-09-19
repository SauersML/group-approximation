---
rg: 2
id: free-coset-swap-factor-has-zero-second-fold-bias
kind: claim
title: The exact free-coset swap factor has zero second-fold bias
distinct_from:
  canonical-arithmetic-swap-fold-gram-is-arcsine: that transfers the Haar fold law to every hypothetical canonical matrix microstate sequence; this computes it unconditionally in the exact group factor and makes no Connes-embeddability assertion.
  full-arithmetic-bernoulli-projection-orbit-is-free-spherical: that uses commuting Bernoulli coordinates, for which the fold square is one; this uses free binary coset lamps, for which the fold itself is Haar.
  finite-swap-conjugate-moments-do-not-fold-arithmetic-double: that constructs finite regular models for each fixed lamp-only moment table after omitting the actor extension; this keeps the complete actor and all group relations, but in an arbitrary finite tracial factor rather than matrices.
---

**ESTABLISHED EXACT TRACIAL FIREWALL.**  Let `C<A`, choose `h in A-C`, and
put

```text
E=<A,s | s^2=1, [s,C]=1>
  ~=(*_(x in A/C) C_(2,x)) rtimes A.                    (FCS1)
```

In the canonical group factor `L(E)`, let `S=lambda(s)`,
`H=lambda(h)`, and

```text
V=HSH^*S.
```

Then the actor has its regular character, `tau(S)=0`, and

```text
tau(V^k)=0                 for every k!=0.              (FCS2)
```

In particular

```text
Re tau(V^2)=0.                                         (FCS3)
```

Indeed `HSH^*` and `S` are the two binary lamp generators indexed by the
distinct cosets `hC` and `C`.  Their product is a cyclically reduced word of
infinite order in the free product lamp kernel.  Every nonzero power is
nontrivial, proving `(FCS2)` by the canonical group trace.

For

```text
P=(I-S)/2,                    Q=HPH^*,
```

the two-projection identity gives

```text
tau(QPQ-(QPQ)^2)
 =(1/16)(1-Re tau(V^2))=1/16.                           (FCS4)
```

Equivalently the fold is Haar and the Gram law is
`(1/2)delta_0+(1/2)Arcsine_[0,1]`.

For the arithmetic pair

```text
C=SL_3(Z)<A=SL_3(Z[1/2]),
```

this is an exact zero-defect tracial countermodel to the conclusion of
`regular-actor-balanced-swap-has-positive-second-fold-bias`, with exactly
its regular-actor and balanced-swap profile.  It is not a matrix
countermodel: Connes embeddability of `L(E)` is precisely the unresolved
group problem.

Consequently the positive-bias terminal cannot follow from a universal
tracial identity, positivity/SOS in the group von Neumann algebra, or any
dimension-blind use of the arithmetic relators.  A proof must use a property
specific to matrix ultraproduct realizations and thereby exclude the exact
packet `(FCS1)--(FCS4)` from every Connes-embeddable model.
