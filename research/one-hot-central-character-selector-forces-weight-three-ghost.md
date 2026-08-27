---
rg: 2
id: one-hot-central-character-selector-forces-weight-three-ghost
kind: claim
title: A common central-character selector allowing arbitrary one-hot atoms also admits a weight-three ghost
distinct_from:
  finite-group-selector-induction-barrier: that uses induction from a commuting selector subgroup inside one finite group; this uses tensor products of deterministic-sector representations and applies to an arbitrary ambient group and central character.
  one-hot-selector-parity-barrier: that computes the affine closure of one-hot words inside an elementary abelian packet; this uses the group of one-dimensional representations to show that a central selector cannot remove the ghost while retaining deterministic completeness models.
  sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm: that realizes the four desired characters by a rational local projection; this proves why one common central-character projection cannot replace the still-missing cross-node carrier correlation.
---

**ESTABLISHED.**  Let `G` be a group, let `Z` be a central subgroup, and
let `zeta:Z->U(1)` be a character.  Suppose `r_0,...,r_3` are commuting
involutions in `G`.  Assume that for at least three distinct indices
`a=0,1,2` there are nonzero finite-dimensional representations

```text
pi_a:G->U(V_a)
```

such that

```text
pi_a(z)=zeta(z) I,
pi_a(r_b)=(-1)^[a=b] I.                                 (CCG1)
```

Then the same central-character sector also contains a weight-three ghost:
there is a nonzero finite-dimensional representation `Psi` with

```text
Psi(z)=zeta(z) I,
Psi(r_0)=Psi(r_1)=Psi(r_2)=-I,
Psi(r_3)=+I.                                           (CCG2)
```

Indeed put

```text
Psi=pi_0 tensor pi_0 tensor pi_0
    tensor conjugate(pi_1) tensor conjugate(pi_2).      (CCG3)
```

The diagonal tensor product is a representation of `G`.  Its central
character is

```text
zeta^3 conjugate(zeta)^2=zeta.
```

Conjugating an involutive scalar sign does not change it.  The symmetric
difference of the five negative sets

```text
{0}, {0}, {0}, {1}, {2}
```

is `{0,1,2}`, proving `(CCG2)`.  Thus the auxiliary part of each
deterministic-sector representation may be arbitrarily noncommutative; no
one-dimensionality assumption is used.

Consequently no common central-character corner can both

1. realize arbitrary four-outcome PVM multiplicities, which in particular
   requires the deterministic representations concentrated on each desired
   one-hot atom; and
2. force the joint spectrum of `r_0,...,r_3` to contain only the four
   one-negative characters.

The conclusion is independent of the order of `zeta`; the `3-2` tensor
power is what preserves the selector.  It applies to finite central packet
extensions as well as to an arbitrary ambient group, even when a
deterministic selector pattern needs a higher-dimensional auxiliary
representation.  A successful
`SYNC_4` carrier must therefore be noncentral, representation-dependent, or
use a genuinely non-character corner coupling.  Adding one more finite
central sign or finite central-character label cannot solve the one-edge
carrier problem while preserving arbitrary completeness-side atom weights.
