---
rg: 2
id: one-hot-central-character-selector-forces-weight-three-ghost
kind: claim
title: A common central-character selector allowing arbitrary one-hot atoms also admits a weight-three ghost
distinct_from:
  affine-context-barrier: that says equations among commuting involutions cut out an affine character set; this proves the selector-relative obstruction even when an arbitrary ambient group and a common central-character corner are added.
  one-hot-selector-parity-barrier: that computes the affine closure of one-hot words inside an elementary abelian packet; this uses the group of one-dimensional representations to show that a central selector cannot remove the ghost while retaining deterministic completeness models.
  sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm: that realizes the four desired characters by a rational local projection; this proves why one common central-character projection cannot replace the still-missing cross-node carrier correlation.
---

**ESTABLISHED.**  Let `G` be a group, let `Z` be a central subgroup, and
let `zeta:Z->U(1)` be a character.  Suppose `r_0,...,r_3` are commuting
involutions in `G`.  Assume that for at least three distinct indices
`a=0,1,2` there are one-dimensional characters

```text
chi_a:G->U(1)
```

such that

```text
chi_a|Z=zeta,
chi_a(r_b)=(-1)^[a=b].                                  (CCG1)
```

Then the same central-character sector also contains a weight-three ghost:
there is a one-dimensional character `psi` with

```text
psi|Z=zeta,
psi(r_0)=psi(r_1)=psi(r_2)=-1,
psi(r_3)=+1.                                           (CCG2)
```

Indeed put

```text
psi=chi_0 (chi_0 chi_1^(-1)) (chi_0 chi_2^(-1))
   =chi_0^3 chi_1^(-1) chi_2^(-1).                     (CCG3)
```

The two ratios in parentheses are trivial on `Z`, so `(CCG3)` restricts to
`zeta`.  On involutions inversion does not change a sign, and symmetric
difference of the three negative sets

```text
{0}, {0,1}, {0,2}
```

is `{0,1,2}`, proving `(CCG2)`.

Consequently no common central-character corner can both

1. realize arbitrary four-outcome PVM multiplicities, which in particular
   requires the deterministic representations concentrated on each desired
   one-hot atom; and
2. force the joint spectrum of `r_0,...,r_3` to contain only the four
   one-negative characters.

The conclusion is independent of the order of `zeta`; using character
ratios is what preserves the selector.  It applies to finite central packet
extensions as well as to an arbitrary ambient group.  A successful
`SYNC_4` carrier must therefore be noncentral, representation-dependent, or
use a genuinely non-character corner coupling.  Adding one more finite
central sign or finite central-character label cannot solve the one-edge
carrier problem while preserving arbitrary completeness-side atom weights.
