---
rg: 2
id: agent-packet-root-bridge-is-perfect-kernel-separation
kind: claim
title: A root bridge preserving the perfect mark is exactly a perfect-kernel character separator
distinct_from:
  forbidden-character-kernel-quotient-compiler: That directly quotients the contextual group once one kernel separates all forbidden characters; this characterizes any attempted odd-root bridge for one packet projection and constructs a finite alternating-wreath bridge from the same separator.
  agent-packet-root-finite-detectors-are-normal-quotient-selectors: That classifies a prescribed finite overgroup by the intersection with the root normal closure; this proves the converse realization theorem while preserving the entire old group and its designated perfect representation.
  agent-pk-affine-ghost-survives-quotient: That computes the ghost surviving the maximal projective quotient; this identifies the same affine-hull condition as the exact obstruction to every perfect-compatible root bridge.
---

Let `G` be a finitely presented group, let `H<=G` be finite, let
`q in C[H]` be a projection, and let

```text
pi:G->U(Mcal)                                           (PKB1)
```

be an exact representation in a finite tracial von Neumann algebra.  The
following are equivalent.

1. There is a finitely presented group `Gamma` containing `G`, an abstractly
   nontrivial element `z in Gamma` of order three, and an extension
   `tilde pi` of `pi` such that

   ```text
   tilde pi(z)=1,
   q=0 in C^*(Gamma/<<z>>).                             (PKB2)
   ```

2. There is a normal subgroup `M normal H` such that

   ```text
   M <= ker(pi|H),
   q=0 in C[H/M].                                      (PKB3)
   ```

Moreover, under `(PKB3)` the bridge in `(PKB2)` can be chosen as an amalgam

```text
Gamma=G *_H K                                          (PKB4)
```

with `K` finite.  Its root `z` satisfies, for every exact
finite-dimensional representation `rho` of `Gamma`,

```text
tr(rho(q)) <= C ||rho(z)-1||_2^2,                      (PKB5)
```

and fixed finite-group correction gives the corresponding normalized-HS
estimate for approximate representations, with a dimension-independent
presentation-error term.

Thus an infinite property-`(T)` normal closure is unnecessary when the
perfect-kernel separator exists, and cannot remove the need for that
separator.  Any root bridge for which killing the root algebraically kills
the physical packet projection is only a disguised forbidden-character
kernel quotient.

For a binary context packet `H`, let `R<=hat H` denote the spectral support
of `pi|H`, and let `q=e_chi` be a forbidden character atom.  Then `(PKB3)`
is equivalent to

```text
chi notin span(R),                                     (PKB6)
```

or, on the fixed `J=-1` slice, to the forbidden assignment lying outside
the affine hull of the perfect support.  A forbidden affine-hull ghost
therefore admits no bridge of type `(PKB2)`.  The known non-CE BCS separation
does not assert `(PKB6)`; if it did for every forbidden type, the existing
`forbidden-character-kernel-quotient-compiler` would already give the final
group directly.

This closes the proposed positive property-`(T)` boundary: ordinary
root-normal-closure amplification helps exactly on the already separated
affine face, while the unresolved nonlinear types remain unchanged.
