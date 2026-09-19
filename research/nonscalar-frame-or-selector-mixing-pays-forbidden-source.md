---
rg: 2
id: nonscalar-frame-or-selector-mixing-pays-forbidden-source
kind: claim
title: A nonscalar carrier frame either covers the source or pays selector-mixing energy
distinct_from:
  predicate-preserving-nonscalar-frames-miss-forbidden-source: that proves exact selector-equivariant carriers share the forbidden kernel and hence cannot frame the source; this gives the robust positive dichotomy when a separately supplied frame is allowed to break selector equivariance
  common-source-hnn-bridges-need-one-gram-saturation-identity: that assumes scalar source saturation and uses it for polar alignment; this converts an operator frame bound into a quantitative charge against the selector-intertwining defects
  common-partial-isometry-swap-game-compiler: that still has to groupify a common frame and the nonlinear predicate rows; this is the dimension-free analytic inequality available once such a frame is present
---

**ESTABLISHED.** Let `p` be the allowed-support projection of one Boolean
selector algebra on a finite tracial source, let `Q` commute with `p`, and put

```text
F=Q(1-p).                                                (NSF1)
```

For `1<=i<=N`, let `S_i` be a partial isometry from the common source to a
target space with

```text
S_i^*S_i=Q.                                             (NSF2)
```

Let `p_i` be the target copy of the allowed-support projection and let
`q_i<=p_i` be an arbitrary, possibly noncommuting, selected target carrier.
Pull it back to the common source:

```text
r_i=S_i^*q_iS_i.                                       (NSF3)
```

If these pulled-back carriers form an operator frame

```text
sum_i r_i >= kappa Q                                   (NSF4)
```

for some `kappa>0`, then

```text
kappa ||F||_2^2
 <= sum_i ||(p_iS_i-S_ip)F||_2^2
 <= sum_i ||p_iS_i-S_ip||_2^2.                         (NSF5)
```

Thus a genuine nonscalar frame is not defeated by the forbidden common
kernel. Instead it gives a sharp dichotomy: either the forbidden source mass
is small, or the transports pay a proportional selector-consistency energy.
Exact predicate-preserving transport is the zero-energy endpoint of `(NSF5)`
and forces `F=0`, recovering the obstruction in
`predicate-preserving-nonscalar-frames-miss-forbidden-source`.

## Compiler consequence

This identifies the first architecture not excluded by the scalar-bus and
predicate-preserving-frame no-gos. Install a finite common-source frame
`(NSF4)` whose transports are allowed to mix selector and payload, and include
the literal intertwining rows `p_iS_i-S_ip` in the consistency energy. Then
the same mixing which crosses the forbidden selector wall is automatically
charged by `(NSF5)`; it need not preserve predicate semantics for free.

For `common-partial-isometry-swap-game-compiler`, `(NSF5)` can replace the
impossible demand that every selected carrier be selector-equivariant. The
remaining construction problem is now concrete and algebraic: groupify one
dimension-independent frame `(NSF4)` on the literal D8 source while wordizing
the finitely many selector-mixing residuals. Once that is done, the existing
predicate and consistency Gram rows plus
`centralized-gram-row-words-upgrade-trace-gap-to-vector-gap` provide the
whole-vector-state endpoint.

