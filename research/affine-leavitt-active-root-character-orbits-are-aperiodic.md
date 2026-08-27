---
rg: 2
id: affine-leavitt-active-root-character-orbits-are-aperiodic
kind: claim
title: The active last-column root module has no nontrivial finite Steinberg-actor character orbit
distinct_from:
  affine-leavitt-steinberg-mark-is-fd-invisible: that kills the active root in every finite-dimensional representation of the whole Steinberg group; this identifies the finite-character-orbit mechanism for one abelian root module under a rank-five actor.
  infinite-character-actor-kills-fd-mark: that is an abstract one-seed theorem; this verifies its aperiodic character hypothesis inside the affine-Leavitt Steinberg group.
  simple-t-augmentation-module-is-aperiodic: that uses simplicity and the regular augmentation module; this uses active-root transvections and finite-dimensional invisibility of the Leavitt idempotent.
---

ESTABLISHED.  Let

```text
R=L_A(k[C_aff]),                  G=St_6(R),
H=<x_ij(r):1<=i!=j<=5, r in R> < G,
M=<x_i6(r):1<=i<=5, r in A R> < G.                         (ALC1)
```

Here the affine packet uses the repository's finite splitting field `k` of
characteristic `p>=5`.  The root relations identify `M` with the additive
elementary abelian `p`-group `(A R)^5`; it is normalized by `H`.  The group
`H` is a quotient of `St_5(R)`, hence has property `(T)`.

Every finite `H`-orbit in `M_hat` consists only of the trivial character.
Consequently, for a fixed Kazhdan generating set of `H`, every nontrivial
character orbit is infinite and its Schreier graph has one uniform positive
bottom spectral gap.

The characteristic-two formulation is not available for the current affine
packet: its active central idempotent was constructed over a splitting field
of characteristic at least five.  No binary Pauli seed is needed.  The
`p`-character PVM of `M` and the nontrivial active root

```text
m_0=x_16(A)                                                (ALC2)
```

already supply the marked mass: any character on which `m_0` is nontrivial
lies in a nontrivial expanding orbit.

