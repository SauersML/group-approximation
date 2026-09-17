---
rg: 2
id: finite-moment-hardness-via-structured-label-groups
kind: route
title: Dead -- supply finite-moment 2-to-1 hardness from an outer construction whose kernel pairings preserve a label structure
target: finite-moment-pairing-2to1-hardness
requires: []
---

**Dead.** The attack: build the outer 2-to-1 instance from a structured
inner test, so that the labels of each left vertex carry a structure
`Sigma` and every constraint at that vertex has a kernel pairing whose swap
is an automorphism of `Sigma`. The natural candidates are all of this form:
Grassmann or affine label spaces (kernel pairs `{x, x+v}` are translations,
so the swaps lie in `AGL`), projective lines (`PGL(2,q)`), code or design
automorphisms, product or block decompositions of the label set (the swaps
preserve a partition), and constructions that split the labels into two
halves treated separately (the swaps preserve a subset). Symmetric
constructions whose vertex stabilizers act transitively on the incident
edges are of this form whenever that stabilizer group does not contain
`Alt`.

Where every member dies: take the constants `m, K, q` and `C = C(m,K,q)`
that the target claim fixes, and the BKM balanced sets, whose pull-back mass
is a family-independent positive constant. Claim
`pair-swap-groups-of-smooth-pairing-designs-contain-alt` gives `n_1`
depending only on these, beyond which every exactly 2-wise uniform law with
`||1_E D_mu||_q <= C` has pair-swap group containing `A_(2n)`. The target
requires witnesses at `n >= max(n0, t)` for arbitrary `n0`, so take
`n0 >= n_1`. Then the invariant of `Sigma`, the group `Aut(Sigma)`, is
forced to contain `A_(2n)`, which means `Sigma` is trivial (for a subset
or partition: step (a) or (b), killed by an exact degree-two identity at
every `n >= 3`; for a primitive geometry: step (c), killed by
`|Aut(Sigma)| < 50 (2n)^(sqrt(2n))` against the `m^n` moment entropy
count). In the edge-transitive case the local pairing law is forced to be
the uniform law on all pairings, which is the circular Rich 2-to-1 input
of BKM Appendix B.

What survives: constructions whose kernel pairings generate `Alt(2n)` or
`S_(2n)` at every left vertex, with an exponentially large support that is
not a single orbit of the vertex stabilizer. Random and composed families
(`D o Q` in the smooth-design artifact) are of this kind, but none comes
with a soundness theorem.
