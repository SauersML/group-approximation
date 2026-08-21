---
rg: 2
id: sp4-metaplectic-not-coboundary-limit-proof
kind: route
title: Coboundaries are a continuous image of a Tychonoff-compact cochain space, hence pointwise closed
target: sp4-metaplectic-class-pointwise-coboundary-limit
requires: []
---

The full argument is in the claim body; record of the three steps.
`T^Gamma` with the product topology is compact (Tychonoff) and the
coboundary map `delta : T^Gamma -> Z^2(Gamma, T)`,
`(delta b)(g,h) = b(g) b(h) b(gh)^(-1)`, is continuous coordinatewise, so
`B^2(Gamma, T) = delta(T^Gamma)` is compact; `Z^2(Gamma, T) subset
T^(Gamma x Gamma)` is Hausdorff, so `B^2` is closed in the pointwise
topology.  A pointwise limit of coboundaries is therefore a coboundary,
and `(MC1)` for the nontrivial metaplectic class of `Sp_4(Z)` (or any
nonzero scalar class of any discrete group) is impossible.  The
nontriviality of the metaplectic class of `Sp_4(Z)` itself is the
nonsplitness of the Deligne double cover, recorded with the
Ioana--Spaas--Wiersma Example 1.3(i) import in
`sp2g-z-full-c-star-algebra-has-llp`.

Nonconstructive remark: closedness shows some finite window `F` has
positive phase-alignment defect
`inf_b max_(g,h in F) | b(g) c_pi(g,h) b(h) b(gh)^(-1) - 1 | > 0`, but
exhibits none; an explicit window with a certified positive defect would
be a quantitative cocycle-rigidity input for the Deligne lane
(`deligne-central-mark-hs-collapse`).
