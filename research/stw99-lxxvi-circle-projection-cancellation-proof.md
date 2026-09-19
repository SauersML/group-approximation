---
rg: 2
id: stw99-lxxvi-circle-projection-cancellation-proof
kind: route
title: Cancel the fiber and then cancel the K1 clutching component
target: stw99-lxxvi-circle-projections-cancel
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Cut the circle at a basepoint.  A projection `P` over `C(T,D) tensor K`
restricts to a projection path on `[0,1]`.  A path of projections is
unitarily trivial over the interval, so `P` is obtained by clutching a fixed
finitely generated projective module `pD^n` at the two endpoints.  The
clutching datum is a unitary in the unitization of the corner

```text
p M_n(D) p.
```

Changing the interval trivialization changes this unitary within its
connected component.  Thus, once the fiber projection is fixed, the bundle
is determined by a component of the corner's unitary group.

Now suppose

```text
P directSum R  ~  Q directSum R.                       (1)
```

Evaluation at the basepoint and cancellation in `D` (stable rank one)
identify the fiber projections of `P` and `Q`; call the common nonzero fiber
`p`.  If it is zero then both bundles are zero and there is nothing to prove.
Since `D` is simple, `p` is full.  Write `u_P,u_Q,u_R` for the clutching
unitaries after compatible choices of trivialization.  Relation (1) gives

```text
[u_P]+[u_R]=[u_Q]+[u_R]
```

in the `K_1` group of the stabilized full corner.  Cancelling in this group
and using Morita invariance identifies `[u_P]=[u_Q]` in
`K_1(p M_n(D) p)`.

Every hereditary corner of a stable-rank-one algebra again has stable rank
one.  Hence

```text
U((p M_n(D) p)^~)/U_0((p M_n(D) p)^~)
    -> K_1(p M_n(D) p)
```

is injective.  The two clutching unitaries are therefore homotopic, so the
corresponding projective `C(T,D)`-modules are isomorphic.  Equivalently,
`P~Q`, which proves cancellation.
