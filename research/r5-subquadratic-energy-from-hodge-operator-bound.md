---
rg: 2
id: r5-subquadratic-energy-from-hodge-operator-bound
kind: route
title: Trade a square-root operator norm for sublinear edge-count energy
target: r5-subquadratic-carmichael-energy
requires:
  - carmichael-edge-hodge-operator-has-root-m-norm
---

Assume `(SF1)`--`(SF2)`.  Orthogonality of the two summands in `H_M` gives

```text
E_M = ||e||^2 = ||T_M f||^2 + ||D^* q||^2.
```

The gauge term is the coboundary of the vertex gauges, and by
`collective-centralizer-cycles-are-free-gauge-identities` its contribution to
the Carmichael edge relations is a free-word identity: choosing the vertex
gauges to be the endpoint corrections `Q_i` themselves makes `q=0`, so the
second term may be taken to vanish.  The first term obeys

```text
||T_M f||^2 <= ||T_M||_(2->2)^2 ||f||^2
            <= C M sum_(k<=K) ||f_k||_2^2,
```

and each `f_k` is a unitary translate of a defining-relator residual, so
`||f_k||_2 = ||r_k(U)-I||_2 <= def_R(U)` by unitary invariance.  With `K`
independent of `M`,

```text
E_M <= C K M def_R(U)^2.                                      (SF3)
```

For a **fixed** model `U` the right side is a constant times `M`, hence
`o(M^2)`, which is `(ACE)`.  The implied constant is allowed to depend on `U`
in `(ACE)`, so no uniformity in `d` or in the defect is lost or needed here.

This is a strict weakening, not a restatement: `(SF3)` is linear in the packet
size while `(ACE)` permits anything sublinear in the edge count, and `(SF3)`
carries a presentation constant while `(ACE)` permits a model-dependent one.
An `(ACE)` proof by any other mechanism — for instance a direct construction
of packets with a sublinear-density bad edge set, in the manner of the second
packet of `carmichael-energy-uniform-criteria-incomparable` — would bypass the
operator norm entirely.
