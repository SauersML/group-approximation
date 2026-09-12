---
rg: 2
id: permutation-length-coset-decomposition-proof
kind: route
title: Split the action into orbits and count fixed points orbit by orbit
target: permutation-lengths-are-convex-hulls-of-coset-lengths
requires: []
artifacts:
  - research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md
---

Section 5 of the artifact. Decompose the finite `H`-set `V` into its orbits
`V_1, ..., V_r`. Fixed points split along the decomposition,

```text
fix_V(z) = sum_i fix_{V_i}(z),
```

because an orbit is invariant. Each orbit is isomorphic as an `H`-set to
`H/L_i` for a point stabilizer `L_i`, and an isomorphism of `H`-sets preserves
fixed-point counts, so `fix_{V_i}(z) = fix_{H/L_i}(z)`. Writing
`p_i = |V_i|/|V| = |H/L_i|/|V|`, which is a probability vector, gives

```text
l_V(z) = 1 - fix_V(z)/|V| = sum_i p_i ( 1 - fix_{H/L_i}(z)/|H/L_i| )
       = sum_i p_i l_{H/L_i}(z).
```

Conversely every convex combination of coset lengths with rational weights is
realized by a disjoint union of coset spaces with the right multiplicities, and
arbitrary real weights are approached by rational ones, so the described set is
exactly the closure of the achievable lengths.

The consequence stated in the claim is then the transport criterion of
Section 1 of the artifact rewritten with `l_V` expanded in this basis. The
proof is complete and uses no hypothesis on the group or on the given
bi-invariant length.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 8.3 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
