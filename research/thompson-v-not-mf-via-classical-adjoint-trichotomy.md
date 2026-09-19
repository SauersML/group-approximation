---
rg: 2
id: thompson-v-not-mf-via-classical-adjoint-trichotomy
kind: route
title: Split every small-defect witness onto one invariant simple ideal, land densely in a classical adjoint group, and gap the three classical families separately
target: thompson-v-is-not-mf
requires: [thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups, thompson-v-gap-on-dense-projective-unitary-images, thompson-v-gap-on-dense-orthogonal-adjoint-images, thompson-v-gap-on-dense-symplectic-adjoint-images, thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes]
---

**The route.**
- Let `eps_SU`, `eps_SO` and `eps_Sp` be the constants of the three gap claims, and `eps` their
  minimum.
- Suppose `V` were MF. By `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes`, there are nontrivial
  irreducibles `sigma_n` of `G0` with `D(sigma_n) -> 0`.
- For large `n`, `D(sigma_n) < min(1/2, delta_(N_exc)/2, eps/2)`. The corollary of
  `thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups` then gives:
  - a classical `X(k)` with `k` large;
  - an `Inn(X(k))`-invariant inner product;
  - a homomorphism `tau_n : G0 -> Inn(X(k))` with dense image and `D(tau_n) <= 2 D(sigma_n) < eps`.
- This contradicts `Gap(X)`. Hence `V` is not MF.

**Each hole is necessary.** Item 5 of the normal-form claim shows that `thompson-v-is-not-mf` implies
each of the three gaps. So the route loses nothing. It reformulates the target exactly as the
conjunction of three classical-family statements.

**What changed relative to the plain gap.** A counterexample to the target must now be a sequence of
dense homomorphisms into one classical adjoint group. Relative to
`thompson-v-gap-witnesses-need-unbounded-lie-closure`, it no longer involves:

- a torus factor;
- a disconnected closure;
- products of simple factors;
- outer automorphisms.

Conversely, the three families are independent test beds for a refutation. An explicit sequence
`G0 -> PSU(k)` with dense image and relator images tending to scalars would make `V` MF. The same holds
in `SO(k)/{+-1}` or `Sp(k)/{+-1}` with relator images tending to the identity.
