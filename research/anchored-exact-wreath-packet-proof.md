---
rg: 2
id: anchored-exact-wreath-packet-proof
kind: route
title: Intersect every exact representation orbit with the diffuse pin and apply the centralizer cover
target: anchored-exact-wreath-packets-have-zero-entropy
requires:
  - diffuse-pin-centralizer-has-zero-quadratic-covering
---

Choose one reference tuple `X_{j,d}` from each unitary-equivalence class that
meets the anchored fiber.  Thus every reference has the same prescribed pin
`D_d`.  If an exact tuple `Y` in its orbit also has pinned coordinate `D_d`,
write `Y=U*X_{j,d}U`.  Comparing pinned coordinates gives

```text
U* D_d U=D_d,
```

so the anchored part of this entire global orbit lies in the orbit of
`X_{j,d}` under the unitary centralizer of `D_d`.  Therefore

```text
Omega_d |_(pin=D_d)
 subset union_(j=1)^N_d {U*X_{j,d}U:[U,D_d]=0}.          (AEP1)
```

The matrices `D_d` form a bounded microstate sequence for a diffuse
self-adjoint.  Apply
`diffuse-pin-centralizer-has-zero-quadratic-covering`, including its
subquadratic-union conclusion `(DPC3)`, to `(AEP1)`.  Hypothesis `(AEW1)`
then gives `(AEW2)`.

For the regular-character packet the character orthogonality calculation
forces `rho` to be a multiple of the left regular representation, so
`N_d=1`.  The general finite-group representation count follows by assigning
one multiplicity in `{0,...,d}` to each irreducible.  These are exactly the
class counts already isolated by
`finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge`; the present
argument shows that passing from orbital language to Hayes' fixed diffuse pin
does not restore any quadratic family.
