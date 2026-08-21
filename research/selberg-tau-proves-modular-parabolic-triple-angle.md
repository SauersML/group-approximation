---
rg: 2
id: selberg-tau-proves-modular-parabolic-triple-angle
kind: route
title: On parabolic invariants the two elliptic displacements coincide, so Selberg gives the angle
target: congruence-modular-parabolic-triple-angle-gap
requires:
  - modular-parabolic-restriction-is-a-three-projection-angle
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
---

Let `a^2=b^3=1`, `u=ab`, and let `F=M^u`.  Define

```text
D:F -> M,                    D y=(1-a)y.                (1)
```

If `y in F`, then `ab y=y`, hence `b y=a y` and
`D y=(1-b)y`.  Therefore

```text
P_a D y=0,                  P_b D y=0,                 (2)
```

so `D(F)` lies in `K=ker P_a cap ker P_b`.  Moreover

```text
ker D = M^u cap M^a = M^Gamma,                          (3)
```

because `b=a u`.

Selberg property `(tau)` for the congruence representations of the modular
group gives `kappa>0` such that every `y perpendicular M^Gamma` has

```text
max(||(1-a)y||,||(1-b)y||) >= kappa ||y||.              (4)
```

The two norms in (4) are equal on `F`, so `D` is bounded below by `kappa`
on `F minus M^Gamma`.

Finally, for `k in K`, `ak=-k`, and for `y in F`,

```text
<D y,k>=<y,(1-a)k>=2<y,k>=<y,2P_u k>.                  (5)
```

Thus `D^*=2P_u|K`.  An operator and its adjoint have the same nonzero
singular values.  Equations (3)--(5) prove that every nonzero singular value
of `P_u|K` is at least `kappa/2`, uniformly over all congruence coefficient
modules.
