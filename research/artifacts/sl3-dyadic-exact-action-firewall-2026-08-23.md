# Dyadic SL3 action: exact finite-action firewall

For

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),       X=A/C,
```

the type-zero Bruhat--Tits vertex action has a uniform GKEP orbit-atlas gap
on every genuine finite action of `A`.

The proof uses only two classical arithmetic facts and the already recorded
Kazhdan one-hot-label argument:

1. `SL_3(Z)` has property `(T)`;
2. every finite image of `SL_3(Z[1/2])` is already the image of `SL_3(Z)`.
   By CSP the finite map factors through an odd congruence level, and the
   integral group surjects at that level.

For a Kazhdan constant `kappa`, every exact-action atlas on the base coset
and one displaced coset has error at least

```text
kappa^2/(2 kappa^2+8).
```

Thus no exact congruence model works, and there is no separate
non-congruence exact finite-action escape.  If the action is sofic, its
approximating permutation maps stay uniformly outside the flexibly
correctable sector.  This is a no-go theorem, not a decision of action
soficity.

Primary classical inputs: Kazhdan property `(T)` for `SL_3(Z)`; the
congruence subgroup property for `SL_3` over `Z[1/2]`; and surjectivity of
`SL_3(Z) -> SL_3(Z/m)` for odd `m`.  The GKEP orbit-atlas definition is
Definition 2.1 of Gao--Kunnawalkam Elayavalli--Patchell,
arXiv:2401.04945v3 / *Research in the Mathematical Sciences* 12 (2025), 48.

