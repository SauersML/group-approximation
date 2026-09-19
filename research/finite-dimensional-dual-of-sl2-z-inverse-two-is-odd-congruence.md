---
rg: 2
id: finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
kind: claim
title: Every finite-dimensional unitary representation of SL2(Z[1/2]) is an odd-congruence representation
distinct_from:
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that uses finite-dimensional co-density and Selberg tau in the HNN argument; this gives the explicit p=2 representation classification and its spectral proof.
  sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index: that is the normal-subgroup theorem input; this combines it with fourth-power spectral dynamics and the congruence subgroup property.
  bs14-character-split-leaves-only-the-regular-microstate-face: that treats tracial-ultraproduct representations; this classifies honest finite-dimensional representations and explicitly does not classify the regular ultraproduct face.
---

Put

```text
Gamma=SL_2(Z[1/2]),
u=[[1,1],[0,1]],
h=diag(2,1/2).
```

Every finite-dimensional unitary representation `rho:Gamma->U(d)` has
finite image and factors through

```text
SL_2(Z/m)                                                (FDU1)
```

for some odd integer `m`. Conversely every unitary representation of an
odd congruence quotient pulls back to one of `Gamma`. Hence the
finite-dimensional unitary dual of `Gamma` is the directed union of the
duals of its odd congruence quotients.

The relation

```text
h u h^(-1)=u^4                                           (FDU2)
```

makes the finite multiset `Spec(rho(u))` invariant under `z|->z^4`. Every
point is periodic: for some `k>=1`,

```text
z^(4^k)=z,       so z^(4^k-1)=1.                        (FDU3)
```

Thus `rho(u)` has finite odd order `N`. The Weyl element conjugates `u` to
the opposite root, so the lower-root image has the same finite order. The
kernel of `rho` contains the normal closure of `u^N`. By the normal subgroup
theorem for this two-place irreducible S-arithmetic lattice, that normal
closure has finite index; hence `rho(Gamma)` is finite. Serre's congruence
subgroup property then puts a principal congruence subgroup in `ker(rho)`.
Since `2` is a unit in `Z[1/2]`, its level is coprime to `2`, proving
`(FDU1)`.

This exact classification does not imply that an asymptotically compatible
pair of exact `SL_2(Z)` vertex representations is close to such endpoints.
The pair produces an exact homomorphism of `Gamma` only after passing to a
tracial matrix ultraproduct, and that representation need not be finite-
dimensional. Character rigidity corrects its finite-character central
summand, but permits the regular character summand. Moving that regular
summand coordinatewise to odd-congruence representations is exactly
`regular-iwahori-relative-congruence-exactification`, not a consequence of
`(FDU1)`.
