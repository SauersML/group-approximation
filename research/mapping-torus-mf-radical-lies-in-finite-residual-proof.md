---
rg: 2
id: mapping-torus-mf-radical-lies-in-finite-residual-proof
kind: route
title: Descend the action to the maximal residually finite quotient
target: mapping-torus-mf-radical-lies-in-finite-residual
requires:
  - finitely-generated-rf-automorphism-mapping-torus-is-rf
---

The finite residual

```text
R = R_fin(K) = intersection {ker(f) | f:K -> F, F finite}
```

is characteristic.  Hence `phi` descends to an automorphism `bar(phi)` of
`Q=K/R`, and the quotient map extends to a surjection

```text
q : K semidirectProduct_phi Z
      -> Q semidirectProduct_bar(phi) Z                 (FRB5)
```

whose kernel is `R x {0}`.

The group `Q` is finitely generated because `K` is, and it is residually
finite by the definition of `R`: a nonidentity class represented by `k` has
`k notin R`, so some finite quotient of `K` separates `k` and factors
through `Q`.  By
`finitely-generated-rf-automorphism-mapping-torus-is-rf`, the target of
`(FRB5)` is residually finite.  Functoriality of the finite residual therefore
gives

```text
R_fin(G) <= ker(q)=R x {0}.                             (FRB6)
```

For the reverse inclusion, identify `K` with its canonical subgroup of `G`.
The finite residual of an arbitrary subgroup maps into the finite residual of
the ambient group: intersect any finite-index subgroup of `G` with `K`.
Hence `R x {0} <= R_fin(G)`.  Together with `(FRB6)` this proves the exact
finite-residual formula in `(FRB1)`.

The MF radical of every group is contained in its finite residual, since
finite groups are MF.  Thus the exact formula also gives the second line of
`(FRB1)`, and `(FRB2)` is immediate.

The same argument with a fixed `phi`-invariant `A normal K` proves `(FRB3)`:
the descended mapping torus of the finitely generated residually finite
quotient `K/A` is again residually finite and MF.

For completeness, consider the characteristic-zero seed.  In the notation
of `torsion-free-lef-kazhdan-non-rf-seed`, write

```text
Gamma = EL_3(R_0) semidirect M,
R_0 = Z[t,t^(-1)],
M = R_0^(3*) directSum R_0^3,
```

and let `Gamma_0` be the finite-index torsion-free characteristic subgroup
chosen there.  We claim `Z(Gamma_0)=1`.

Indeed, `Gamma_0 intersect M` has finite index in the torsion-free abelian
group `M`.  If `(h,w)` is central in `Gamma_0`, commuting with this
finite-index translation subgroup says that `h` fixes it pointwise.  Every
element of `M` has a nonzero integer multiple in that subgroup, and `M` is
torsion-free; hence `h` acts trivially on all of `M`.  The natural summand is
a faithful `EL_3(R_0)`-module, so `h=1`.

Now `w` is fixed by the finite-index image of `Gamma_0` in `EL_3(R_0)`.  For
every elementary matrix `e_ij(1)`, some positive power belongs to that image:
two of its nonnegative powers lie in the same coset.  This power is
`e_ij(n)` for some `n>0`.  Invariance under all these matrices forces every
coordinate of both the natural and dual components of `w` to vanish, because
`R_0` is torsion-free.  Thus `w=0` and `Z(Gamma_0)=1`.

The kernel `A=C/C_+` in the seed is central.  Conversely, every central
element of `K` maps to a central element of `Gamma_0`, hence to the identity.
Therefore `Z(K)=A`.  The quotient `Gamma_0` is finitely generated and
residually finite by finite index and linearity, and it is nontrivial.  Apply
`(FRB3)` to the characteristic subgroup `A=Z(K)` to obtain `(FRB4)` for every
automorphism of the seed.
