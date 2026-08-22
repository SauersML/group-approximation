---
rg: 2
id: infinite-order-central-mark-group-proof
kind: route
title: Shear the Britton compression defect into a protected central integer
target: infinite-order-central-mark-group
requires:
  - concrete-compression-source
  - hnn-torsion-theorem
  - heisenberg-hnn-shear-promotes-infinite-defect-to-central-mark
artifacts:
  - research/artifacts/infinite-central-mark-hnn-shear-2026-08-21.md
---

## Direct construction

Take `K=ker(SL_3(Z)->SL_3(Z/3Z))` and

```text
Gamma=Z^3 semidirect K,
alpha(v,A)=(2v,A),
a=(e_1,I).
```

The principal congruence subgroup `K` is torsion-free, finite index in
`SL_3(Z)`, finitely presented, and has property (T).  Hence `Gamma`, a
finite-index subgroup of the integral affine Kazhdan group, is torsion-free,
finitely presented, and has property (T).  The endomorphism `alpha` is
injective and `a` is outside its image.

Apply `concrete-compression-source` to the base `Gamma times <c>`.  It gives
the HNN group

```text
P=<Gamma,c,t | [c,Gamma]=1,
                  t gamma t^-1=alpha(gamma) (gamma in Gamma)>
```

and the nontrivial Britton word

```text
u=[t c t^-1,a].
```

Only finitely many relations are needed because `Gamma` is finitely
presented and finitely generated.  The base `Gamma times <c>` is
torsion-free, so `hnn-torsion-theorem` makes `P` torsion-free.  Therefore
the nontrivial element `u` has infinite order.

Now apply
`heisenberg-hnn-shear-promotes-infinite-defect-to-central-mark` to `(P,u)`:

```text
H=<P,z,s | [z,P]=1, s u s^-1=u z, s z s^-1=z>.
```

Here `[z,P]=1` abbreviates finitely many relations against a finite
generating set of `P`.  The shear theorem proves that `H` is torsion-free
and finitely presented, that `z` is a nontrivial central element of infinite
order, and that

```text
z=(s u s^-1)u^-1 in <<u>>_H.
```

Both HNN base embeddings are injective.  Thus the copy `iota(Gamma)` and
the elements `t,c` retain all the original compression data in `H`:
`t iota(Gamma)t^-1=iota(alpha(Gamma))` is a proper subgroup of
`iota(Gamma)`, and `c` centralizes `iota(Gamma)`.  This is exactly the
assertion of `infinite-order-central-mark-group`.
