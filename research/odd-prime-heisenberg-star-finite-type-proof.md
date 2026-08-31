---
rg: 2
id: odd-prime-heisenberg-star-finite-type-proof
kind: route
title: Expand the Heisenberg characters and use amalgam normal form
target: odd-prime-heisenberg-star-saturates-finite-type-gates
requires:
  - finite-type-restriction-overlap-defect-formula
  - finite-type-subprojection-forces-large-root-intersection
  - central-type-sum-equality-is-intersection-readable
---

The degree-`ell` Heisenberg character with central character `zeta`
equals `ell zeta^a` on `J^a` and vanishes off the center. Therefore

```text
z_(E_0,pi_zeta)
 =(ell/ell^3) sum_a ell zeta^(-a) J^a
 =(1/ell) sum_a zeta^(-a) J^a
 =e_(Z,zeta)=q.                                        (HPS8)
```

For `A_i=<J,X_i>`, direct expansion gives

```text
p_(i,r)
 =(1/ell^2) sum_(a,b) zeta^(-a-rb) J^a X_i^b.          (HPS9)
```

The characters `alpha_(i,r)` are distinct, so their central idempotents
are orthogonal. Summing `(HPS9)` over `r` and using

```text
sum_(r in F_ell) zeta^(-rb)=ell delta_(b,0)
```

gives `sum_r p_(i,r)=q`. The coefficient of `X_i` in every
`p_(i,r)` is nonzero. Amalgam normal form has `X_i notin E_0`, proving
`(HPS4)`.

The same normal form gives

```text
A_i intersect E_0=Z,       A_1 intersect A_2=Z.        (HPS10)
```

Since `|E_0|=ell^3`, `|Z|=ell`, and `dim(pi_zeta)=ell`,
formula `(HPS5)` follows. It is the equality case of the large-root-
intersection theorem. The clean-face packing obstruction does not apply
inside a context: all `ell` atoms there use the same subgroup `A_i`, so
their pairwise atom-group intersection is `A_i`, not merely `Z`.

At an element `J^a X_i^b` with `b!=0`, all `ell` coefficients in
`(HPS9)` are nonzero and their sum is zero by the same root-of-unity
identity. This proves the asserted phase balance.

The restrictions of every `alpha_(i,r)` to `Z` are the same character
`zeta`. Applying the finite-type restriction-overlap formula to
`A_1 intersect A_2=Z` gives

```text
tau(p_(1,r)p_(2,s))
 =|Z|/(|A_1||A_2|)
 =ell/(ell^2 ell^2)
 =1/ell^3.                                             (HPS11)
```

Also `tau(p_(i,r))=1/ell^2`. Thus the two full families have defect

```text
ell/ell^2 + ell/ell^2
 -2 ell^2/ell^3=0,
```

recovering their already explicit equality to `q`.

It remains to prove the proper-marginal assertion. If `(HPS7)` holds,
then its common value belongs to

```text
C[A_1] intersect C[A_2]=C[A_1 intersect A_2]=C[Z],     (HPS12)
```

where the middle equality is coefficientwise in the group basis. For
`b!=0`, the coefficient of `J^a X_1^b` in the left side is

```text
zeta^(-a)/ell^2 sum_(r in S) zeta^(-rb).               (HPS13)
```

It must vanish for every nonzero `b`. Hence the Fourier transform of the
indicator of `S` on `F_ell` has no nontrivial frequency. The indicator
is constant, so `S` is empty or all of `F_ell`. The same argument applies
to `T`, and equality makes the two choices agree. This also gives a direct
proof of the relevant central-type intersection conclusion.

Finally, `Gamma` is the fundamental group of a finite tree of finite
groups. Bass--Serre theory supplies a free subgroup of finite index, so
`Gamma` is virtually free and therefore hyperlinear. The construction is
accordingly an exact boundary model only; it does not establish the
nonhyperlinear root.
