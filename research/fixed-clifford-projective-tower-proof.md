---
rg: 2
id: fixed-clifford-projective-tower-proof
kind: route
title: Apply invariant-character Clifford theory and test the anisotropic upper-root class
target: fixed-clifford-projective-dyadic-tower
requires:
  - iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree
  - pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss
---

The newest kernel consists of matrices

```text
1+2^(a-1)X(A,B,C),       A,B,C in F_2,
```

and multiplication is addition of triples. Conjugation factors through
`G_1`. From `iwahori-dual-fusion-firewall-proof`, an upper transvection and
the Weyl element act on dual coordinates by

```text
u:(alpha,beta,gamma)->(alpha,beta,alpha+beta+gamma),
w:(alpha,beta,gamma)->(alpha,gamma,beta).
```

The vector `(1,1,1)` is fixed by both generators, proving invariance of
`ell_0` and hence that its inertia group is `G_a`.

Choose a section `s:G_(a-1)->G_a`. The failure of `s` to be multiplicative
lies in `L_a`; applying `chi_a` gives a scalar two-cocycle `omega_a`.
Standard invariant-character Clifford theory identifies representations of
`G_a` on which `L_a` acts by `chi_a` with projective representations of
`G_(a-1)` having the inverse multiplier (changing `omega_a` to its inverse
does not affect the claim). This proves `(FCT3)` without assuming that
`chi_a` extends linearly to `G_a`.

For `(FCT4)`, use the explicit kernel conditions

```text
N_a: x,w=1 mod 2^a, y,z=0 mod 2^a,
M_a: x,w=1 mod 2^a, y=0 mod 2^(a-1), z=0 mod 2^(a+1).
```

The upper unipotent with entry `2^(a-1)` lies in `M_a` and represents
`X(0,1,0)` in `L_a`. Since `ell_0(0,1,0)=1`, it acts by `-1` throughout
every representation over `chi_a`; hence `M_a` is not killed. On the other
hand `(DRI2)` gives `M_(a+1) subset N_a`, and `N_a` is killed because the
representation factors through `G_a`. The upper-conductor assertion follows
similarly from nontriviality on `L_a=N_(a-1)/N_a`.
