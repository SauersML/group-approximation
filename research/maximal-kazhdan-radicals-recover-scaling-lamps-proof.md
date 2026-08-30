---
rg: 2
id: maximal-kazhdan-radicals-recover-scaling-lamps-proof
kind: route
title: Fix a Bass-Serre vertex and then a Davis cube
target: maximal-kazhdan-radicals-recover-scaling-lamps
requires:
  - scaling-unimodular-racg-blocks
artifacts:
  - research/artifacts/composite-scaling-kazhdan-radical-reconstruction-2026-08-30.md
---

Write `P=P_m`, `B_1=B_(m,1)`, and

```text
A=V_m x <w>,   D=B_1 x <w>,   L=P semidirect B_1,
E_m=A *_D L.                                             (KR1)
```

Let `Sigma_m` be the Davis cube complex of
`W=W_(Gamma_m)=P/<w>`.  The group `L` acts cubically: `P` acts through
`W`, and `B_1` acts by graph automorphisms.

## Cube stabilizers and their finite radicals

For a clique `C` in `Gamma_m`, put

```text
Q_C=<w,c_x : x in C> <= P,
K_C=Stab_(B_1)(C),
S_C=Q_C semidirect K_C.                                  (KR2)
```

The standard `C`-cube has stabilizer `S_C` in `L`; every other cube
stabilizer is a conjugate of one of these.  The exact sequence
`1-><w>->P->W->1` and the elementary abelian special subgroup
`W_C` give

```text
|Q_C|=2^(|C|+1).                                         (KR3)
```

Because `Gamma_m` is finite, `K_C` has finite index in
`B_1~=Z^3 semidirect SL_3(Z)`, so it has property `(T)`.  Hence `S_C`
has property `(T)`, being a finite extension of `K_C`.

Every finite-index subgroup `K<=B_1` has trivial finite radical.  If
`F normal K` is finite and `f=(u,M) in F`, then `C_K(f)` has finite
index.  Its intersection with the translation lattice is a full lattice.
Commuting with that lattice forces `M=I`.  Thus `f` is a translation,
and its finite order forces `u=0`.  Applying this to `K_C`, any finite
normal subgroup of `S_C` maps trivially to `K_C`, while `Q_C` itself
is finite and normal.  Therefore

```text
FinRad(S_C)=Q_C.                                         (KR4)
```

## Every maximal Kazhdan radical lies in the lamp kernel

Let `H<=E_m` be maximal with property `(T)`.  Property `(T)` implies
Serre property `FA`, so `H` fixes a vertex of the tree in (KR1).  If it
fixes an `A`-vertex, its height image in `Z` is trivial.  Property-`(T)`
groups are finitely generated, and a finite subset of the direct-limit
height-zero kernel lies in one telescope level.  Hence `H` lies in an edge
stabilizer and therefore in an adjacent conjugate of `L`.  Thus in all
cases, after conjugation, `H<=L`.

Property `(T)` also implies property `FW`, so `H` fixes a point of
`Sigma_m` and stabilizes its minimal cube.  It is therefore contained in a
conjugate of some `S_C`.  Since that cube stabilizer itself has property
`(T)`, maximality gives equality.  By (KR4),

```text
FinRad(H) is a conjugate of Q_C and lies in N_m.          (KR5)
```

This proves `K_T(E_m)<=N_m`.

## Every site lamp occurs in a maximal Kazhdan radical

Choose an inclusion-maximal clique `C` containing a given vertex `x` of
`Gamma_m`.  We prove that `S_C` is maximal property `(T)`.

First, `S_C` fixes a unique point of `Sigma_m`, the center of the
standard `C`-cube.  Indeed the fixed-set formula for a spherical special
subgroup of a RACG is

```text
Fix(W_C)= {center of the C-cube} x Sigma_(link(C)).
```

Here `link(C)` is empty by maximality.  For completeness, this formula can
be read directly from minimal cubes: a fixed point would put `W_C` inside
a conjugate spherical subgroup `gW_Dg^(-1)`; maximal sphericality gives
equality, distinct RACG generators are not conjugate, and

```text
N_W(W_C)=W_C x W_(link(C))=W_C.
```

Thus the cube is the standard one, and its coordinate flips fix only its
center.  The group `K_C` fixes that center, so `S_C` has the same
singleton fixed set.

Second, `S_C` fixes a unique `L`-vertex in the Bass--Serre tree.  Every
edge adjacent to that vertex has stabilizer `lDl^(-1)` for some `l in L`.
The projection `L->B_1` gives the exact intersection

```text
P intersect lDl^(-1)=<w>.                               (KR6)
```

Indeed an element of the intersection has a representative `ldl^(-1)`
whose projection is trivial, so `d in D intersect P=<w>`; centrality of
`w` finishes.  Since `c_x` has nontrivial image in `W`, it is not in
`<w>`.  Therefore it belongs to no adjacent edge stabilizer, and its fixed
set in the Bass--Serre tree is exactly the chosen `L`-vertex.

Now suppose a property-`(T)` subgroup `J` contains `S_C`.  Property
`FA` gives a Bass--Serre fixed vertex, which must be the unique vertex
fixed by `S_C`; hence `J<=L`.  Property `FW` gives a Davis fixed point,
which must be the unique point fixed by `S_C`; hence `J` lies in its
point stabilizer, exactly `S_C`.  Thus `S_C` is maximal property `(T)`.
By (KR4), its finite radical contains `c_x`.

Every site in every block has such a maximal clique, and the site lamps
generate `N_m`.  Therefore `N_m<=K_T(E_m)`, which together with (KR5)
proves (KR).
