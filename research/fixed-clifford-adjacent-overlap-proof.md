---
rg: 2
id: fixed-clifford-adjacent-overlap-proof
kind: route
title: Pull the opposite newest layer back to the preceding upper-root character
target: fixed-clifford-sectors-have-zero-adjacent-opposite-overlap
requires:
  - fixed-clifford-projective-dyadic-tower
---

Write an abstract upper-Iwahori element as

```text
gamma=[[x,y],[z,w]],                 z even,
sigma(gamma)=[[x,2y],[z/2,w]].                         (FZP1)
```

For `X=X(A,B,C) in sl_2(F_2)`, choose `gamma_X in B` whose opposite
reduction modulo `2^(a+1)` is

```text
q_(a+1)(sigma(gamma_X))=1+2^a X in L_(a+1).             (FZP2)
```

Such lifts exist because the opposite Iwahori image contains the entire
principal congruence kernel.  Equations `(FZP1)--(FZP2)` give

```text
x,w=1+2^a A,
y=2^(a-1)B,
z=2^(a+1)C
```

at the relevant precisions.  Therefore the upper reduction one level lower
is

```text
q_a(gamma_X)=1+2^(a-1)X(0,B,0) in L_a.                 (FZP3)
```

If `pi` lies over `ell_0` at level `a`, `(FZP3)` acts on all of `pi` by

```text
(-1)^B.                                                 (FZP4)
```

If `rho` lies over `ell_0` at level `a+1`, `(FZP2)` acts on all of `rho`
by

```text
(-1)^(A+B+C).                                           (FZP5)
```

For a `B`-intertwiner `T`, comparison of `(FZP4)` and `(FZP5)` at
`X(1,0,0)` gives `T=-T`, hence `T=0`.  This proves `(FZO1)` without using
the projective multipliers or their choice of sections.

For the stronger orbit assertion, let `rho` be any irreducible at level
`a+1` with a nonzero intertwiner.  Restrict `rho` to the normal abelian group
`L_(a+1)`.  On the image of the intertwiner, `(FZP4)` says that its
`L_(a+1)` character is

```text
ell_B(A,B,C)=B=(0,1,0).                                 (FZP6)
```

Clifford theory says all newest-layer characters in an irreducible form one
`G_(a+1)`-orbit.  The explicit dual-orbit table in
`iwahori-dual-fusion-firewall-proof` places `(0,1,0)` in precisely the orbit
`O_B` of `(FZO2)`, of size three.  Orbit--stabilizer gives an index-three
inertia group, proving the final assertions.

