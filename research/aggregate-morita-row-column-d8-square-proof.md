---
rg: 2
id: aggregate-morita-row-column-d8-square-proof
kind: route
title: Factor the literal Morita aggregate commutator into two dihedral packets
target: aggregate-morita-row-column-fold-has-d8-square-model
requires:
  - leavitt-range-sum-fold-is-first-object-erasing-row
  - finite-positive-root-fragments-have-marked-regular-models
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

The Steinberg incidence relations give

```text
[S_0,S_1]=[T_0,T_1]=[S_0,T_1]=[S_1,T_0]=1.
```

For each matching intermediate coordinate, the ordinary three-root formula
gives

```text
[S_i,T_i]=x_78(s_it_i)=C_i.
```

The output root `(7,8)` shares the initial index with each `S_i` and the
terminal index with each `T_i`, so both `C_i` commute with all four input
roots.  The elementary commutator identities therefore yield

```text
[S_0S_1,T_0T_1]=[S_0,T_0][S_1,T_1]=C_0C_1.
```

Root addition followed by `s_0t_0+s_1t_1=1` proves `(AMF3)`.

For the finite model, in either dihedral factor the two generating
reflections satisfy `[a,b]=(ab)^2=c`, where `c` is the central half-turn.
Equations `(AMF4)` now give

```text
[S_i,T_i]=C_i,
[S_0S_1,T_0T_1]=([a,b],[a,b])=(c,c)=C_0C_1=N,
```

and all crossed commutators vanish because the two branches occupy separate
direct factors.  Since `c` is nonidentity, so is `C_1`.  Its left regular
action consists of two-cycles and has a nonzero negative spectral
projection.  The Atomic Leavitt Gap then gives the stated scoped failure of
any vanishing-modulus three-row conclusion.
