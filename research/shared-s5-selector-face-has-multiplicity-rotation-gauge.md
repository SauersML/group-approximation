---
rg: 2
id: shared-s5-selector-face-has-multiplicity-rotation-gauge
kind: claim
title: A shared S5 selector face still has a finite-dimensional multiplicity-rotation gauge
invalidates:
  - shared-s5-selector-face-locally-implies-joint-s6-packet
distinct_from:
  a5-a4-overlap-has-two-seam-charges: that computes two representation-ring kernel directions for A5 restricted to A4; this gives an explicit unitary multiplicity rotation between two S6 extensions of one literally shared S5 action.
  finite-s6-selector-centralizer-pins-common-pivot-arm: that pins a group element once both candidate arms live in one representation of S6; this proves two different S6 extensions can each contain an arm centralizing the same selector subgroup.
  common-pivot-r2-r3-data-preserve-a6-label-swap: that is a permutation of the common labels inside one S6 representation; this gauge conjugates the entire second extension through the commutant of the shared S5 face.
---

Let `rho` be the natural permutation representation of

```text
S_6=Sym({i,p,j,k,l,q})
```

on `C^6`, and let

```text
H=Sym({p,j,k,l,q}) ~= S_5,             K=Sym({j,k,l,q}) ~= S_4. (SMG1)
```

The restriction `rho|_H` contains the trivial representation twice:

```text
C e_i  directSum  C v,       v=5^(-1/2)(e_p+e_j+e_k+e_l+e_q).   (SMG2)
```

Let `U` interchange the orthonormal vectors `e_i,v` and act identically on
their orthogonal complement.  Then `U` commutes with `rho(H)`.  Consequently

```text
rho_0(g)=rho(g),                  rho_1(g)=U rho(g) U^*           (SMG3)
```

are two representations of `S_6` which agree literally on `H`.  However,
for `x=(i p)`,

```text
rho_0(x) != rho_1(x).                                             (SMG4)
```

Both arm operators commute with the same selector algebra `rho(K)`, because
`x` centralizes `K` and `U` commutes with `K`.  Every relation contained in
the shared S5 face—including all relations among the complement selectors
and any nonshared Carmichael collision supported there—also agrees exactly
in the two extensions.

Thus a common selector subgroup, even enlarged to the whole common S5 face,
does not by itself put the two contextual arms inside one S6 representation.
The fixed-packet centralizer theorem becomes applicable only after an
additional relation kills this multiplicity rotation or directly supplies a
joint S6 exactification.  This countermodel concerns the proposed local
inference only; it is not a representation of the full simple Thompson group,
so a genuinely global Bleak--Quick relation may still eliminate the gauge.

