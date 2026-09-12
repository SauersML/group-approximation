---
rg: 2
id: low-rank-full-square-zero-doubled-line-proof
kind: route
title: Rank one is forced, so range and source are continuous isomorphic line bundles
target: low-rank-full-square-zero-forces-doubled-line
requires:
  - homogeneous-full-square-zero-is-nilpotent-section
---

**Part 1.**  Given `theta:L->L'` an isomorphism onto the second copy, put
`x=iota_(L') theta pi_L`, where `pi_L` projects onto the first summand.  Then
`x^2=0` because `pi_L` kills `L'`, and `x_t != 0` for every `t`.  By
`homogeneous-full-square-zero-is-nilpotent-section`, `x` is full.

**Part 2.**  Let `x` be full and square-zero, so `x_t != 0` for all `t`.
Square-zero gives `range(x_t) subset ker(x_t)`, hence
`2 rank(x_t) <= rank E <= 3`, and `rank(x_t)=1` at every point.

For a rank-one operator `T`, `TT*` is a rank-one positive operator with trace
`||T||_2^2>0`.  So

```text
P_t = x_t x_t* / tr(x_t x_t*),        Q_t = x_t* x_t / tr(x_t* x_t)
```

are continuous projection fields of rank one: `P` onto the range of `x`, `Q`
onto the orthogonal complement of `ker x`.  Since `range x subset ker x`,
`P_t Q_t=0`.  The map `x` restricts to a fibrewise isomorphism from the line
bundle `QE` onto the line bundle `PE`.  Therefore

```text
E = PE directSum QE directSum (1-P-Q)E ~= L directSum L directSum M,
```

with `L=PE` and `M=(1-P-Q)E` of rank `rank E-2`.

**The examples.**  Over `S^4` and `S^6` every line bundle is trivial.  For
`rank E=2`, `M=0` and the splitting makes `E` trivial, contradicting
`c_2 != 0`.  For `rank E=3`, `M` is a line bundle, so again `E` is trivial,
contradicting `c_3 != 0`.  The value `c_3(TS^6)=e(TS^6)=
chi(S^6)=2` is the Euler class of the underlying real bundle.
