---
rg: 2
id: amenable-lamp-rounding-preserves-the-kt-named-return-wall
kind: claim
title: Amenable lamp rounding preserves the Kun--Thom cyclic-parity covariance and named return wall
artifacts:
  - research/bcjm-rounding-preserves-the-cyclic-parity-proof.md
distinct_from:
  amenable-hyperlinear-rounds-to-sofic: that rounds an amenable restriction to permutation matrices in the same dimension; this tracks the external actor covariance and canonical two-lamp displacement through that rounding.
  kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence: that supplies the exact cyclic-parity return correspondence; this proves that its named covariance and displacement survive amenable rounding of a hypothetical wreath microstate.
---

Use the pinned Kun--Thom cyclic-parity data of
`kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence`.
Let `A=direct_sum_(G/Gamma) C_2`, let `v,w` be its distinct nonzero
cyclic-parity lamp words, with `Gamma` fixing `v`, and let the named
return `h` satisfy `hvh^(-1)=w`. Suppose `theta_n` is a canonical-trace
hyperlinear approximation of the wreath group.

After passage to a subsequence, amenable rounding supplies permutation-valued
lamp approximations `beta_n` in the same dimensions with

```text
epsilon_n(a):=||beta_n(a)-theta_n(a)||_2 -> 0
```

for every fixed `a in A`. Keep the actor unitaries
`U_(g,n)=theta_n(g)` in the corresponding basis. If

```text
c_n(g,a)=||U_(g,n)theta_n(a)U_(g,n)^*
             -theta_n(gag^(-1))||_2,
```

then the exact comparison estimate is

```text
||U_(g,n)beta_n(a)U_(g,n)^*-beta_n(gag^(-1))||_2
 <=epsilon_n(a)+c_n(g,a)+epsilon_n(gag^(-1)) -> 0.        (ALR1)
```

Put `V_n=beta_n(v)`, `W_n=beta_n(w)`, and
`p_n=(I+V_n)/2`, `r_n=(I+W_n)/2`. These define projections in the
tracial matrix ultraproduct, and the canonical two-lamp character gives

```text
tr(p_n),tr(r_n) -> 1/2,
||p_n-r_n||_2 -> 1/sqrt(2),
||[p_n,U_(s,n)]||_2 -> 0                  for fixed s in Gamma,
||U_(h,n)p_nU_(h,n)^*-r_n||_2 -> 0,
||[p_n,U_(h,n)]||_2 -> 1/sqrt(2).                        (ALR2)
```

Repairing the fixed finite table `<v,w>=C_2^2` makes `p_n,r_n` literal
commuting projections without changing these limits. A simultaneous
diagonalization of that repaired table makes those two projections
diagonal, after conjugating the actor matrices by the same unitary.
Their ranks are asymptotically half the ambient dimension; exact half-rank
and simultaneous permutation form for every other lamp are not asserted.

The actor matrices have not been made genuine representations. Thus this
claim supplies no Laurent-actor exactification or collapse of the return
wall; it only proves that the wall and its named covariance survive the
available amenable rounding.

DERIVATION
bcjm-rounding-preserves-the-cyclic-parity-proof
