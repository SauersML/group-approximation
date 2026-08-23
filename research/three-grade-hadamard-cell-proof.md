---
rg: 2
id: three-grade-hadamard-cell-proof
kind: route
title: Put a Hadamard reflection on one measurable matched pair
target: three-actor-grades-support-an-exact-hadamard-cell
requires:
  - cyclic-aperiodicity-collapses-two-actor-grade-unitaries
---

The compact Haar space `K` is nonatomic. Indeed, if `K` were finite then
`A` would be finite, while some positive power of the automorphism induced
by `t` would be the identity on `A`, contradicting `(CAT1)` because `A` is
nonzero. Also every positive power of `t` acts ergodically by `(CAT1)`, so
the transformation induced by `t` is aperiodic. The height-two Rokhlin lemma
therefore gives a positive-measure set `E` for which `E` and `tE` are
disjoint; shrinking `E` if necessary makes their complement have positive
measure. With `p=1_E` and the convention

```text
U_t f U_t^*=alpha_t(f),
```

this proves `(THC1)`.

Since `q=alpha_t(p)`, the operator `v=qU_t` satisfies

```text
v^*v=p,       vv^*=q,       v^2=(v^*)^2=0.            (THP1)
```

Write `d=p-q` and `x=v+v^*`. Orthogonality of `p,q,r` and `(THP1)` give

```text
d^2=x^2=p+q,       dx+xd=0,
rx=xr=rd=dr=0.                                            (THP2)
```

Hence `W=W^*` and

```text
W^2=r+(d+x)^2/2=r+p+q=1.
```

The identity `v^*=pU_(t^(-1))` gives `(THC3)`. Its three coefficients are
nonzero because `p,q,r` have positive trace. Finally, direct multiplication
using `(THP1)` gives `(THC4)`. The Fourier expansion in a crossed product is
unique, so the nonzero `t` and `t^(-1)` coefficients in `(THC4)` prove that
`WpW^*` is not in the base. Every finite partition cocycle normalizes the
base, proving the last assertion.

The relations in `(THP1)` also give

```text
e_ij e_kl=delta_(j,k)e_il,       e_ij^*=e_ji.
```

This proves `(THC5)`, and the usual matrix-unit calculation proves `(THC6)`.
