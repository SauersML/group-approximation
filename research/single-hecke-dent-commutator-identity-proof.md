---
rg: 2
id: single-hecke-dent-commutator-identity-proof
kind: route
title: Equal shell displacements plus the Hilbert-space norm identity
target: single-hecke-dent-is-the-expanding-commutator-defect
requires: []
---

Choose the left-coset representatives in the standard form
`w_i=u_i h` with `u_i in Lambda`.  Exact `Lambda`-centrality of `xi`
and unitarity of `Ad pi(u_i)` give

```text
||Ad pi(w_i)(xi)-xi||_2
 =||Ad pi(u_i)(Ad pi(h)(xi)-xi)||_2=d                  (SHD4)
```

for every `i`.  Polarizing `(SHD4)` gives

```text
Re <xi,Ad pi(w_i)(xi)>=||xi||_2^2-d^2/2.
```

Averaging and using `S=(I+T)/2` therefore yields

```text
Re <xi,S(xi)>=||xi||_2^2-d^2/4.                       (SHD5)
```

Now expand the square:

```text
||S(xi)-xi||_2^2
 =||S(xi)||_2^2+||xi||_2^2-2 Re <xi,S(xi)>
 =||S(xi)||_2^2-||xi||_2^2+d^2/2.
```

Rearrangement is `(SHD1)`.  The triangle inequality and `(SHD4)` give

```text
||S(xi)-xi||_2
 =(1/2)||T(xi)-xi||_2
 <=(1/(2L)) sum_i ||Ad pi(w_i)(xi)-xi||_2=d/2.         (SHD6)
```

Substituting `0<=||S(xi)-xi||_2^2<=d^2/4` into `(SHD1)` proves
`(SHD2)`.  For a unitary `k`, `||k||_2=1` and
`d=||[k,pi(h)]||_2`; hence `(SHD2)` proves `(SHD3)`.
