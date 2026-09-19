---
rg: 2
id: fournier-facio-hyperfinite-exhaustion-calibration-proof
kind: route
title: Calibrate hyperfinite support exhaustion on a singular bilateral-shift model
target: fournier-facio-hyperfinite-support-exhaustion-misses-cutoff
requires:
  - fournier-facio-generator-support-components-escape-cutoffs
---

Let `mu` be a translation-invariant finitely additive probability measure on
`Z` which vanishes on finite sets, and define the diagonal state

```text
phi_mu(A)=integral_Z <A delta_k,delta_k> dmu(k).       (HFSP1)
```

Let `T delta_k=delta_(k+1)` and `pi(j)=T^j`.  Translation invariance makes
`phi_mu` invariant under `Ad(T)`, so `pi` is an exact amenable
representation.  For every nonzero `j`,

```text
<T^j delta_k,delta_k>=0                               (HFSP2)
```

at every `k`.  Thus its charged character is the regular character and its
essential-freeness row is exact.  A translation-invariant free mean vanishes
on `c_0(Z)`; the diagonal of every compact operator belongs to `c_0(Z)`.
Hence `phi_mu` vanishes on the compact operators and is singular.  The
matrix-support graph of `T` is the integer line, which has one infinite
connected component carrying full charge.

It remains to construct a nested finite exhaustion without creating a null
boundary.  Choose a `2`-adic integer `a` which is not the image of an ordinary
integer—for example the `2`-adic integer with alternating binary digits—and
let `r_n in {0,...,2^n-1}` be its residue modulo `2^n`.  Put

```text
D_n=r_n+2^n Z.                                        (HFSP3)
```

The congruence compatibility gives `D_(n+1) subset D_n`.  Let `R_n` be the
equivalence relation whose classes are the integer intervals between
successive points of `D_n`.  Every class has size `2^n`, and the relations
are increasing.

They exhaust the full relation.  Indeed, if fixed integers `x<y` were
separated at every level, the nested finite sets

```text
D_n intersect [x+1,y]
```

would all be nonempty and hence would have a common integer `d`.  Then
`d=r_n mod 2^n` for every `n`, so `d=a` in `Z_2`, contrary to the choice of
`a`.  Therefore every pair of integers lies in one `R_n`-class for all large
enough `n`, proving `(HFSC2)`.

Define `T_n` to shift forward inside each `R_n`-interval and cyclically send
its final point back to its first point.  The vectors `T delta_k` and
`T_n delta_k` agree except at the final points of the intervals, namely

```text
E_n=D_n-1.
```

Translation invariance and finite additivity give every residue class modulo
`2^n` charge `2^(-n)`.  At an exceptional point the two image vectors are
orthogonal, so their squared distance is `2`.  Hence

```text
phi_mu((T-T_n)^*(T-T_n))=2 mu(E_n)=2^(1-n).           (HFSP4)
```

This is positive for every fixed `n`, despite converging to zero.  Thus the
finite `R_n`-classes never form support components for a comparison unitary
which is null-close to `T`.  The actual comparison support remains the one
infinite component, exactly the surviving case of the cutoff theorem.

The example satisfies amenability, singularity, exact multiplicativity,
regular character, and combinatorial hyperfiniteness simultaneously.
Therefore none of those soft data can turn an asymptotically vanishing
boundary into the exact charged-null boundary required by the cutoff fence.
