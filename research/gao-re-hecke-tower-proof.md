---
rg: 2
id: gao-re-hecke-tower-proof
kind: route
title: Apply the commuting square to Fourier double-coset orthogonality
target: gao-re-witness-carries-orthogonal-arithmetic-hecke-tower
requires:
  - sl3-re-over-lattice-iff-re-over-scalars
---

The commuting square gives, for every `g in A`,

```text
E_D(U_g)=pi(E_N(u_g))
        = U_g,   g in C,
          0,     g notin C.                              (RHT1)
```

For `c_1,c_2,d_1,d_2 in C`, the inner product between
`U_(c_1 a c_2)` and `U_(d_1 b d_2)` is the canonical group trace of

```text
(c_1 a c_2)^(-1)(d_1 b d_2).
```

It vanishes unless the two group elements agree, which can occur only when
`CaC=CbC`.  Linear extension and closure prove orthogonality of `K_a,K_b`.

Because `pi` is trace preserving, its restriction is an isometry of the
source `N-N` correspondence `closure(Nu_aN)` onto `K_a`; hence the Jones
dimensions and the finite-index description are unchanged.  The
commensurability calculation in
`sl3-lattice-inclusion-is-quasiregular-not-mixing` makes these dimensions
finite.

Finally the double cosets `C h^n C`, `n>=0`, are distinct (their Cartan
translation lengths in the Bruhat--Tits building are distinct), while
`h^n notin C` for `n!=0`.  Equation `(RHT1)` gives the relative Haar
statement and the orthogonal tower.

There is also an elementary quantitative index bound.  Conjugation by
`h^n=diag(2^n,1,2^(-n))` sends the `(3,1)` entry of an integral matrix to
`2^(-2n)` times that entry.  Hence membership in

```text
C cap h^(-n) C h^n
```

forces the `(3,1)` entry to be divisible by `2^(2n)`.  The lower root
elements `I+rE_(31)`, for `0<=r<2^(2n)`, consequently represent distinct
cosets, proving index at least `2^(2n)` and unbounded Jones dimension.

Nothing here chooses exact representatives of these correspondences in
each coordinate `A_k`.  Gao's definition only places them in the metric
ultraproduct.  Promoting this tower to simultaneous coordinatewise
hyperfinite bimodule data is therefore the remaining, nonformal gate.  This
proves the claim without smuggling that gate into its conclusion.
