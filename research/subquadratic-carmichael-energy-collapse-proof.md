---
rg: 2
id: subquadratic-carmichael-energy-collapse-proof
kind: route
title: Pigeonhole the edge energy against the same-cell pair count of a compact conjugacy orbit
target: subquadratic-carmichael-energy-collapse
requires: []
---

## The two-matrix kernel

Let `A,C in U(d)` be unitary conjugates of `B`.  Two identities, both verified
by expanding:

```text
A - I = A(I-A^3) + (A^4-I),                                   (1)
(AC)^2 - A^4 = A(C-A)AC + A^3(C-A).                           (2)
```

Normalized Hilbert--Schmidt norm is unitarily invariant on both sides, so `(1)`
gives `||A-I||_2 <= ||A^3-I||_2 + ||A^4-I||_2` and `(2)` gives
`||(AC)^2-A^4||_2 <= 2||A-C||_2`.  Since `A=WBW^*` we have `A^3=WB^3W^*` and
therefore `||A^3-I||_2=||B^3-I||_2` and `||A-I||_2=||B-I||_2`.  Combining,

```text
||B-I||_2
  <= ||B^3-I||_2 + ||A^4-(AC)^2||_2 + ||(AC)^2-I||_2
  <= ||B^3-I||_2 + 2||A-C||_2 + ||(AC)^2-I||_2,               (CP)
```

which is the kernel.  No relator, word, or filling has been used.

## Producing a close pair by counting

Fix `r>0`.  The orbit `O(B)={WBW^*: W in U(d)}` is a continuous image of the
compact group `U(d)`, hence compact in normalized-HS distance, so it admits a
finite cover by `N=N(d,B,r)` open balls of radius `r`.  Assign each `X_i` a
cover ball containing it and let `m_1,...,m_N` be the resulting cell sizes.
By Cauchy--Schwarz, `sum_a m_a^2 >= M^2/N`, so the number of pairs sharing a
cell satisfies

```text
S_M = sum_a C(m_a,2) = (1/2)(sum_a m_a^2 - M) >= M^2/(2N) - M/2,   (3)
```

which is positive once `M>N`.  Write `e_(ij)=||(X_iX_j)^2-I||_2`.  The
same-cell pairs are a subset of all pairs, so their energies sum to at most
`E_M`, and hence some same-cell pair `(i,j)` has

```text
e_(ij)^2 <= E_M/S_M.                                          (4)
```

For that pair `X_i` and `X_j` lie in one ball of radius `r`, so
`||X_i-X_j||_2 <= 2r`.  Feeding this pair into `(CP)`:

```text
||B-I||_2 <= ||B^3-I||_2 + 4r + sqrt(E_M/S_M),                (5)
```

which is `(EFF)`.

## Passing to the limit

Fix `r`.  Then `N=N(d,B,r)` is a constant, so `(3)` gives
`S_M >= (1+o(1))M^2/(2N)` and the hypothesis `E_M=o(M^2)` gives
`E_M/S_M -> 0` along the assumed unbounded sequence of `M`.  Taking that limit
in `(5)` leaves `||B-I||_2 <= ||B^3-I||_2 + 4r`, and `r>0` was arbitrary, so
`(SCE)` follows.

The order of the two limits is the whole argument: `d` and hence `N` are fixed
before `M` grows, so the covering number is a constant, not a competitor.  The
packets for different `M` need not be nested and no relation between them is
used.

## Consistency checks

If `B=omega I` with `omega^3=1`, `omega!=1`, every conjugate is `B` itself and
`(X_iX_j)^2=B^4=B`, so `E_M=3M(M-1)/2` is not `o(M^2)` — consistent with `(SCE)`
failing for such a `B` (`sqrt3 <= 0` is false).  If `B^4=I`, then `B^3=B^*` and
`(SCE)` holds with equality, so the theorem is sharp.  If `B^2=I`, `(SCE)` is a
tautology.
