---
rg: 2
id: bounded-abelian-register-polynomial-spectral-loss-proof
kind: route
title: Pair joint labels inside torus boxes and swap a fixed fraction
target: bounded-abelian-register-has-polynomial-spectral-loss
requires: []
artifacts:
  - research/artifacts/bounded-abelian-register-spectral-loss-2026-08-21.md
---

Assume `k>=1` and put

```text
x=(N/2)^(1/k),                 M=floor(x).
```

The hypothesis `N>=2^(k+1)` gives `x>=2`, hence `M>=x/2`; also
`M^k<=N/2`.  Partition each circle into `M` half-open arcs of angular
length `2 pi/M`.  The resulting partition of the joint-label torus has at
most `M^k<=N/2` occupied boxes.  If their occupancies are `n_b`, pairing
labels arbitrarily inside each box produces

```text
P=sum_b floor(n_b/2)
 >=(1/2)sum_(n_b>0)(n_b-1)
 =(N-number of occupied boxes)/2
 >=N/4                                                   (BAR3)
```

disjoint pairs.

Let `S` interchange the two coordinate vectors in every selected pair and
fix all remaining coordinate vectors.  Then `S=S^*=S^(-1)`.  The
normalized Hilbert--Schmidt orthogonal projection onto `D_N` is the
diagonal conditional expectation `E_D`.  On each paired two-plane `S` has
zero diagonal, while on each unpaired coordinate it equals one.  Therefore
`S-E_D(S)` has exactly `2P` entries of modulus one, and

```text
dist_2(S,D_N)^2=||S-E_D(S)||_2^2=2P/N>=1/2.              (BAR4)
```

For a selected pair `(a,b)`, the two phases `z_i(a),z_i(b)` lie in one
arc, so their chordal distance is at most `2 pi/M`.  On its two-plane the
commutator `[S,U_i]` has exactly two nonzero entries, of respective values
`z_i(a)-z_i(b)` and its negative.  The pairs are disjoint, whence

```text
||[S,U_i]||_2^2
 =(2/N) sum_(a,b) |z_i(a)-z_i(b)|^2
 <=(2P/N)(2 pi/M)^2
 <=(2 pi/M)^2.                                          (BAR5)
```

Summing over `i` and using `M>=x/2` now gives

```text
sum_i ||[S,U_i]||_2^2
 <=4 pi^2 k/M^2
 <=16 pi^2 k (2/N)^(2/k),                               (BAR6)
```

which proves `(BAR1)--(BAR2)`.  In particular, an inequality
`dist_2(X,D_N)<=C(sum_i||[X,U_i]||_2^2)^(1/2)` would force
`C>=N^(1/k)/(4 pi sqrt(2k) 2^(1/k))` by `(BAR4)--(BAR6)`, so `C` is at
least of order `N^(1/k)` when `k` is fixed.

Finally, if two joint labels coincide, the transposition of their two
coordinate vectors commutes with every `U_i` but is not in `D_N`.  Thus the
common commutant strictly contains the intended position algebra and no
finite constant in such a commutator-to-`D_N` estimate can exist.  The
argument uses only commuting diagonal register words and makes no assertion
about a nonabelian register or a generator count growing with `N`.
