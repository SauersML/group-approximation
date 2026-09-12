---
rg: 2
id: full-square-zero-forces-discriminant-power-vanishing
kind: claim
title: A full square-zero section of End E kills a power of the Chern discriminant of E
distinct_from:
  low-rank-full-square-zero-forces-doubled-line: that computes the exact splitting condition in ranks two and three, where the nilpotent has constant rank; this handles every rank, where the rank may jump, and records the cohomological consequence.
  full-square-zero-gap-forces-dd-torsion: that extracts projections from one uniform spectral gap in a continuous-trace algebra; this uses a finite cover by gap sets, one for each possible rank.
---

**ESTABLISHED.**  Let `E` be a complex vector bundle of rank `N>=2` over a
compact Hausdorff space `X`, put `s=floor(N/2)`, and let

```text
Delta(E) in H^(2N(N-1))(X; Z)
```

be the discriminant of the Chern polynomial: the integral polynomial in
`c_1(E),...,c_N(E)` which, in terms of formal Chern roots, is
`prod_(a<b) (t_a - t_b)^2`.  (Singular cohomology throughout; Chern classes
are pulled back along a classifying map.)

1. **Gap cover.**  If `Gamma(X, End E)` contains a full square-zero element,
   then `X` is the union of `s` open sets `W_1,...,W_s` such that on each `W_r`

   ```text
   E|_(W_r) ~= K_r directSum K_r directSum L_r,       rank K_r = r.
   ```

2. **Discriminant obstruction.**  Consequently `Delta(E)^s=0` in
   `H^(2sN(N-1))(X; Z)`.

**Examples in every rank.**  Let `X=(CP^M)^N` with `M>=2s(N-1)` and let `E`
be the sum of the `N` pulled-back tautological line bundles, with roots
`t_1,...,t_N`.  Then `Delta(E)^s=prod_(a<b) (t_a-t_b)^(2s)` is a nonzero
polynomial in which every variable has degree at most `2s(N-1)<=M`, so it is
nonzero in `Q[t_1,...,t_N]/(t_a^(M+1))`.  Hence `Gamma(X, End E)` contains no
full square-zero element, in every rank `N>=2`.
