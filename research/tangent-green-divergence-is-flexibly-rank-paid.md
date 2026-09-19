---
rg: 2
id: tangent-green-divergence-is-flexibly-rank-paid
kind: claim
title: Divergent Iwahori Green modes are Hilbert-Schmidt negligible or flexibly rank-paid
distinct_from:
  proper-torus-reynolds-is-edge-refinement: that constructs an explicit logarithmically divergent infinity/cb Green family and refutes uniform cb Newton; this proves those modes cannot refute the normalized-HS gauge-optimized target.
  gauge-optimized-target-has-uniform-congruence-tangent-gap: that supplies the uniform L2 quotient gap; this combines it with spectral truncation and the mixed Taylor estimate to give a hard-tail/soft-coordinate dichotomy.
  bs14-thresholded-newton-needs-coordinate-basin: that thresholds residual values before any endpoint coordinate has been selected; this thresholds an already selected endpoint's normal coordinate and therefore does not solve global basin entry.
---

Let `rho` be any exact congruence endpoint, let `Z` be the tangent space to
the exact endpoint/core-gauge locus there, and let `C=DF_rho` on its
Hilbert-orthogonal normal space.  There are constants `sigma,L>0`, independent
of level, dimension, representation and multiplicity, such that

```text
||Ch||_2>=sigma||h||_2,                               (TGD1)
||F(rho exp(h))-Ch||_2<=L||h||_op||h||_2.             (TGD2)
```

Here the fixed finite tuple of anti-Hermitian coordinates is given the
maximum operator norm and Euclidean normalized-HS norm; changing these fixed
product conventions changes only universal constants.

The following consequences hold.

### 1. Infinity-Green enemies have vanishing HS mass

If `||h||_op<=1` and every output row of `Ch` has operator norm at most
`epsilon`, then, for the fixed number `k` of rows,

```text
||h||_2<=sqrt(k) epsilon/sigma.                        (TGD3)
```

In particular the logarithmically divergent scalar modes in
`proper-torus-reynolds-is-edge-refinement`, normalized to input infinity
norm one, converge to zero in normalized Hilbert--Schmidt norm.  Direct-sum
amplification does not change this conclusion.  Nor can many such modes be
packed on disjoint physical supports while keeping the output operator norm
small: their sum would contradict `(TGD1)`.

### 2. Every tangent has a rank-paid hard tail

For `theta>0`, let `p_j` be the spectral projection of the coordinate
absolute value `|h_j|` on `(theta,infinity)`.  Then

```text
sum_j tr(p_j)<=theta^(-2)||h||_2^2
      <=theta^(-2)sigma^(-2)||Ch||_2^2.               (TGD4)
```

The coordinatewise soft truncation
`h_j^soft=(1-p_j)h_j(1-p_j)` has operator norm at most `theta`.  Since
`p_j` is a spectral projection of `|h_j|`, it reduces `h_j`; hence
`exp(h_j)-exp(h_j^soft)` is supported on `p_j`.  Fixed-word telescoping
therefore changes every presentation word on rank at most a fixed
word-length multiple of `sum_j rank(p_j)`, at metric cost
`O(||Ch||_2^2/theta^2)`, without first taking a BS-invariant hull.  This is
a metric hard-tail ledger; the coordinatewise truncation need not preserve
the exact-core tangent constraints, so realizing it by one legal endpoint
boundary remains part of the active-dilation problem.

### 3. The soft coordinate is nonlinearly coercive

If a normal coordinate has `||h||_op<=theta<=sigma/(2L)`, then
`(TGD1)--(TGD2)` give

```text
||F(rho exp(h))||_2 >= (sigma/2)||h||_2.              (TGD5)
```

Thus the tangent quotient gap integrates with dimension-independent
constants on the operator-soft complement.  There is no soft-delocalized
countersequence inside a selected congruence coordinate tube.

## Proof

Equation `(TGD1)` is
`gauge-optimized-target-has-uniform-congruence-tangent-gap`.  Each output
row with operator norm at most `epsilon` has normalized-HS norm at most
`epsilon`, so `(TGD3)` follows immediately.  Markov's spectral inequality
in each fixed coordinate gives the first inequality in `(TGD4)` (absorbing
the fixed coordinate count into the norm convention), and `(TGD1)` gives
the second.  A word containing one changed coordinate `q` times changes on
at most `q rank(p_j)` translated dimensions and by Frobenius norm at most
`2q sqrt(rank(p_j))`; summing the fixed coordinate list is the same
finite-word support ledger as
`low-rank-reflection-surgery-preserves-the-exact-bs-core`.  Finally `(TGD2)`
is the mixed Taylor estimate from
`normalized-hs-taylor-remainder-is-not-dimension-free`, and subtraction
from `(TGD1)` proves `(TGD5)`.

## Exact remaining scope

This closes the proposed **soft-delocalized** attack and explains why the
divergent cb Green family kills strict operator-norm Newton but not flexible
normalized-HS repair.  It does not prove `(GOS1)`: `(TGD4)--(TGD5)` begin
with a chosen exact endpoint `rho` and its normal coordinate `h`.  Producing
that coordinate, or an energy-paid active boundary carrying its hard part,
from the raw exact BS core and approximate `X` is precisely the relative
ultraproduct liftability/atom-authentication gate.  A genuine counterexample
must therefore remain outside every selected endpoint tube (or change
torsion multiplicity globally); it cannot be a diffuse small-amplitude
Green mode around congruence zeros.
