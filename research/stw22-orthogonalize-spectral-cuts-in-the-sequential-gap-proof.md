---
rg: 2
id: stw22-orthogonalize-spectral-cuts-in-the-sequential-gap-proof
kind: route
title: Compute the convergent-sequence completion and replicate every small spectral cut
target: stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-convergent-sequence-gap-audit-2026-08-30.md
---

The extreme traces of `C(X) tensor U` are the point evaluations followed by
the unique trace of `U`, so its uniform `2`-norm is the supremum of the
fibre `2`-norms.  Kaplansky density in `R` gives the displayed description
of `M`.  Indeed, one implication follows from uniform `2`-norm convergence.
Conversely, given a bounded sequence with
`||a_n-a_infinity||_2 -> 0`, approximate `a_infinity` and finitely many
exceptional `a_n` in `U`, with the same norm bound, and use the
`a_infinity` approximant on the tail.  This gives a norm-continuous
`U`-valued function on `X` and arbitrarily small uniform `2`-norm error.

Evaluation at `infinity` now gives the formula for `K_infinity`.  Products
by scalar functions vanishing at `infinity` have coordinate norms tending
to zero.  Conversely, truncation shows that every element of `K_infinity`
whose coordinate norms tend to zero belongs to `J_infinity`.  This proves
`(CSG)`.

Choose projections `p_n in R` with `tau(p_n)=1/n`.  Then
`p=(0,p_1,p_2,...)` belongs to `K_infinity`, while its coordinate norms are
one, so its class in `(CSG)` is nonzero.

It remains to exclude bounded traces.  More generally, let `(N_n,tau_n)`
be any sequence of finite factors and set

```text
D=product_n N_n / direct-sum_n^c0 N_n,
I={[(a_n)] in D: ||a_n||_(2,tau_n) -> 0}.
```

Let `sigma` be a bounded positive trace on `I`, and let
`a=[(a_n)]` be a positive contraction in `I`.  Fix `epsilon>0` and put

```text
b_n=(a_n-epsilon)_+,
p_n=1_(epsilon,infinity)(a_n).
```

Chebyshev's inequality gives

```text
tau_n(p_n) <= epsilon^(-2)||a_n||_2^2 -> 0.              (1)
```

Fix an arbitrary integer `m`.  After deleting finitely many coordinates,
`m tau_n(p_n)<=1`.  In the finite factor `N_n`, there are therefore `m`
pairwise orthogonal projections unitarily equivalent to `p_n`.  Coordinate
unitaries produce `m` pairwise orthogonal conjugates
`b^(1),...,b^(m)` of `b=[(b_n)]` in `I`; finitely many discarded
coordinates disappear in the `c_0` quotient.

A bounded trace on an ideal is invariant under unitaries of the containing
algebra: this follows by extending it through an approximate identity, or
equivalently by its canonical tracial extension to the multiplier algebra.
Hence

```text
m sigma(b)=sigma(sum_(j=1)^m b^(j)) <= ||sigma||.
```

Since `m` is arbitrary, `sigma(b)=0`.  Finally
`||a-b||<=epsilon`, so `sigma(a)<=epsilon||sigma||`; letting `epsilon`
tend to zero gives `sigma(a)=0`.  Thus `sigma=0`, and `(CSG)` is
bounded-trace-free.

For completeness, `(CSG)` is not sigma-unital.  Suppose that positive
contractions `e^(1),e^(2),...` formed a countable approximate identity and
lift them to positive coordinate contractions `e^(j)_n` with
`||e^(j)_n||_2 -> 0`.  Choose increasing coordinates `n_k` so that

```text
tau(sum_(j=1)^k (e^(j)_(n_k))^2) < k^(-4).
```

For

```text
r_k=1_[0,k^(-2)](sum_(j=1)^k (e^(j)_(n_k))^2),
```

Chebyshev gives `tau(1-r_k)<k^(-2)`.  Choose a projection
`p_(n_k)<=r_k` of trace `1/k`, put `p_n=0` at all other coordinates, and
discard the harmless first coordinate.  Then `p=[(p_n)]` is a nonzero
projection in `(CSG)`, while for every fixed `j`,

```text
||e^(j)_(n_k) p_(n_k)|| <= 1/k                 (k>=j).
```

Thus `e^(j)p=0` in `(CSG)` for every `j`, contradicting
`e^(j)p -> p`.  This proves non-sigma-unitality.  It does not by itself
settle stability, since stability is defined without a sigma-unitality
hypothesis.
