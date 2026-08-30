---
rg: 2
id: stw22-damped-orthogonalizers-across-rank-one-blocks-proof
kind: route
title: Quotient to the rank-one skeleton and damp discontinuous orthogonalizers in its kernel
target: stw22-height-three-scattered-trace-continuity
requires:
  - stw22-rank-one-scattered-fibre-gaps-are-tracefree
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-height-three-two-level-damping-audit-2026-08-30.md
---

Write `R=pi_tau(U)''`.  As in
`stw22-cofinite-corona-calculation-at-rank-one-points-proof`, `M` is the
algebra of bounded `2`-norm-continuous maps from `X` to `R`.

Fix a rank-two point `x`.  Compact metrizable scattered spaces are
zero-dimensional.  Since `x` is isolated in `X^(2)`, choose a clopen
neighbourhood `V` with `V intersect X^(2)={x}`.  A decreasing clopen local
base `(W_n)` at `x`, with intersection `{x}`, gives compact clopen annuli
`W_n\W_(n+1)`.  Each annulus meets the discrete space
`X^(1)\X^(2)` in a finite set.  Splitting the annuli into finitely many
clopen pieces and re-enumerating gives

```text
V\{x}=disjoint-union_(n>=1) V_n,                         (H3.1)
```

where every `V_n` is compact and clopen in `V\{x}`, every `V_n` has at
most one nonisolated point, and every neighbourhood of `x` contains all but
finitely many `V_n`.  Choose `z_n in V_n`, taking the nonisolated point when
one exists.

Localizing by `1_V`, the gap `I_x=K_x/J_x` has the concrete description

```text
I_x ~= { (a_n): a_n in M(V_n),
                   sup_n ||a_n||<infinity,
                   sup_(t in V_n)||a_n(t)||_2 -> 0 }
       / { (a_n):||a_n|| -> 0 }.                         (H3.2)
```

Evaluation at the distinguished points defines a surjective star
homomorphism

```text
q:I_x -> G,
q([(a_n)])=[(a_n(z_n))],                                (H3.3)
```

where

```text
G={ (r_n) in product_n R:||r_n||_2 -> 0 }
    / { (r_n):||r_n|| -> 0 }.
```

Surjectivity follows by using the constant section with value `r_n` on
`V_n`.  The rank-one theorem says that `G` has no nonzero bounded positive
trace.

It remains to prove the same for `H=ker(q)`.  Let `sigma` be a bounded
positive trace on `H`, and let `a` be a positive contraction in `H`.
Choose positive representatives `a_n`.  Since `q(a)=0`,
`delta_n=||a_n(z_n)||` tends to zero.  Replacing `a_n` by

```text
b_n=(a_n-delta_n)_+
```

does not change its class in `(H3.2)` and gives `b_n(z_n)=0`.

Fix `epsilon>0` and put `c_n=(b_n-epsilon)_+`.  Fix an arbitrary integer
`m`.  Uniform `2`-norm convergence in `(H3.2)` and Chebyshev imply that,
after discarding finitely many blocks,

```text
m tau(1_(epsilon,infinity)(b_n(t))) <= 1
                                      (t in V_n).        (H3.4)
```

For every isolated `t in V_n\{z_n}`, choose unitaries
`u_(1,n,t),...,u_(m,n,t) in R` which move the support of `c_n(t)` onto
pairwise orthogonal projections.  No continuity of these unitaries is
required.  Define

```text
y_j(t)=u_(j,n,t)c_n(t)^(1/2),
y_j(z_n)=0,
y_j(x)=0.                                                (H3.5)
```

These are elements of `H`.  Indeed, at an inner limit point `z_n`,

```text
||y_j(t)||_2^2=tau(c_n(t)) <= tau(b_n(t)) <= ||b_n(t)||_2 -> 0,
```

because `b_n(z_n)=0`.  At the outer limit point `x`, the same estimate and
the uniform `2`-norm nullity in `(H3.2)` give

```text
sup_(t in V_n)||y_j(t)||_2 -> 0.
```

Thus multiplication by `c_n^(1/2)` damps every discontinuity in the
pointwise choices of `u_(j,n,t)`.

In `H` one has

```text
y_j^* y_j=c,
```

and the positive contractions `y_j y_j^*` are pairwise orthogonal.  The
finitely many discarded blocks vanish in `(H3.2)`.  Traciality therefore
gives

```text
m sigma(c)=sigma(sum_(j=1)^m y_j y_j^*) <= ||sigma||.
```

Letting `m` grow gives `sigma(c)=0`; then
`||b-c||<=epsilon` and `epsilon -> 0` give `sigma(a)=0`.  Hence `H` is
bounded-trace-free.

Finally, any bounded trace on `I_x` vanishes on `H`, factors through `G`,
and vanishes there, so `I_x` is bounded-trace-free.  Rank-zero and rank-one
points were handled by
`stw22-rank-one-scattered-fibre-gaps-are-tracefree`.  The abstract fibre-gap
criterion now gives the asserted description and uniform `2`-norm
continuity of every trace on `M`.
