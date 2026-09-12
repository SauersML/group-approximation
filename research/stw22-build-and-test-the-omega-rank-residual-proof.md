---
rg: 2
id: stw22-build-and-test-the-omega-rank-residual-proof
kind: route
title: Close the finite derivative kernels and test the surviving cofinal projection packets
target: stw22-omega-power-rank-escape-core
requires:
  - stw22-derived-set-gap-trace-reduction
artifacts:
  - research/artifacts/stw22-omega-power-rank-escape-audit-2026-08-30.md
---

For each `n`, restriction `I_n -> I_(n+1)` is surjective and has
bounded-trace-free kernel by
`stw22-derived-set-gap-trace-reduction`.  The maps `r_n` are therefore
surjective.  Moreover

```text
0 -> L_n -> L_(n+1)
  -> ker(I_n -> I_(n+1)) -> 0                           (ORE1)
```

is exact.  Bounded-trace-freeness is preserved by extensions: a bounded
positive trace vanishes on the ideal and then factors to the quotient.
Induction proves that every `L_n` is bounded-trace-free.  A bounded trace on
`L_(<omega)` vanishes on every `L_n`, hence on their dense union, so it is
zero.

Now let `sigma` be a bounded positive trace on `I_0`.  Its restriction to
the ideal `L_(<omega)` is zero, so it factors uniquely through `Q_omega`.
Conversely every bounded trace on `Q_omega` pulls back to one on `I_0`.
This proves the trace-cone assertion and the exact equivalence.

We next prove that the residual quotient is genuinely nonzero.  Put

```text
alpha_k=omega^k,
U_k=(omega^(k-1),omega^k]             (k>=1).
```

The `U_k` are pairwise disjoint clopen subsets of `X\{x}` and converge to
`x`; the point `alpha_k` has Cantor--Bendixson rank `k`.  Choose nonzero
projections `p_k in R` with `tau(p_k)->0`, and define the clopen-constant
projection section `p` displayed in the claim.  It is `2`-norm continuous
at `x`, belongs to `K_x(X)`, and is not in `J_x(X)`.

If `h in L_n`, then restriction of `h` to `X_n` belongs to `J_x(X_n)`.
Since `alpha_k in X_n` for every `k>=n`,

```text
||h(alpha_k)|| -> 0,
||p(alpha_k)-h(alpha_k)|| -> 1.
```

The quotient norm modulo `J_x(X)` is the norm limsup as `t -> x`, so the
distance from `p` to `L_n` is one.  This holds for every `n`, and therefore
the distance from `p` to `L_(<omega)` is one.  Its image in `Q_omega` is a
nonzero projection.

Finally let `theta` be a bounded positive trace on `Q_omega`, and fix `m`.
After discarding finitely many `U_k`, arrange `m tau(p_k)<=1`.  In each
factor choose `m` equivalent pairwise orthogonal copies of `p_k`.  Because
the sections are constant on each clopen `U_k` and their `2`-norms tend to
zero, the implementing partial-isometry sections belong to `I_0` and pass
to `Q_omega`.  Thus the image of `p` has `m` orthogonal Murray--von Neumann
equivalent copies, and

```text
m theta(p) <= ||theta||.
```

Arbitrariness of `m` gives `theta(p)=0`.  The same proof applies to every
cofinal clopen packet of shrinking projections described in the claim.
