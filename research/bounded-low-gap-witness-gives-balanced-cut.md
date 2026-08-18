---
rg: 2
id: bounded-low-gap-witness-gives-balanced-cut
kind: claim
title: A bounded low-adjoint-energy witness yields a balanced almost-invariant spectral cut
artifacts:
  - docs/TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md
---

Let `(M,tau)` be a finite matrix algebra with normalized trace, let
`u_1,...,u_m` be unitaries, and let `x=x^*` satisfy

```text
tau(x)=0,   ||x||_2=1,   ||x||_op <= C
```

for some `C>=1`.  Put

```text
E = sum_(s=1)^m ||[u_s,x]||_2^2.
```

Then there is a spectral projection `q=1_[t,infinity)(x)` such that

```text
1/(4 C^2) <= tau(q) <= 1-1/(4 C^2)
```

and

```text
sum_s ||[u_s,q]||_2^2 <= 2 C sqrt(m E).
```

The same statement holds in a nonzero corner after using its normalized
corner trace and Hilbert--Schmidt norm.

Thus every uniformly non-spiky failure of an adjoint Poincare inequality
produces a quantitatively balanced almost-invariant cut.  In the
`hs-expander-block-decomposition` programme, the genuinely new obstruction is
therefore the complementary one: low-energy witnesses whose normalized
`L^2` mass escapes every fixed operator-norm truncation, together with the
need to organize the resulting cuts into a nested compressor-compatible
partition without dimension-dependent error accumulation.
