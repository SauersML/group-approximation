---
rg: 2
id: stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses
kind: claim
title: Problem X(2) reduces exactly to finitely generated weakly dense witnesses
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: this is an equivalent finitely generated counterexample normal form inside the factor, not a claim that the factor is quasidiagonal.
  directed-unions-preserve-trace-approximations: that theorem reduces a non-QD trace to some separable restriction; this produces a finitely generated algebra which remains weakly dense in the hyperfinite factor.
  stw07-local-qd-subalgebras-force-quasidiagonality: that is a norm-local theorem for separable ambient algebras; this handles the norm-nonseparable factor and adds the weakly dense CAR core.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

For the hyperfinite `II_1` factor `R`, the following are equivalent:

1. `R` is quasidiagonal as a C-star algebra;
2. every finitely generated unital C-star subalgebra of `R` is
   quasidiagonal;
3. every finitely generated unital C-star subalgebra of `R` which is weakly
   dense in `R` is quasidiagonal.

More precisely, fix a unital CAR subalgebra `D subset R` whose weak closure
is `R`.  If `R` is not quasidiagonal, there is a finitely generated unital
C-star algebra `A` such that

```text
D subset A subset R,             weak_closure(A)=R,
```

and, for `tau=tau_R|A`,

* `A` is stably finite but not quasidiagonal;
* `tau` is faithful and amenable but not quasidiagonal;
* the GNS von Neumann algebra of `(A,tau)` is `R`; and
* `A` cannot be both exact and UCT.

Thus a negative answer to Problem X(2) already has a finitely generated,
weakly dense witness carrying all the hyperfinite Hilbert--Schmidt
approximations.  The remaining failure is genuinely in operator norm.
