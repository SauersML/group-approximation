---
rg: 2
id: stw10-qd-traces-admit-exact-finite-dimensional-core-models
kind: claim
title: Quasidiagonal traces admit models that are exact on any prescribed finite-dimensional core
distinct_from:
  stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses: that extracts a finitely generated weakly dense counterexample algebra; this puts every finite CAR stage exactly in the multiplicative domain of the matrix models and so normalizes the remaining obstruction.
  directed-unions-preserve-trace-approximations: that extends approximate models from members of a directed dense family; this perturbs an ambient model to be an exact bimodule map over a prescribed finite-dimensional subalgebra.
  stw08-exactness-coherifies-qd-models: that open claim asks for connecting maps between all successive finite-dimensional models and would imply an AF embedding; this exactifies one fixed domain subalgebra independently in each model, with no inter-model coherence.
  stw09-faithful-qd-trace-models-coherify: that open claim asks for compatible model traces across an inductive system; this preserves the original asymptotic trace coordinatewise and adds no connecting maps.
  stw99-problem-x1-amenable-traces-quasidiagonal: that asks whether Hilbert--Schmidt multiplicativity can always be upgraded to operator-norm multiplicativity; this theorem starts with a quasidiagonal trace and preserves operator-norm multiplicativity while freezing a finite-dimensional core.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `A` be a unital C-star algebra, let `tau` be a trace on `A`, and let
`E subset A` be a unital finite-dimensional C-star subalgebra.  Then `tau`
is quasidiagonal if and only if it has quasidiagonal u.c.p. matrix models
`psi_i:A -> M_(k_i)` for which

```text
E subset MD(psi_i)
```

at every index.  Equivalently, `psi_i|E` is a unital star homomorphism and

```text
psi_i(a x b)=psi_i(a) psi_i(x) psi_i(b)
```

for `a,b in E` and `x in A`.  The models can be chosen uniformly close on
the unit ball to any given quasidiagonal models after passage to a cofinal
tail.  Thus neither their operator-norm multiplicativity nor their trace
convergence is lost.

In particular, fix a weakly dense CAR algebra

```text
D=closure(union_n D_n) subset R,        D_n isomorphic to M_(2^n),
```

inside the hyperfinite `II_1` factor.  Problem X(2) is equivalent to the
following finite, core-exact condition: for every finite `X subset R`, every
`epsilon>0`, and every `n`, there is a u.c.p. map `psi:R -> M_k` such that

```text
D_n subset MD(psi),
|tr_k(psi(x))-tau_R(x)|<epsilon                    (x in X),
||psi(xy)-psi(x)psi(y)||<epsilon                   (x,y in X).
```

On `D_n` the normalized trace is then not merely approximate: it is exactly
`tau_R`, because every unital representation of the full matrix algebra
`D_n` has its unique normalized trace.  The statement for `R` is a
finite-set/net criterion; it makes no separability assumption on `R`.

If `A subset R` is separable and contains `D`, the restricted trace is
quasidiagonal exactly when there is a sequence of u.c.p. maps `psi_n` which
is asymptotically multiplicative in operator norm, converges to the
restricted trace, and has `D_n subset MD(psi_n)`.  Consequently, the
finitely generated weakly dense witness supplied by
`stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses` in a
negative solution cannot admit this CAR-exact sequence.  The unresolved
part is therefore confined to norm modeling of the finitely many operators
outside an exactly represented matrix stage.
