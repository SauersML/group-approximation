---
rg: 2
id: thompson-v-ce-one-word-trace-face-proof
kind: route
title: Cut the regular central summand from any nontrivial Thompson-V character
target: thompson-v-ce-one-word-trace-face-is-binary
requires:
  - thompson-v-character-simplex
  - thompson-v-not-lef
---

By `thompson-v-character-simplex`, every trace is

```text
tau_t=t tau_reg+(1-t)tau_triv,       0<=t<=1.
```

For `w!=1`, direct expansion gives

```text
tau_t(q_w)=2-tau_t(w)-tau_t(w^*)=2t.                  (1)
```

For `0<t<1`, the GNS von Neumann algebra of `tau_t` is the central direct sum
of `L(V)` and `C`, with trace weights `t` and `1-t`; for `t=1` it is `L(V)`.
If any `tau_t` with `t>0` is Connes embeddable, its nonzero regular central
corner `L(V)` is Connes embeddable, so `V` is hyperlinear. Conversely, if
`V` is hyperlinear then `L(V)` is Connes embeddable and every direct-sum
mixture `tau_t` is Connes embeddable. Equation `(1)` therefore makes the CE
value set either `{0}` or the entire interval `[0,2]`.

Every finite-dimensional unitary representation of `V` is trivial: simplicity
makes a nontrivial one faithful, while Mal'cev residual finiteness of its
finitely generated linear image would make the infinite simple group `V`
residually finite, contradicting `thompson-v-not-lef`. Hence the exact
finite-dimensional support value of `q_w` is `0`.
