---
rg: 2
id: small-trace-rank-one-quarantine-proof
kind: route
title: Shatter a negligible corner into one-dimensional atoms
target: small-trace-rank-one-quarantine
requires: []
---

For a unitary `u` and a projection `q`, expand the normalized
Hilbert--Schmidt commutator norm:

```text
||[u,q]||_2^2
 = tau((u q-q u)^*(u q-q u))
 = 2 tau(q) - 2 tau(q u^* q u q).
```

The last term is

```text
tau(q u^* q u q) = ||q u q||_2^2 >= 0,
```

where cyclicity of the trace inserts the final `q`.  Hence

```text
||[u,q]||_2^2 <= 2 tau(q).
```

Apply this separately to the pairwise orthogonal rank-one atoms of `e` and
sum:

```text
sum_j ||[u,q_j]||_2^2
 <= 2 sum_j tau(q_j)
 = 2 tau(e).
```

No invariance of `e` or of the individual atoms was used.

For the gap statement, every self-adjoint element of `q_j M_d q_j` has the
form `x=c q_j` with `c in R`.  Its normalized corner trace is `c`, so

```text
x-tau_(q_j)(x)q_j=0,
```

and it commutes with every compression `q_j u_s q_j`, which is also scalar in
the one-dimensional corner.  Thus the displayed Poincare inequality holds
for every positive choice of gap constant.

Finally let `a=v q_j v^*` and `b=q_l`.  Both are rank-one projections, so
`tau(a)=tau(b)=1/d`.  Since

```text
tau(ab)=tau(aba)=||b a||_2^2 >= 0,
```

we have

```text
||a-b||_2^2
 = tau(a)+tau(b)-2 tau(ab)
 <= 2/d.
```

If `e != 0`, then `rank(e)>=1`, hence `1/d <= tau(e)` and

```text
||v q_j v^*-q_l||_2 <= sqrt(2 tau(e)).
```

The two rank-one blocks have equal trace.  When the atoms are chosen inside a
coarse projection they refine it by construction, completing all assertions.
