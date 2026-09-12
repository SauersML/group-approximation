---
rg: 2
id: reduced-mf-hyperlinear-radical-in-amenable-radical-proof
kind: route
title: Push the corona embedding to every tracial ultraproduct and apply BKKO
target: reduced-mf-hyperlinear-radical-in-amenable-radical
requires: [bkko-reduced-traces-concentrate-on-amenable-radical]
---

Let `iota : C*_r(G) -> Q = prod_n M_(d_n) / sum_n M_(d_n)` be injective.

**Unital reduction.**  `P = iota(1)` is a nonzero projection of `Q`; lift it to
projections `P_n` of rank `r_n`.  Since `P != 0`, infinitely many `r_n` are
positive; restricting to those coordinates and compressing by `P_n` gives an
injective unital *-homomorphism into `prod_(n in S) M_(r_n) / sum`.  Coordinates
with `r_n = 0` carry vanishing norm, so no element loses its norm.  Assume
`iota` unital from now on.

**Unitary lifts.**  For `g in G`, `iota(lambda_g)` is a unitary of `Q`; lift it
to `x_n(g)` with `||x_n(g)* x_n(g) - 1|| -> 0` and correct by polar
decomposition to unitaries `u_n(g) in U(d_n)`.  Because `iota` is a
homomorphism,

```text
||u_n(a) u_n(b) - u_n(ab)||_op -> 0        (a, b in G).
```

Different lifts differ by sequences tending to zero in norm, so they have the
same asymptotic traces.

**Every limit trace is a trace on the reduced algebra.**  Fix a free
ultrafilter `omega` on the index set and let `M^omega` be the tracial
ultraproduct of the `M_(d_n)` with the normalized traces.  Sequences tending to
zero in operator norm tend to zero in normalized Hilbert--Schmidt norm, so the
quotient `Q -> M^omega` is a unital *-homomorphism.  Composing with `iota`
gives a unital *-homomorphism `C*_r(G) -> M^omega`, and

```text
tau_omega = tr_omega o (quotient) o iota
```

is a tracial state on `C*_r(G)` with `tau_omega(lambda_g) = lim_omega tr(u_n(g))`.

**Apply BKKO.**  By `bkko-reduced-traces-concentrate-on-amenable-radical`,
`tau_omega(lambda_s) = 0` for every `s notin R_a(G)` and every free ultrafilter
`omega`.  Every cluster point of the bounded sequence `tr(u_n(s))` is such an
ultralimit, so

```text
tr(u_n(s)) -> 0        (s notin R_a(G)).
```

**Visibility.**  Given a finite `F in G` and `delta > 0`, for all large `n`
the operator-norm defects on `F` are at most `delta`.  Normalized
Hilbert--Schmidt defect is bounded by operator-norm defect, and
`Re tr(u_n(s)) <= 1/2`.  So `s` is tracially visible with `c_s = 1/2`.

**Radical form.**  An element is tracially visible exactly when some
homomorphism into a tracial matrix ultraproduct does not kill it.  One
direction: take the ultralimit of visible models along increasing finite sets
and shrinking defects; the unitary has `Re tau <= 1 - c < 1`, so it is not `1`.
The other: lift the homomorphism and use faithfulness of the trace,
`1 - Re tau(u) = ||1 - u||_2^2 / 2 > 0`.  Hence `Rad_hyp(G) <= R_a(G)`.
