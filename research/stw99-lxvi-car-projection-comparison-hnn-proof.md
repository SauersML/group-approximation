---
rg: 2
id: stw99-lxvi-car-projection-comparison-hnn-proof
kind: route
title: Turn unequal CAR ranks into a proper equivalent subprojection
target: stw99-lxvi-car-hnn-trace-balance-dichotomy
requires: []
---

Let `p,q in D` be projections which are Murray--von Neumann equivalent in
`A`.  Suppose, toward a contradiction, that

```text
tau_D(p)<tau_D(q).
```

Projection comparison in the CAR algebra is completely determined by its
unique trace.  Hence there is a projection `r<q` in `D` which is
Murray--von Neumann equivalent to `p` inside `D`.  The ambient equivalence
`p equivalent_A q` now gives

```text
q equivalent_A p equivalent_D r<q.
```

Thus `q` is an infinite projection in `A`.  An infinite subprojection makes
the unit infinite: adding `1-q` to the equivalence displays `1_A` as
equivalent to the proper subprojection `r+(1-q)`.  This contradicts
finiteness of `1_A`.  Interchanging `p` and `q` rules out the opposite trace
inequality and proves `(1)`.

Apply `(1)` to `p=theta_0(e)` and `q=theta_1(e)` for every projection
`e in C`; relation `(2)` makes them unitarily equivalent in `A`.  In a
real-rank-zero algebra, finite-spectrum selfadjoint elements, and hence the
linear span of projections, are norm dense in the selfadjoint part.  The
two bounded traces therefore agree on all of `C`, proving `(3)`.  Conversely,
if they differ, they differ on some projection, and the first paragraph
makes the ambient unit infinite.

Now assume `C` is finite dimensional.  For each edge image
`theta_i(C) subset D`, the trace-orthogonal projection gives a faithful
`tau_D`-preserving conditional expectation

```text
E_i:D->theta_i(C).
```

When the edge traces agree, the standard reduced HNN construction for
`(D,theta_0,theta_1,E_0,E_1)` has a faithful canonical expectation `E` onto
`D`, and reduced-word cancellation gives a trace

```text
Tau=tau_D after E.
```

It is faithful because both `tau_D` and `E` are faithful.  Its matrix
extensions are faithful, so the reduced HNN algebra is stably finite.  The
universal full HNN algebra maps unitally onto this reduced algebra, and
pulling `Tau` back gives a tracial state on the full algebra.  If the full
algebra is simple, the quotient map has zero kernel (equivalently its
nonzero trace is faithful), and stable finiteness follows.

If the edge traces do not agree, a mismatched edge projection is unitarily
conjugate to one of different CAR trace in either HNN construction.  The
first paragraph makes its unit infinite before any simplicity or
inductive-limit argument enters.  This closes both sides of the stated HNN
dichotomy.
