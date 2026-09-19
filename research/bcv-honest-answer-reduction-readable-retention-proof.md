---
rg: 2
id: bcv-honest-answer-reduction-readable-retention-proof
kind: route
title: Recover every padded answer bit at a Boolean evaluation point
target: bcv-honest-answer-reduction-retains-readable-closure
requires:
  - bcv-perfect-answer-reduction-decodes-double-cover
---

Restriction-free padding appends unconstrained readable and unreadable
variables while retaining every original variable as an initial coordinate.
Choose the appended observables to be identities. Purification has the same
graph, variables, and strategies and changes only how readable values are
substituted into the linear constraints. Double cover duplicates the same
matrices, and oracularization retains the isolated-player measurements. Thus
it is enough to recover the padded strategy from the point measurements in
the final answer-reduced strategy.

Write a padded answer outcome as two Boolean functions

```text
f^R,f^L : F_2^Lambda -> F_2.
```

In the proof of Proposition 5.80, BCV equation `(192)` defines the
isolated-player point PVM by data processing the source PVM along

```text
f^kappa |-> Ind(f^kappa)(p),       kappa in {R,L},        (HAP1)
```

where `Ind(f)` is the multilinear extension in the coordinate block
`S_f` and the value lies in `F_q`. For each `xi in F_2^Lambda`, choose
the point `p_xi in F_q^S` whose `S_f` coordinates are `xi` and whose
other coordinates are zero. Multilinear interpolation on the Boolean cube
gives

```text
Ind(f)(p_xi)=f(xi) in {0,1} subset F_q.                  (HAP2)
```

Fix an `F_2`-linear coordinate functional `lambda:F_q->F_2` with
`lambda(1)=1`. The observable obtained by multiplying the target answer-bit
observables selected by `lambda` is therefore exactly the padded source
observable `f(xi)`. If `kappa=R`, all of those target bits are readable
by BCV Table 3, so every padded source readable spectral projection lies in
the target initial readable Boolean algebra. If `kappa=L`, the same
calculation writes every padded source unreadable observable as a word in
target structural unreadable generators.

Let `i` denote the resulting map on source readable projections. If `d`
is already represented in the target and `u` is a source unreadable
generator, the preceding word identity gives

```text
i(u d u^*) = i(u) i(d) i(u)^*.                          (HAP3)
```

Induction on unreadable words and closure under Boolean operations proves
`(HAR1)`. The recovery maps are literal left inverses to the padding and
evaluation maps on the source generators, so the Boolean homomorphism is
injective. A finite Boolean algebra has dimension equal to its number of
atoms, and an injective unital Boolean homomorphism cannot decrease that
number, proving `(HAR2)`.

This route records the literal left inverse on BCV's chosen forward
completeness strategy. It is not the boundary for arbitrary targets:
`bcv-perfect-answer-reduction-decodes-double-cover` now gives an exact
atomwise decoder for every attained perfect target ZPC strategy and retains
its readable closure. The finite-field term in the quantitative theorem is
only positive-error slack. The arbitrary-target theorem naturally decodes
to the double cover and uses synchronization or bipartiteness to recover the
uncovered source; it need not recover the particular source strategy with
which the forward construction began.
