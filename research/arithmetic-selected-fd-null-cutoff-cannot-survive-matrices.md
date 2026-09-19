---
rg: 2
id: arithmetic-selected-fd-null-cutoff-cannot-survive-matrices
kind: claim
title: The arithmetic finite-dimensional-null Laplacian cutoff vanishes on selected inner-adjoint matrix lifts
distinct_from:
  arithmetic-leak-has-fd-null-laplacian-witness: that constructs the explicit exponentially finite-dimensional-null sequence; this is the matrix-origin upper-semicontinuity needed to kill its selected value.
  tempered-selected-conjugation-vector-obeys-rcc: that asks for weak containment of the entire cyclic conjugation module; this tests only one explicit positive-gap cutoff sequence.
---

**OPEN SELECTED CUTOFF.**  Let `(y_N)` be the sequence in
`arithmetic-leak-has-fd-null-laplacian-witness`.
Suppose asymptotic matrix representations of `A=SL_3(Z[1/p])`, together
with selected unitaries that projectively centralize `C=SL_3(Z)`, induce in
the tracial matrix ultraproduct the twice-adjoint representation `gamma` and
the selected `C`-fixed full-rank operator `T=Ad U`.  Prove

```text
lim_(N->infinity) ||gamma(y_N)T||_2=0.                  (ASC1)
```

## Semantic status: a universal certificate, not a weaker theorem

In the ultraproduct hypotheses above, `T` is exactly `C`-fixed.  Therefore
for every `N`, not merely asymptotically,

```text
gamma(x_N)T=T,
gamma(y_N)T=(gamma(h)-1)T,
||gamma(y_N)T||_2^2
  =2(1-|tau([U,pi(h)])|^2).                            (ASC0)
```

Thus `(ASC1)` is semantically equivalent to qualitative projective transfer.
The gain from `(APW1)` is a single explicit finite-dimensional-null
certificate sequence; it does not make the no-leak assertion logically
weaker.  The route `arithmetic-fd-null-cutoff-gives-projective-transfer`
records the useful certificate direction; the reverse direction is the
displayed identity `(ASC0)` and is stated here without adding a circular
route to the dependency graph.

The sequence also has one fixed maximal-C-star limit.  By
`arithmetic-kazhdan-corner-is-fd-invisible`,

```text
x_N -> p_C,
y_N -> z=(u_h-1)p_C,                                   (ASCZ)
```

where `z` is nonzero but every exact finite-dimensional representation of
`A` kills it.  Thus `(ASC1)` asks whether this explicit FD-radical element
vanishes on the selected twice-adjoint MF representations coming from
arithmetic microstates.  Full membership `z in I_MF(A)` would be stronger
than necessary.

Equivalently, for every `epsilon>0` there are a fixed `N` and a finite
presentation-defect tolerance `delta>0` such that every finite matrix tuple
with defect below `delta` and projective `C`-centrality defect below `delta`
satisfies

```text
||gamma_n(y_N)T_n||_2 < epsilon.                        (ASC2)
```

Exact finite-dimensional representations satisfy the estimate by the
exponential bound `(APW2)`.  The open content is upper semicontinuity for
the selected inner-adjoint vectors of approximate matrix models.  Ordinary
word telescoping does not suffice because `N` is chosen only after the
desired accuracy, while the canonical arithmetic HNN leak retains the
nonzero value `(APW3)` for every `N`.  Consequently the proof must use
matrix origin, not merely the group relations, canonical character, or
positivity.

The arithmetic hypotheses are essential.  The established counterexample
`exact-codensity-does-not-imply-matricial-rcc` gives an abstract co-dense
Kazhdan pair for which the analogous `y_N` has zero norm in every exact
finite-dimensional representation while a full-rank twice-adjoint selected
unitary retains maximal mass in a matrix ultraproduct.  Thus property `(T)`,
exact co-density, matrix origin, and full rank do not imply `(ASC1)` in
general.  A proof here must use the specific denominator and root relations
of `SL_3(Z[1/p])`.

There is also a sharp conditional arithmetic countermodel.  In the compact
homogeneous-quotient crossed product, let `P` be one compact-open orbit,
`U=1-2P`, and `m=mu(P triangle hP)`.  Then `U` is exactly `C`-central and

```text
tau(U u_h U u_h^*)=1-2m,
||gamma(y_N)T||_2^2=8m(1-m)                            (ASC3)
```

for every `N`.  The quantized Hecke dent bounds `m` away from zero.  Hence
Connes embeddability of
`sl3-homogeneous-quotient-crossed-product-is-connes-embeddable` would give
matrix lifts refuting `(ASC1)` with a uniform positive floor.  That
embeddability is open, so `(ASC3)` is a conditional stress test rather than
an unconditional refutation.

Finally, `normal-closure-heat-exits-control-arithmetic-leak` gives a fixed
finite non-spherical localization of the same target: the denominator
displacement is bounded by cross first-exits of finitely many conjugated
lattice heat filters.  Commuting a filter past `h` only makes it exact on
the correspondingly transported vector and is tautological.  The missing
input is why matrix-origin arithmetic relations kill the filters on the
original selected vector.  Any proof by scalar compression back to the
lattice-fixed space returns to the already-fenced finite spherical Hecke
moment problem.
