---
rg: 2
id: supercritical-network-needs-noncanonical-cuts
kind: claim
title: No branch network built from canonical data can be supercritical, and the Fourier-flat character cuts are subcritical by a factor of two
artifacts:
  - notes/TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md
  - notes/TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md
  - research/artifacts/fractional-branch-pressure-2026-08-19.md
distinct_from:
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out fixed universal algebraic support zeros in the transport formulation; this rules out canonical state families in the branching formulation and additionally computes the subcritical ceiling of the character cuts.
  fixed-atlas-transport-cost-cannot-separate: that kills one fixed positive-dual cost matrix; this kills every canonical branch network regardless of cost, and its mechanism is the exact model's own carrier mass rather than a dual value.
  exact-models-cannot-separate-marked-pair: that concerns separation of a marked pair by exact finite models; this concerns supercriticality of a branch network and is a statement about which data the network may consume.
---

Consider a candidate branching obstruction in the sense of
`fractional-source-branch-pressure`: states `P_i^(n)`, branch words, coverage
fractions `c_e`, a rational certificate `(y,kappa)` with
`B^T y >= (1+kappa)y`, and errors `eta^(n) -> 0` along a sequence of
microstates with relator defect `delta_n -> 0`.

Call the network **canonical** if the states, words and thresholds are fixed by
the presentation alone, so that along the sequence

```text
x^(n) -> x^inf,      eta^(n) -> eta^inf,
```

where `(x^inf, eta^inf)` are the corresponding data computed in an exact
tracial realization of the presented group (its group von Neumann algebra, or
any exact model in which the same words and cuts are defined).

**(NCC1)**  A canonical supercritical network is impossible.  Indeed
`(FSB3)` holds in the exact model as well, so

```text
kappa (y . x^inf) <= y . eta^inf = lim y . eta^(n) = 0,
```

and since `y>0` and `x^inf >= 0` this forces `tau(P_i^inf)=0` for every state
on the supercritical component.  For the atlas Pauli cell this contradicts
`tau(E)=1/8`.

**(NCC2)**  Consequently every candidate network must select at least one
state projection, source projection or threshold from finite-multiplicity or
matrix-coordinate data that does **not** converge in the exact model.  The
supercriticality has to be a property of the microstate's coordinates, never of
the presented group.

**(NCC3) The character cuts are subcritical, quantitatively.**  Take the raw
character cuts `F_eps` and transported cuts `G_eta` of
`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md`, with

```text
tau(F_eps) = tau(G_eta) = 1/8,     tau(F_eps G_eta) = 1/64
```

for all sixteen pairs.  Apply `soft-block-mass-yields-fractional-branch` with
`P=F_eps`, `Q=G_eta`, `W=1`.  The coverage guaranteed out of one raw cut totals

```text
sum_eta c_eta(t) >= 4 (1/8 - t^2)/(1 - t^2),
```

which is positive only for `t^2<1/8` and is at most `1/2` there; and the
Chebyshev ceiling `(SBM2)` gives

```text
sum_eta c_eta(t) <= 1/(2 t^2),
```

which is at most `1` for every `t >= 1/sqrt(2)`.  So the flat character table
is subcritical at every threshold at which it produces a branch at all, and it
misses the supercritical line by exactly a factor of two.  This is `(NCC1)` made
visible: those cuts and masses are canonical, hence they could not have been
supercritical.

## How to read this

It is not a kill.  It is the statement that "make the error spread" cannot be
executed on canonical Fourier data, and the reason is not weakness of the
estimates: the exact model realizes them.  Two escapes remain open and both are
already named in this graph.

- **Finer cuts.**  Split the character cuts by finite multiplicity, as in
  `atlas-one-cut-finite-multiplicity-extraction`.  Their traces are not pinned
  by the exact model, so `(NCC1)` does not apply to them.
- **Exhibited spikiness.**  `(NCC3)` bounds only what the *mass* forces.  A
  microstate whose blocks are far spikier than flat mass requires can have
  coverage close to one; but that spikiness must be produced from the relators,
  not inferred from `||X||_2`.  This is the productive half of
  `pauli-block-tail-or-flat-rigidity-dichotomy`.

Section 6 of `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md` proves the same
conclusion for the Reynolds row/column translations by the same mechanism, and
the "falsification gate" bullet of `atlas-supercritical-pauli-branching-cycle`
states the integer case in prose.  `(NCC1)` is the general theorem behind both.
