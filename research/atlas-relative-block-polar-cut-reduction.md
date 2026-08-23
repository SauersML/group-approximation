---
rg: 2
id: atlas-relative-block-polar-cut-reduction
kind: claim
title: One positive typed block of the relative Atlas unitary supplies the finite common-cut field
distinct_from:
  separate-packet-calculi-have-no-common-matching: that rules out selectors formed separately from two packet reservoirs; this uses the legal mixed coordinate `P_i U Q_j` and therefore breaks the independent gauges.
  pauli-overlap-yields-positive-spectral-corner: that extracts explicit constants from one compulsory Pauli cross-Gram sum; this gives the general finite-menu polar construction and isolates typed mass localization as the only missing hypothesis.
  pauli-overlap-floor-is-subcritical-for-extension-authentication: that shows positive mass does not align several packet paths or force holonomy; this claims only the acquisition schema's common endpoint cut and bounded coordinate transport.
  atlas-a8-mixed-block-transport-has-permutation-models: that realizes every rational untyped block-mass plan; this uses that absorber to prove why total mass one cannot be localized to the required typed block without a relation-sensitive estimate.
---

Let `P_1,...,P_a` and `Q_1,...,Q_b` be fixed word-visible orthogonal
finite-carrier decompositions of the target and source spaces, and let `U`
be the exact unitary relative coordinate of the two regular Atlas charts.
For a fixed nonempty admissible set of typed incidences
`E subset {1,...,a} times {1,...,b}`, assume

```text
sum_((i,j) in E) ||P_i U Q_j||_2^2 >= alpha > 0.       (RBP1)
```

There is a deterministic finite-menu selection of `(i,j) in E`, projections
`R<=Q_j`, `S<=P_i`, and a polar partial isometry `V:R H -> S H` such that

```text
tau(R)=tau(S) >= alpha/(2|E|-alpha),                    (RBP2)
P_i U Q_j R=V A,
sqrt(alpha/(2|E|)) R <= A <= R.                         (RBP3)
```

In particular `A` is invertible on `R` with

```text
||A^(-1)|| <= sqrt(2|E|/alpha).                         (RBP4)
```

Choose the lexicographically first block maximizing the Hilbert--Schmidt
mass on `E`.  Its square `T^*T`, for `T=P_iUQ_j`, has normalized trace at
least `alpha/|E|`.  Put

```text
lambda=alpha/(2|E|),       R=1_[lambda,1](T^*T).
```

If `p=tau(R)`, the contraction bound gives

```text
alpha/|E| <= tau(T^*T) <= lambda(1-p)+p,
```

and rearrangement is `(RBP2)`.  Polar decomposition on `R` gives
`(RBP3)--(RBP4)` and `S=VRV^*`.

This is an admissible finite-matrix selector.  Under the Atlas double gauge
`U |-> DUC`, every block mass is unchanged, `R` transforms by the source
gauge, `S` by the target gauge, and `V` covariantly between them.  Compression
and transport by `V` do not increase Hilbert--Schmidt error; if normalization
by `A^(-1)` is used, the loss is at most the fixed factor in `(RBP4)`.
The amplitude `A` and all other transported path products may be retained as
stable nuisance monomials.  No claim that `A` is a group word is needed: the
relation terms remain compressed literal word paths, and `V` is only the
chosen finite coordinate gauge.

For the complete block alphabet, unitarity gives

```text
sum_(i,j) ||P_iUQ_j||_2^2=1.                            (RBP5)
```

Thus `(RBP1)` always holds with `E` equal to all `ab` blocks and `alpha=1`.
The relative unitary therefore defeats the separate-packet gauge no-go and
always supplies a positive **untyped one-edge** common cut.

It does not by itself fill the Atlas typed census.  The census needs the
winning block to lie in the prescribed hard/interior/comb incidence set on
which the same compressed paths define `W,R0,R1,L0,L1` and the three desired
columns.  Equation `(RBP5)` gives no mass lower bound on that proper set.
Indeed the regular-`A8` permutation absorber realizes every rational
transportation plan with the fixed margins; whenever those margins admit a
plan supported on `E^c`, separate type and block-mass data have an exact
finite model with zero left side in `(RBP1)`.

Nor does applying the construction separately to three required paths make
their cuts common.  Positive spectral cuts can have zero meet, and fixed
positive cross-Gram mass retains arbitrary residual holonomy.  Direct-summing
the three polar corners merely gives three differently labelled unknown
multiplicity reservoirs, so it cannot support one nuisance-quotient matrix
in the same three variables.

Consequently the load-bearing selector field reduces exactly to a typed
localization estimate `(RBP1)` for one incidence set already carrying all
required path labels.  Once such an estimate is derived from a literal mixed
Atlas relation, the finite selection, positive mass, and dimension-independent
Hilbert--Schmidt loss are automatic by `(RBP2)--(RBP4)`.  The existing
positive-overlap/subcritical results do not refute this one-edge construction;
they prove that it cannot substitute for the missing simultaneous typed
localization.
