---
rg: 2
id: kt-double-reduced-cstar-is-mf
kind: claim
title: The reduced C-star algebra of the q=2 Kun--Thom double is MF
distinct_from:
  reduced-amalgam-canonical-trace-is-mf: that asks for operator-norm microstates selecting the canonical trace on the full group C-star algebra; this asks for a norm-corona embedding of the reduced group C-star algebra, after which the trace is selected automatically by uniqueness.
  symmetric-double-weak-mf: that embeds the abstract group, and in the proof a full auxiliary symmetric amalgam, into a norm matrix corona; neither conclusion says that the regular representation norm is approximated.
  kt-double-mixed-word-trace-selection: that is equivalent to hyperlinearity and controls normalized Hilbert--Schmidt moments only; reduced C-star MF additionally controls operator norms of every group-ring element.
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

**OPEN.**  For the explicit Kun--Thom pair over `F_2`, put

```text
Gamma < G,                 D=G *_Gamma G.
```

Prove that `C*_r(D)` embeds into a norm matrix corona.

The target is stronger than hyperlinearity of `D`.  Its value is that the
reduced algebra has a unique tracial state: the `q=2` Bass--Serre calculation
in the cited artifact gives a faithful non-elementary tree action and trivial
amenable radical, so the BKKO theorem makes the canonical regular trace the
only trace on `C*_r(D)`.  Consequently any MF embedding of this reduced
algebra automatically induces the canonical trace in a tracial matrix
ultraproduct and makes `D` hyperlinear.

This is not supplied by residual finiteness of `G` or by Shulman's symmetric
full-amalgam theorem.  In particular, MF passes to C-star subalgebras, so the
claim already requires

```text
C*_r(G) is MF.                                             (KRC1)
```

Residual finiteness supplies group-level norm-corona separation and an MF
completion carrying an abstract regular trace; it does not supply `(KRC1)`.
The concrete profinite regular completion used in
`symmetric-double-weak-mf-proof` fails to factor through `C*_r(G)` by
`kt-shulman-profinite-vertex-model-is-nontempered`.

The remaining relative-microstate architecture is quantitatively constrained
by `kt-return-expectation-pays-one-full-edge-principal-angle`.  For the fixed
compressor return `h=t^(-1) gamma t outside Gamma`, vanishing of the matrix
edge expectation forces the aggregate forward covariance leakage of
`C*(phi_n(Gamma))` under `phi_n(t)` to have liminf at least one.  If an edge
word basis has Gram lower bound `lambda_n`, word lengths `ell_(i,n)`, and
actor covariance defect at most `epsilon_n`, this requires

```text
lambda_n^(-1) epsilon_n^2 sum_i ell_(i,n)^2 >= 1-o(1).  (KRC2)
```

Thus the positive model cannot be a uniformly conditioned exactification of
the vertex inclusion.  It must use genuinely approximate coordinates whose
vanishing pointwise defect is amplified by growing word complexity or a
degenerating moving edge Gram matrix.  The latter escape is real even for
exact canonical-character vertex sequences:
`kt-kazhdan-edge-grams-are-conditioned-only-at-fixed-radius` constructs
moving edge words with arbitrarily small Gram eigenvalue.  Property `(T)`
controls every fixed window but supplies no uniform conditioning at the
moving radius required here.

The infinite index of the actual compressor strengthens this from a
one-direction obstruction to a divergent-capacity requirement.
`kt-infinite-index-returns-force-divergent-edge-leakage` proves that any
relative vertex microstates realizing the canonical edge expectation must
satisfy

```text
||(1-E_(B_n))Ad(phi_n(t))E_(B_n)||_HS^2 -> infinity,    (KRC3)
```

and hence the left side of `(KRC2)` must diverge rather than merely stay
above one.  The positive construction must therefore create unboundedly many
moving edge directions on which pointwise-small covariance errors aggregate.

The unnormalized divergence cannot by itself be opposed to the full actor.
`vanishing-weight-block-carries-full-actor-edge-leakage` constructs canonical
approximate tables of the actual full Kazhdan actor, including its strict
compressor, in which all of the divergent leakage sits on a vanishing
physical-trace summand.  The dominant exact finite-image summand makes every
exterior-return expectation tend to one, so this is not a reduced relative
model.  It proves that the next positive or negative step must control the
**joint distribution** of return-expectation loss and leakage across physical
trace sectors; aggregate leakage plus actor relations alone is padding-blind.
