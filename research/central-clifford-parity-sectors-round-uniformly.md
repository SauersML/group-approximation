---
rg: 2
id: central-clifford-parity-sectors-round-uniformly
kind: claim
title: Exact positive-distance parity uniformly rounds every central Clifford sector
distinct_from:
  sparse-clifford-cycles-refute-average-commutator-rounding: that constructs a sparse projective commutation graph without parity checks; this proves that exact positive-distance parity makes every nontrivial central-sign sector pay constant complete-pair energy.
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that gives only a zero-versus-nonzero support statement for arbitrary reflections under stopping distance; this gives a quantitative same-Hilbert correction for direct sums of scalar-commutator sectors using ordinary code distance.
  complete-overlay-code-group-has-uniform-conjugation-gap: that starts with an exact representation of the already abelian code group; this allows noncommuting Clifford sectors and bounds the trace on which they occur.
---

Let `C=ker(H)<=F_2^L` have relative distance at least `delta>0`.  Let
`Q_1,...,Q_L` be reflections in a finite tracial von Neumann algebra and
assume every parity check is exact: the reflections in each row commute and
their product is `I`.

Assume also that there is a central decomposition `1=sum_omega p_omega`
such that on every summand all pair commutators are scalar signs:

```text
p_omega Q_i Q_j=(-1)^(b_omega(i,j))p_omega Q_j Q_i.       (CCP1)
```

Put

```text
E_com=(1/L^2)sum_(i,j)||Q_iQ_j-Q_jQ_i||_2^2.              (CCP2)
```

Then there are commuting reflections `Q_i'` on the same Hilbert space,
satisfying every parity check exactly, for which

```text
(1/L)sum_i ||Q_i-Q_i'||_2^2 <= E_com/delta^2.             (CCP3)
```

Consequently sparse Clifford cycles, matching reservoirs, finite-rank
projective cocycles, and arbitrary direct sums of those sectors cannot
refute shared-face synchronization once the positive-distance parity layer
is exact.  Any countermodel to
`repeated-ldpc-shared-face-marginal-synchronization` must use genuinely
noncentral commutators and/or spectral mixtures whose parity faces have not
already been made into one shared exact tuple.

