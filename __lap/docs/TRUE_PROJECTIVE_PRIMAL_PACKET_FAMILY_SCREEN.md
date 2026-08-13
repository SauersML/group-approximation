# Exact primal-packet screen for the computed projective family

Date: 2026-08-11

## Outcome

Exact Gram--LLL certificates now test the primal harmonic lattice at every
computed projective level in

```text
53, 61, 73, 79, 89, 97, 121.                       (PPF1)
```

The harmonic ranks are respectively

```text
2, 2, 0, 2, 2, 0, 7.                               (PPF2)
```

At every nonzero-rank level except `53`, there is a determinant-one basis of
the projected primal lattice `Q_X` whose Gram matrix `G_X` satisfies

```text
max_i sum_j |(G_X)_{ij}| < B_X^2.                   (PPF3)
```

Consequently the synthesis operator `T_X:e_i |-> q_i` obeys

```text
||T_X||^2=lambda_max(G_X)
          <=max_i sum_j |(G_X)_{ij}|<B_X^2,         (PPF4)
```

and, in particular, every basis packet has norm below the spherical
threshold.  By the successive-minimum theorem,

```text
B_X lambda_1(Q_X^#)>=1.                             (PPF5)
```

Level `53` is the unique tested exception to this sufficient packet test.
This is exactly the level already isolated by the nonintegral subthreshold
harmonic class and the paired-discriminant calculation.  The packet screen
there is **inconclusive**, not a proof of denominator collapse or of failure
of TRUE.

## Exact finite-family certificate

For each positive-rank level, invert the exact exported Gram matrix of
`Q_X^#`, clear denominators, and apply exact Gram--LLL.  If `U_X` is the
resulting integral basis change, every certificate verifies

```text
|det U_X|=1.                                        (PPF6)
```

Thus the displayed vectors form a basis of the full primal lattice, not a
finite-index packet sublattice.  The numerical renderings of the exact
rational inequalities are:

| level | rank | `max ||q_i||^2` | `max_i sum_j |<q_i,q_j>|` | `B_X^2` | result |
|---:|---:|---:|---:|---:|:---|
| 53  | 2 | 14.02417335 | 14.08246543 | 12 | packet test fails |
| 61  | 2 | 8.02506134  | 8.18045032  | 28 | safe |
| 73  | 0 | --          | --          | 28 | vacuous |
| 79  | 2 | 8.01355670  | 8.02524940  | 28 | safe |
| 89  | 2 | 1.64782018  | 1.72170173  | 12 | safe |
| 97  | 0 | --          | --          | 28 | vacuous |
| 121 | 7 | 5.79618123  | 8.76412387  | 12 | safe |

All comparisons in the JSON certificates are made over `Q`; the decimals
are only for readability.  In particular, at level `121`,

```text
||T_121||^2 < 8.765 < 12.                           (PPF7)
```

This is stronger than seven separate short-vector inequalities.  The seven
new directions form one uniformly controlled Riesz/synthesis packet at this
level, despite the enormous coefficients of the raw algebraically dual
basis.

## What this changes

The first important signal is that increasing harmonic rank did not degrade
the packet geometry.  Level `121` introduces seven genuinely new harmonic
directions, yet its reduced packet operator is better conditioned relative
to the threshold than the rank-two levels `61` and `79`.

The second signal is the exact isolation of `53`.  Among every computed
positive-rank chart, the only failure of the elementary packet-radius test is
the same chart whose paired integral repair was already known to require
special treatment.  This supports a family proof organized as

```text
uniform short primal packets for the generic charts
  + finitely many paired-discriminant exceptional charts.     (PPF8)
```

The third signal is methodological.  Direct dual SVP is unnecessary once a
short primal packet is available.  Exact Gram--LLL in rank equal to the
harmonic dimension certifies the denominator inequality, even when the
ambient cellular complex has thousands of coordinates.

## Exact scope

This is a finite-family theorem, not a uniform theorem over all projective
levels.  Moreover, `Q_X` is the orthogonal projection of the integral cycle
lattice.  A short vector of `Q_X` need not have a sparse or uniformly short
integral lift in the ambient cellular complex.  Hence `(PPF3)` proves a
denominator/systole statement.  It does not supply the compatible bounded
integral section required for numerator control.

The next family theorem should explain why every genuinely new harmonic
space admits a spanning packet satisfying a level-independent radius bound,
or the stronger row-sum bound `(PPF3)`.  Separately, the ambient lift packets
must be controlled.  The present data suggest that `53` should be treated as
a finite exceptional paired-discriminant chart rather than as the model for
generic growth.

## Reproduction

The exact Sage script is

```text
experiments/sl3_projective_primal_packet.py
```

and the certificates are

```text
experiments/projective-cellular-p53-primal-packet.json
experiments/projective-cellular-p61-primal-packet.json
experiments/projective-cellular-p73-primal-packet.json
experiments/projective-cellular-p79-primal-packet.json
experiments/projective-cellular-p89-primal-packet.json
experiments/projective-cellular-p97-primal-packet.json
experiments/projective-cellular-n121-primal-packet.json
```

