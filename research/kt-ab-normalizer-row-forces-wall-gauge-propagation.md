---
rg: 2
id: kt-ab-normalizer-row-forces-wall-gauge-propagation
kind: claim
title: The first full-pair normalizer row propagates every Kun--Thom flat-wall gauge
distinct_from:
  kt-a2-heisenberg-flat-wall-survives-one-more-compressor: That constructs a wall while keeping the transverse Heisenberg generators identical in the two maps; this proves that the full-pair normalizer word C=AB^(-1) forbids keeping A identical once the B-wall is present.
  kt-two-positive-compressors-generate-full-obstruction: That gives a permutation/canonical-lamp obstruction for the full pair A=CB,B but no unitary-HS inequality; this gives an explicit normalized-HS inequality for one mixed Gamma--normalizer row, while stopping short of a full unitary obstruction.
  kt-two-compressor-irrep-flow-has-profinite-stationary-points: That proves scalar irrep weights can be stationary under both compressor flows; this acts on the actual relative multiplicity gauge and shows that its B-displacement must propagate to A.
  kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath: That supplies exact models of every A,B-only lamp cylinder and actor word; this uses the missing mixed Gamma incidence, namely covariance of a fixed Gamma element under C=AB^(-1).
  kt-double-shortest-fold-repair-is-a-bare-wall: That extracts a bare wall from a repaired length-two mixed trace; this quantifies how that wall must spread from the B generator to the A generator when the first full-actor normalizer row is imposed.
---

**ESTABLISHED GAUGE-PROPAGATION INEQUALITY.**  Retain the explicit full
Kun--Thom compressor pair

```text
B=I+E_12,                  A=C B,
C=A B^(-1),                C^3=1,                       (KGP1)
```

where `C` cyclically permutes the polynomial variables and normalizes
`Gamma`.  Let `pi:Gamma->U(d)` be any common finite-dimensional Gamma map,
fix `gamma in Gamma`, and write

```text
x=pi(gamma),                    y=pi(alpha_C(gamma)).     (KGP2)
```

For two candidate vertex maps let `a_i,b_i` be their unitaries assigned to
`A,B`, and define the literal normalizer words and returned folds

```text
c_i=a_i b_i^*,
h_i=b_i^* x b_i,                i=0,1.                   (KGP3)
```

If

```text
epsilon_i=||c_i x c_i^*-y||_2,                           (KGP4)
```

then

```text
||h_0-h_1||_2
 <=epsilon_0+epsilon_1+2||a_0-a_1||_2.                  (KGP5)
```

Consequently a squared `B`-fold gap tending to two cannot be extended over
the full pair while keeping the two `A` unitaries equal or `o_2(1)`-close.
More precisely, if `epsilon_0,epsilon_1->0`, then

```text
liminf ||a_0-a_1||_2 >=1/sqrt(2),                       (KGP6)
```

so the squared `A`-gap is at least `1/2`.  If `a_0=a_1`, then one of the two
fixed mixed normalizer rows has defect at least `1/sqrt(2)-o(1)`.

Thus the one-compressor flat wall cannot be extended to the pair by changing
only `B` and repairing a few boundary blocks: its gauge must propagate
macroscopically into `A`.  This is not a full obstruction.  Two complete
vertex maps are allowed to differ on both `A` and `B`, and `(KGP5)` is
compatible with a coherent relative-commutant cocycle over the whole actor.
Constructing or excluding that nonamenable multiplicity cocycle remains the
full-actor seam.

Proof: `kt-ab-normalizer-gauge-propagation-proof`.
