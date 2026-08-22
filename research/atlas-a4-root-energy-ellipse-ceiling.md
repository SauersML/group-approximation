---
rg: 2
id: atlas-a4-root-energy-ellipse-ceiling
kind: claim
title: One ellipsoidal scalar in square-root four-cycle energies beats the 19243 wall
distinct_from:
  atlas-a4-joint-weighted-cycle-ceiling: that target leaves five positive weights existentially quantified; this target analytically eliminates all of them and retains only one nonlinear scalar of the four trace deficits.
  atlas-a4-anisotropic-four-cycle-ceiling: that target uses a fixed diagonal Cauchy budget; this target uses the exact triangle envelope and the optimized weighted S3 exchange rate.
  atlas-a4-root-ellipse-exact-tracial-escape: that gives an exact finite-factor zero of all packet/collision residuals with ellipse value 73; the present claim can therefore only be a matrix-specific trace-exclusion statement.
---

Let `U_n` be a normalized exact-regular A4 context-network sequence in the
fixed reference-aligned coordinates.  In addition to the thirty vanishing A4
packet defects, assume the collision relation itself vanishes:

```text
||q_19243(U_n)-1||_2 -> 0.                             (A4-ROOT-COLLISION)
```

This extra hypothesis is essential: packet normalization alone has an exact
constant reference-alignment counterexample, recorded in
`atlas-reference-packet-root-ellipse-countermodel`.

Put

```text
x_ij(n)=sqrt(1-Re tau_n(V_n(tij))) >=0,
S_n=2x_01(n)+2x_23(n)+4x_30(n).
```

Prove the single scalar ceiling

```text
limsup_n [S_n^2 + S_n x_12(n) + x_12(n)^2] < 3/128.   (A4-ROOT-ELLIPSE)
```

This is the completely optimized form of the four-cycle-to-S3 contradiction.
Indeed `S_n^2` is the exact positive-word triangle upper budget for the
synthesized raw involution `t21`, while `x_12^2` is the budget for the directly
observed raw involution `t12`.  The cross term is precisely what remains after
optimizing the relative weights in the two-generator S3 Cayley gap.

The threshold uses the collision relation directly.  In the Leavitt quotient
necessity sequence `q_19243(U_n)->1`, so
`atlas-19243-relation-forces-s3-distance` gives the squared S3-distance floor
`1/32`; the optimized Cayley dual turns this into `3/128`.  The older
centrality-only route paid an unnecessary second occurrence of the collision
word and produced the weaker threshold `3/512`.

Equivalently,

```text
S_n^2+S_n x_12+x_12^2
 =(S_n+x_12/2)^2 + 3x_12^2/4,
```

so the target is literally membership in one fixed ellipse in the two aggregate
root-energy coordinates `(S_n,x_12)`.

## Analytic audit: the exact identities give the opposite inequality

Put

```text
F_n=S_n^2+S_n x_12(n)+x_12(n)^2.
```

The established identity
`atlas-root-energy-ellipse-controls-s3-distance`, followed by
`atlas-19243-relation-forces-s3-distance`, applies under exactly the collision
hypothesis displayed above and gives

```text
F_n
 >=(3/4) dist_2(U_n,C_(S3))^2
 >=(3/4) max(0,(sqrt(2)-||q_19243(U_n)-1||_2)/8)^2.   (A4-ELLIPSE-LOWER)
```

Consequently every sequence quantified by this claim satisfies

```text
liminf_n F_n >=3/128.                                  (A4-ELLIPSE-WALL)
```

Thus no exact moment or ellipse manipulation from the presently recorded
identities can prove the requested strict upper bound.  If even one sequence
with the stated packet and collision defects exists, `(A4-ELLIPSE-WALL)`
directly contradicts the conclusion.  The claim can only be true because the
quantified class is empty; equivalently, one must prove a positive joint
packet-plus-collision residual gap.  The ellipse is the final contradiction
functional after that nonexistence input, not an independent upper inequality
on a nonempty zero-residual moment set.

There is an even stronger directional counter-bound in the actual Leavitt
necessity sequence.  The additional kernel word `q_14` also has vanishing
defect there, so `atlas-q14-forces-t30-covariance-floor` gives

```text
liminf_n x_30(n)^2 >=1/2.
```

Since `S_n>=4x_30(n)` and all variables are nonnegative,

```text
F_n>=S_n^2>=16x_30(n)^2,
liminf_n F_n>=8.                                       (A4-Q14-ELLIPSE-WALL)
```

This does not refute the claim as formally stated, because it assumes only
collision `19243`, not `q_14`.  It does show that on the intended necessity
sequence the optimized S3 threshold `3/128` is not the active analytic wall:
the one-coordinate `t30` wall is larger by more than two orders of magnitude.
Any proof effort based only on existing exact scalar identities should
therefore target `atlas-a4-t30-energy-ceiling-below-q14-wall`; proving the
ellipse ceiling itself still requires the unresolved joint-gap theorem.

## Attempts

- **Recognize that the corrected target is a uniform joint-relator gap.**
  Once `(A4-ROOT-COLLISION)` is included,
  `atlas-root-energy-ellipse-controls-s3-distance` already gives the opposite
  inequality `liminf F_n>=3/128` for every hypothesized sequence.  Hence the
  requested strict `limsup F_n<3/128` can hold only because no such sequence
  exists.  More precisely, for `rho_k=Reg(A8) tensor I_k` put

  ```text
  epsilon(k,U)=max( ||q_19243(U)-1||_2,
                    max_(w in the thirty-word packet)||w(U)-1||_2 ).
  ```

  The corrected ellipse claim is equivalent to

  ```text
  inf_(k>=1,U in U(20160k)) epsilon(k,U)>0.             (A4-JOINT-GAP)
  ```

  Indeed, if the infimum were zero, choices with `epsilon<1/n`, followed by
  `atlas-a4-context-network-simultaneous-hs-exactification` and
  `atlas-a4-context-exact-regular-normalization`, would give a normalized
  sequence.  Those `o(1)` perturbations preserve the fixed collision word and
  all four root traces, so the established lower wall and the proposed upper
  ceiling would apply simultaneously, a contradiction.  Conversely
  `(A4-JOINT-GAP)` makes the quantified class of sequences empty.  Thus a
  finite SOS search must certify a positive residual gap; merely optimizing
  the ellipse functional on putative zero-residual points is circular.

- **Use the corrected shifted-double-coset compiler.**  The local A4
  centralizer-product theorem cannot be applied to the two raw chart alphabets
  as if they were already aligned: some same-chart packet pairs have product
  order `6`, others order `2`.  `atlas-a4-packet-centralizer-product-compiler`
  now fixes one exact packet alignment `R` and gives the correct constraints
  `C_a R C_b` / `C_b R C_a`.  Any holonomy or moment proof of this ellipse must
  be written in that shifted geometry.  The unshifted `C_a C_b` formulation is
  false.
- **Exploit the exact first-rank finite screen.**
  `atlas-a4-gl5-packet-collision-screen` exhausts all `9,999,360` relative
  positions in `GL5(F2)` for the standard embedded chart `A8`.  Exactly `202`
  satisfy all thirty A4 pair-cubes, distributed among chart-intersection sizes
  `20160`, `1344`, and `168`; collision `19243` is nonidentity on every one.
  Thus the first ambient-rank enlargement has no exact packet-plus-collision
  escape.  The three intersection sizes coincide with the chart/parabolic/core
  ladder and are a concrete guide for a finite-stratum or building-rigidity
  proof.
- **Search the ellipse directly.**  Do not introduce artificial Cauchy or S3
  weights in an SDP/SOS implementation.  Lift the four nonnegative root-energy
  variables and optimize this one positive quadratic form.
- **Exploit direction-selective collision control.**  A strong bound on `t30`
  is especially valuable because it enters `S_n` with coefficient `4`; `t01`
  and `t23` enter with coefficient `2`, while `t12` occupies the separate
  detector coordinate.
- **Use the shorter q14 directional wall when possible.**  The exact kernel
  word `q_14=(t23_(1)t23_(2))^2` becomes a two-syllable `t30` comparison after
  the fixed packet alignment.  `atlas-q14-forces-t30-covariance-floor` proves
  `liminf x_30^2>=1/2`, reducing the sufficient upper target to the separate
  one-coordinate claim `atlas-a4-t30-energy-ceiling-below-q14-wall`.  The
  ellipse remains a valid endpoint, but the one-coordinate route has much
  more numerical slack.
- **Use the two-context classical core as a dual guide.**  The exact packet
  audit already identifies two A4 contexts hitting every collision-perfect
  classical alignment.  Ask whether their matrix-valued residuals dominate the
  ellipse rather than reconstructing all thirty context gauges.
- **Treat the four rectangle holonomies as the only nonclassical variables.**
  After exact A4 qutrit normalization and the biclique tree gauges,
  `atlas-a4-packet-four-rectangle-normal-form` leaves one `K_(2,2)` and three
  `K_(2,4)` rectangle holonomies on multiplicity wires.  A proof may therefore
  target a fixed four-unitary trace inequality for collision `19243`, rather
  than the full `20160 k` relative chart unitary.
- **Return the escaping point.**  Failure of a finite SOS relaxation should
  output an approximate point `(S,x12)` outside the ellipse together with the
  multiplicity mode realizing it; that is a targeted new packet-search input.
- **Universal tracial optimization is already refuted at value seventy-three.**
  `atlas-a4-root-ellipse-exact-tracial-escape` constructs an exact finite-factor
  common-frame solution of all thirty packet relations and `q_19243=1` with
  `(x01,x12,x23,x30)=(1,1,1,1)`, hence `F=73`.  Therefore an SDP/SOS search is
  relevant only if its axioms encode matrix embeddability rather than merely
  positivity and the exact trace relations.  Any relaxation valid for all
  finite tracial von Neumann algebras must admit this escaping point.
- **Amplification cannot dilute a blockwise counterexample.**
  `atlas-root-ellipse-is-amplification-concave` proves that the ellipse
  functional is positively homogeneous and concave in the four squared root
  energies.  Since those squared energies average under direct sums,

  ```text
  F(direct sum_j U_j) >= sum_j theta_j F(U_j).
  ```

  In particular every direct sum of nontrivial regular finite-quotient models
  still has `F>=1`; the scalar bound is sharp among binary nonzero energy
  patterns.  Thus an amplified finite-quotient escape cannot be hidden in
  favorable blocks.  This is a no-go for dilution, not construction of the
  presently unknown finite quotient and not the matrix-specific ceiling.
- **Exact matrix zeros are already finite-quotient tests.**
  `atlas-exact-matrix-zero-set-is-a-finite-quotient-test` applies Malcev
  residual finiteness to the finitely generated image of any exact
  finite-dimensional packet/collision model.  Such a model exists if and only
  if `Gamma_A4` has a nontrivial finite quotient, in which case a regular
  finite-quotient model has `F>=1`.  Therefore a bounded fixed-rank unitary
  search cannot find an exact escape of a genuinely new type.  Only an
  unbounded approximate matrix sequence can evade the finite-quotient fork.

  The arbitrary-matrix lower estimate `F>=3/128` at exact collision is already
  `atlas-root-energy-ellipse-controls-s3-distance`; another operator
  Cauchy--Schwarz/SOS derivation of the same direction would duplicate an
  established theorem.  The missing content remains the opposite strict upper
  ceiling, equivalently the positive joint residual gap.
