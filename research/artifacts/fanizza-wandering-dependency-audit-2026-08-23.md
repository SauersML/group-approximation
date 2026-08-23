# Fanizza coherent-verifier wandering dependency audit

Date: 2026-08-23

This audit follows only the Fanizza high-cascade route and does not use the
Atlas or Bernoulli programs.

## Exact established cone

1. `two-copy-bcs-game-hamiltonian-dominates-fanizza-signal` constructs
   `0<=H_m<=1` and proves `D_R<=C_m H_m` in every nonmember representation.
2. `uniform-clock-reflection-block-encodes-game-hamiltonian` constructs the
   full clock/flag reflection `C=V_m`, proves `C^2=1`, and proves only the
   first-corner identity `Q(1-C)Q=H_m Q`.
3. `fanizza-coherent-verifier-wandering-promotion` asks an infinite-order
   word `w` to reproduce that first corner in canonical matrix models.
4. The former downstream routes treated `QCQ` as a reflection in the `Q`
   corner and invoked the finite-order compression telescope.

Step 4 is not a consequence of Steps 1--3. The exact correction is

```text
QCQ=(1-H_m)Q,
QC(1-Q)CQ=H_m(2-H_m)Q.
```

Thus `QCQ` is a corner reflection exactly when `H_m=0`. The full reflection
returns through the complementary clock/flag space whenever losing energy is
present.

## Consequences for the cascade

- The abstract theorem
  `compressed-reflection-kills-even-cesaro-mark` remains correct, but its
  Fanizza specialization did not meet the hypothesis `V=QVQ`, `V^2=Q`.
- `fanizza-compression-implies-localized-square-return` is invalid: squaring
  the first compression discards the nonzero complementary excursion.
- `fanizza-wandering-dirichlet-return-route` is invalid: a one-step
  Dirichlet comparison does not control the powers used by its Cesaro sum.
- The open coherent-verifier wordization target is not refuted, but it is no
  longer load-bearing by itself. A repaired route needs either a genuinely
  reducing returned carrier or a separate weighted-state estimate for all
  excursions.

## Direct construction attempt

For each clock value, the selected representation has the controlled
involution

```text
c_j=1-e_(jj)+e_(jj)((1-L_j)+L_jX).
```

These involutions commute and their product is exactly `C`. This is the
single native finite-lamp word supplied by the two established ingredients,
but it has order two. If the controls are imposed as finite packet
relations, wandering is lost; if they are merely chosen in the HALT
representation, canonical microstates are not constrained. Therefore the
current ingredients alone do not synthesize the requested wandering Hecke
word. The sharp missing datum is a payload-coupled robust rule that controls
the complementary excursion while preserving an infinite normal form.
