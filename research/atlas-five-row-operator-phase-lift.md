---
rg: 2
id: atlas-five-row-operator-phase-lift
kind: claim
title: Five saturated Atlas rows lift nonlinear phase defect to linear covariance energy
artifacts:
  - experiments/atlas_five_row_phase_finite_screen.py
distinct_from:
  atlas-linear-energy-controlled-by-full-packet-defect: that asks to control the sum of all 234 linearized boundary rows by all 234 nonlinear defects plus the interior separator; this keeps only the five rows already certified to saturate the covariance tangent kernel.
  atlas-boundary-tangent-covariance-coercivity: that bounds covariance by the five linearized rows and is already global in the chart unitary; this asks for the missing nonlinear-to-linear comparison for those rows.
  atlas-a4-holonomy-coherence-gap: that exact-regular local-network ceiling is refuted by the multiplicity-two frame; this includes the full-atlas interior consequence which the local frame does not satisfy.
  atlas-independent-phase-incidence-is-not-coercive: that frees the twenty-seven phase-edge occurrences from the common conjugation orbit and gives an exact private-edge counterexample; this retains the orbit identities and asks whether they restore coercivity.
  atlas-five-row-lift-failure-dichotomy: that proves exact finite zero screening sees only the macroscopic failure branch and isolates the additional normalized blow-up branch; this asks to exclude both branches by one uniform inequality.
---

**OPEN.**  Let

```text
J={0,11,30,44,55}                                     (FPL1)
```

be the five first-boundary indices whose integral derivatives already have
the full `H=GL_3(2)`-fixed kernel.  For each `j in J`, write

```text
l_j(U)=||rho(z_j)U||_2,                               (FPL2)
```

with the fixed integral row `z_j in Z[A8]`, and let

```text
e_j(U)=||pi_U(s_j)-1||_2,
e_int(U)=||pi_U(c_19243)-1||_2.                        (FPL3)
```

Prove one multiplicity-independent constant `C_5<infinity` such that every
relative chart unitary `U in U(20160k)` satisfies

```text
sum_(j in J) l_j(U)^2
 <= C_5 [sum_(j in J)e_j(U)^2+e_int(U)^2].             (FPL4)
```

This is the smallest presently certified finite operator-valued phase
inequality sufficient for the strict two-`S3` ceiling.  The left side is a
five-row quadratic form in the common relative unitary; the right side
contains the corresponding five nonlinear transported-phase products and
one interior commutator.  No local representation-type variable remains.

It is also already a direct goal-level obstruction.  As proved in
`nonhyperlinear-directly-from-five-row-phase-lift`, hyperlinearity of the
Leavitt unit group supplies regular relative-chart models whose six
nonlinear defects tend to zero while the five-row linear energy stays
bounded away from zero.  Thus `(FPL4)` by itself proves that explicit group
non-hyperlinear; the downstream two-`S3` packet is unnecessary for that
implication.  This sharpens rather than resolves the claim: proving `(FPL4)`
is already proving the desired finite HS separation.

## Exact-model audit

The known multiplicity-two frame does not refute `(FPL4)`.  It is exact on
the thirty shortest A4 context rows and on collision `19243`, but those are
not the five first-boundary words `(FPL1)` together with the full-atlas
interior commutator.  Its refutation of
`atlas-a4-holonomy-coherence-gap` therefore cannot be transferred to this
claim or to `atlas-two-s3-energy-ceiling-below-19243-floor`.

The characteristic-two affine boundary model is the relevant calibration:
it kills all 234 boundary defects while retaining positive covariance, but
the interior commutator is nontrivial.  Thus it proves that `e_int` cannot be
deleted from `(FPL4)` and supplies a finite lower bound on any admissible
constant; it does not make the right side vanish.

## Exact 27-phase reduction

Transport the second chart through the certified classical alignment.  For
`x in A8` put

```text
Phi_x(U)=rho(x) U rho(x)^*.
```

If `(u_jr,v_jr)` are the prefix immediately before and after the `r`-th
second-chart syllable of `s_j`, literal multiplication gives

```text
pi_U(s_j)=prod_r Phi_(u_jr)(U) Phi_(v_jr)(U)^*,
rho(z_j)U=sum_r (Phi_(u_jr)(U)-Phi_(v_jr)(U)).          (FPL5)
```

The five rows have respectively `3,4,4,4,4` such phase edges, hence nineteen
in total.  The transported interior commutator is an alternating
sixteen-syllable word and contributes eight more.  Thus `(FPL4)` is exactly
the following finite 27-phase assertion, uniformly over `k` and
`U in U(20160k)`:

```text
sum_j ||sum_r (Phi_(u_jr)-Phi_(v_jr))||_2^2
 <= C_5 [sum_j ||prod_r Phi_(u_jr)Phi_(v_jr)^*-1||_2^2
          +||Q_int(U)-1||_2^2].                       (FPL6)
```

Here `Q_int` is the fixed eight-edge product read directly from
`c_19243`.  Equivalently, the infimum of the right side of `(FPL6)` divided
by its left side, over every multiplicity and every point with positive left
side, must be positive.  An exact countermodel would therefore be five closed
phase cycles and the closed interior cycle with at least one nonzero additive
circulation.

This reduction also isolates the important caveat: excluding common zeros
in each fixed finite dimension does **not** prove the required uniform
amplified gap.  The infimum could still tend to zero as `k` grows.

## Six-relator quotient compression firewall

All nineteen boundary phase endpoints lie in the transported copy of
`H=GL_3(2)`.  If the six ordinary relators identified the two labelled
copies of `H`, four fixed bridge fillings would prove `(FPL4)` by direct
telescoping, as recorded in
`atlas-six-relator-bridge-filling-proves-five-row-phase-lift`.

That sufficient condition is refuted.  All six words lie in the genuine
Leavitt kernel, while the two faithful `A8` charts in the exact Leavitt
quotient intersect trivially.  Hence every nontrivial `H` bridge survives
the universal six-relator quotient.  The desired estimate, if true, must be
a finite-regular-margin phenomenon; it cannot be a van Kampen consequence
of these six relations.

There remains an equally sharp negative side.  Any finite quotient of
the six-relator group which injects both marked `A8` factors and separates an
`H` bridge yields, in its left regular representation, an exact amplified
countermodel: all six nonlinear defects vanish while five-row coercivity
makes the linear energy positive.  Thus the exact algebra already forces a
bridge escape; the unresolved question is whether that escape occurs in a
finite regular-margin quotient or only in infinite representations.

## Bounded exact finite screen

`experiments/atlas_five_row_phase_finite_screen.py` replays three exact
screens over `F2` and uses coefficient collisions, not floating point, for
regular-representation linear energies.

* On the stored multiplicity-two `GL8(2)` frame, collision `19243` and hence
  `c_19243` are identity, but all five boundary values are nonidentity; each
  has `rank(w_j-1)=2`.  After regularization the five linear energies are
  `6,8,8,8,8`, while the five nonlinear energies sum to `10`.  This gives the
  exact calibration `C_5 >= 38/10=19/5`, not a countermodel.
* The stored collision-zero `GL5(2)` fourteen-core frame fails all five rows.
  The stored twenty-two-row frame kills row `0` and fails the other four.
* Exhausting all `20,160` inner `A8` relative frames finds exactly one point
  killing the five boundary rows: the classical frame, where all five linear
  rows vanish.  Its interior commutator is nonidentity, so no inner frame
  kills all six words.

These computations are finite evidence only.  They neither exhaust arbitrary
relative unitaries nor supply the multiplicity-uniform positive infimum in
`(FPL6)`.

## Why this is still nonlinear

For one row, the exact atlas word is a product of transported relative
phases, whereas `rho(z_j)U` is their signed sum.  Ordinary telescoping bounds
the product by the sum in the opposite direction.  Reversing it in
normalized Hilbert--Schmidt norm cannot follow from a Taylor remainder,
because products of two HS-small terms need operator-norm control.  The
interior commutator must rule out precisely the large noncommutative phase
cancellations which survive the five boundary products.

## Attempts

1. **Telescope the five products.**  This proves the reverse inequality,
   bounding each nonlinear defect by a sum of phase increments.  Reversing
   it loses operator norm on the quadratic cross terms and is unavailable in
   normalized HS norm.
2. **Delete the interior row.**  The exact characteristic-two affine model
   kills all five boundary products while retaining positive linearized
   energy, so a boundary-only inequality is false.
3. **Use the exact A4 coherence transducer.**  It losslessly identifies the
   three local phase sectors, but a multiplicity unitary remains free around
   a cycle.  The unresolved operation is to make `c_19243` pay that one
   operator-valued loop phase rather than only its scalar character.
4. **Use only the six phase-cycle incidences.**  Refuted by
   `atlas-independent-phase-incidence-is-not-coercive`.  Two private edges
   of row `11` carry cancelling signs, while one private interior edge
   absorbs the fixed interior fold.  All six multiplicative holonomies then
   vanish but the row-11 additive circulation has norm four.  Hence a proof
   must use the common-orbit identities `P_x=lambda(x)Ulambda(x)^*`, not just
   unitarity and the cycle products.
5. **Use a determinant or Fredholm index of the common orbit.**  Refuted by
   `atlas-phase-cycle-determinant-is-gauge-trivial`.  Every phase edge has
   determinant one identically, and scalar rotation of the relative gauge
   changes `det U` arbitrarily while leaving all multiplicative holonomies
   and all singular values of the additive circulations unchanged.  Square
   phase differences have index zero; rectangular stacking only records the
   fixed source-target dimension difference.  Any finite-only invariant must
   therefore retain relative singular-subspace information rather than a
   determinant or index.
6. **Quotient the gauge and use the aligned transverse Hessian.**
   `atlas-aligned-quotient-spectrum-cannot-reach-low-defect` proves that the
   nonzero aligned quotient spectrum is indeed a finite, multiplicity-uniform
   irrep-pair calculation.  But `c_19243` keeps every low-defect frame at
   distance at least `sqrt(2)/16` from the whole aligned commutant manifold.
   Hence this favorable local spectrum cannot see the relevant sequence; a
   surviving singular invariant must be global on the remote nonlinear branch.
7. **Classify exact zeros in finite quotients.**
   `atlas-five-row-lift-failure-dichotomy` proves that this sees only the
   macroscopic failure branch.  Even if every fixed multiplicity had no
   exact positive-energy zero, `(FPL4)` could fail along a sequence with
   additive energy `eta_n^2 -> 0` and nonlinear residual `o(eta_n)`.  After
   dividing by `eta_n` this gives a unit vector in a Hilbert-ultraproduct
   blow-up cone.  Excluding that cone requires a global multiplicity-uniform
   estimate on the remote low-defect branch; it is not a finite exact
   zero-set calculation.
