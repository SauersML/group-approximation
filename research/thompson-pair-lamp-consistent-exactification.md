---
rg: 2
id: thompson-pair-lamp-consistent-exactification
kind: claim
title: Anchor and transport two-point lamp words below the involution threshold
distinct_from:
  operator-norm-finite-state-rounding: that asks for a finite exact joint-character support for the whole even-lamp module with controlled actor covariance; this asks only that the two-point lamp words be anchored to one exact involution family and transported by each actor generator, and only below fixed constants.
  finite-presentation-must-expose-whole-module-with-uniform-defect: that asks for a modulus tending to zero for all-pairs module multiplication before rounding; this asks for constant thresholds on two-point lamps only, and consumes the involution dichotomy instead of a modulus.
  thompson-even-lamp-fp-finite-state-detector: that is the exact finite-dimensional triviality theorem for the Thompson even-lamp group; this is the approximate-model hypothesis that would let the exact theorem be applied to corona coordinates.
artifacts:
  - research/artifacts/finite-memory-pair-kernel-audit-2026-08-23.md
---

OPEN.  Fix a finite presentation of

```text
Gamma_state = I_X rtimes V,
```

a base pair `(x_0,x_1)` in the Thompson orbit `X`, the lamp generator
`b=b_(x_0,x_1)`, and for every pair `(x,y)` an actor word `g_(x,y)` with
`g_(x,y)(x_0,x_1)=(x,y)`.  Put

```text
w_(x,y) = g_(x,y) b g_(x,y)^(-1).
```

Prove that there are a finite relator set `R` and `delta>0` such that every
finite-dimensional unitary tuple `U` with `Def_R(U)<=delta` admits an exact
homomorphism `rho:I_X->U(d)` into commuting involutions with

```text
sup_(x != y) ||rho(b_(x,y)) - w_(x,y)(U)||_op <= 1/2,          (PLC1)
```

and such that each actor generator transports the pair words,

```text
sup_(x != y) ||U_s w_(x,y)(U) U_s^* - w_(s x,s y)(U)||_op
    <= eta < 1.                                                (PLC2)
```

Both suprema are over **all** pairs, including pairs whose transporter words
grow with the matrix dimension.  That quantifier is the whole problem: for a
fixed pair, `(PLC1)` and `(PLC2)` follow from a finite van Kampen diagram.

**Why the constants suffice.**  If `rho(b_(x,y))=I` then `(PLC1)` gives
`||w_(x,y)(U)-I||<=1/2`, `(PLC2)` gives `||w_(s x,s y)(U)-I||<=1/2+eta`, and
`(PLC1)` again gives

```text
||rho(b_(s x,s y))-I|| <= 1+eta < 2.
```

Since `rho(b_(s x,s y))` is an exact involution, it equals `I`.  So the pair
kernel is actor-invariant and
`thompson-pair-kernel-invariance-kills-even-lamps` makes `rho` trivial; by
`(PLC1)` every pair word satisfies `||w_(x,y)(U)-I||<=1/2`.  In a norm matrix
corona the image of a lamp is an exact involution, so its distance from `1` is
`0` or `2`; a bound of `1/2` therefore forces it to be `1`.  No modulus
tending to zero is needed anywhere.

**Why this is not the whole-module gate.**  `(PLC1)`--`(PLC2)` concern only
two-point lamps and only fixed constants, whereas
`finite-presentation-must-expose-whole-module-with-uniform-defect` asks for
all-pairs module multiplication with a modulus `omega(delta)->0`.  The
reduction of the witness shape from an arbitrary module word to a two-point
lamp is the surviving content of the finite-memory pair-kernel memo.

**Falsifier.**  A model with `Def_R(U)->0` whose pair words are incoherent at
moving addresses — for instance a stabilizer-holonomy ladder accumulating
along transporters `g_(x_n,y_n)` of growing length — refutes `(PLC1)`.  No
such construction exists yet, and the same object would refute
`finite-presentation-must-expose-whole-module-with-uniform-defect`.

## Attempts

- **Ask instead for the pair-kernel jump `J_n(s)` to stay below `2` for every
  exact correction of the model (the memo's `thompson-moving-pair-return-checksum`).**
  Refuted: `exact-lamp-lifts-admit-moving-pair-kernel-jumps` twists any lift by
  the parity character of a finite window and produces `J_n(s)=2` at every
  coordinate in dimension `2`, for a model of defect exactly zero whose lamp
  corona classes are all trivial.  An exact lift is pinned by the corona only
  at fixed module elements.  Anchoring `(PLC1)` to the model's own word
  evaluations is exactly what kills that twist.
- **Ask only that some exact correction have an invariant pair kernel.**  Then
  `rho=1` is admissible precisely when the lamps already die, so by
  `thompson-pair-kernel-invariance-kills-even-lamps` the hypothesis and the
  conclusion coincide — a restatement, not a reduction.
- **Use pointwise corona covariance.**  It handles every fixed pair and says
  nothing about a pair chosen after the coordinate; a tail partition makes the
  fixed-pair implication eventually vacuous while moving witnesses persist
  (same node, variant construction).
- **Address the challenges by literal conjugation.**
  `conjugacy-addressed-opnorm-challenges-are-lossless` gives
  `||(a^(-1) r a)(U)-I||=||r(U)-I||`, so a remote *conjugate of one relator*
  costs nothing.  But a pair lamp has many names, and passing between two
  names introduces a stabilizer word whose length grows with the address.
  `(PLC1)` is precisely the demand that this holonomy stay below the
  involution threshold; it is not supplied by conjugacy addressing.
- **Use the depthwise operator-norm lemma.**
  `depthwise-opnorm-collapse-implies-mf-radical` permits an arbitrary finite
  constant `C_N` at each fixed depth `N`, but requires the bias `b_N->0` for
  one fixed mark.  The moving witness is chosen after the coordinate, so no
  fixed finite window contains all witnesses and the quantifier order does not
  match.  Using it needs a return theorem transporting every moving pair back
  to one of finitely many depth-`N` prototypes with address-independent error.
- **Invoke uniform Ulam stability of Thompson groups.**  Blocked by
  `corona-defect-is-not-uniform`: a corona representation supplies pointwise,
  not uniform, multiplicative defect, which is exactly the hypothesis such
  theorems need.  The distinction is the same pointwise-versus-uniform gap as
  `(PLC1)` itself.
- **Replace the approximate argument by an exact corona invariant.**
  `norm-matrix-corona-has-no-proper-isometries` is available and bypasses
  rounding entirely, but the projections a presentation produces exactly in a
  corona are finite-subgroup character projections, which is the existing
  finite-order/rank-monodromy lane rather than a finite-memory engine.
