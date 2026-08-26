---
rg: 2
id: growing-multicut-el20-order-seven-inheritance
kind: claim
title: Transport one reservoir gauge around seven moving coefficient-sensitive cuts
distinct_from:
  finite-coordinate-el20-active-cut-inherits-order-seven-anchor: that asks for one positive common cut reducing both order-seven heads and is refuted by the exact zero-cut commutator; this permits a different cut at every intermediate iterate.
  order-seven-first-exit-is-not-seven-step-leakage: that disproves control from one first-exit operator; this asks for all seven separately typed transition boundaries.
  el20-order-seven-heads-force-zero-common-hecke-reducing-cut: that forbids one common invariant signed-Hecke corner; this deliberately does not produce one.
---

**OPEN MOVING-CUT ORDER-SEVEN COMPILER.**  Work in an arbitrary
operator-norm matrix model of

```text
G=EL_20(L_(F_2)(1,2))
```

on the positive-density active core of the surviving mark.  Construct one
positive initial source `E_0` and, for each native row `i=1,2`, projections

```text
E_(i,0)=E_0,E_(i,1),...,E_(i,6),E_(i,7)=E_0           (GMC1)
```

such that the order-seven head `T_i=J_iv_i` carries each stage to the next
with total normalized-Hilbert--Schmidt boundary loss tending to zero:

```text
sum_(k=0)^6 ||(1-E_(i,k+1))T_iE_(i,k)||_2=o(1).       (GMC2)
```

At every stage authenticate the transported label factor and the **same**
multiplicity involution `D_i`, rather than seven unrelated gauges.  The
seven compressed factors must therefore multiply to

```text
M_i^7 tensor D_i^7=1 tensor D_i+o_2(1),               (GMC3)
```

while the literal elementary-group relation gives the identity.  Since
`D_i^2=1`, conclude `D_i=1+o_2(1)`.

Here **same** must mean equality in the fixed Hecke reservoir frame, not
merely that the seven gauges are transported or unitarily conjugate copies
of one involution.  By
`moving-order-seven-stage-gauges-have-coboundary-drift`, the
natural moving-frame telescope otherwise produces

```text
D_(i,6)...D_(i,0)
```

and this product can be the identity for seven conjugate nontrivial
involutions.  Equivalently, the construction must prove asymptotic
commutation of the initial discrepancy with the reservoir holonomy, or an
equally strong fixed-frame synchronization theorem, before `(GMC3)` is
available.

The initial cut `E_0` must retain the two unequal native selector meanings,
the common-source Hecke factorization, and the mixed Pauli gauge locks.  It
must have a fixed positive fraction of the active core.  Intermediate cuts
may depend on the row and matrix coordinate and need not lie in the signed
Hecke character source.

This is the sharp survivor after the zero-common-cut theorem.  Merely taking
`E_(i,k)=T_i^kE_0T_i^(-k)` makes `(GMC2)` tautological but does not prove the
stagewise occurrence typing or constancy of `D_i`; those are the substantive
coefficient-sensitive requirements.  No Property `(T)`, Kazhdan input,
canonical trace, or literature theorem is permitted.

## Attempts

- **The six-exit operator telescope is complete.**
  `six-exit-moving-cut-seventh-power-telescope` proves, for arbitrary moving
  projections, that the seven-factor compressed product differs from
  `E_0T^7E_0` by at most the sum of the six intermediate transition exits,
  or by `sqrt(6)` times their total squared energy.  Thus `(GMC2)` has no
  hidden analytic multiplication loss.  The remaining content is entirely
  coefficient-sensitive: retain a positive typed initial source and prove
  that the stage transitions carry one fixed-frame reservoir gauge.

- **There is no separate abstract mass-extraction hole after a full-Gram
  bridge.**  The signed Hecke source already has fixed positive mass.  A word
  satisfying `(ESB1)--(ESB2)` in
  `el20-six-moving-coefficient-square-bridges` transports that whole source
  to the next moving cut and keeps its reservoir factor trivial; its six
  conjugates preserve the mass automatically.  Together with the established
  six-square gauge lock, this is exactly the missing positive-mass mechanism.
  What is not known is the ordinary EL20 coefficient word with those full
  source/range Grams and ungauged typing.  Merely selecting lower spectral
  mass cannot replace it.

- **The paid Reynolds cut supplies a genuine first moving source row, but
  only under its honest detector alternative.**
  `paid-cut-has-moving-hecke-source-or-detector` conjugates the actual signed
  source by the frozen paid Whitehead word.  Either one conjugated detector
  pays at least `1/2`, or a positive support of mass at least
  `3tau(P_z)/31744` lies in the resulting moving source; undoing the
  conjugation and applying either literal `u_i` then has exactly zero source
  boundary.  The incompatible-character commutator simultaneously forces
  `10epsilon_1+4epsilon_2>=sqrt(tau(R_0))`, so this cut cannot be the common
  cut forbidden above.  This closes one initial mass/ordinary-row step, not
  the compiler: the detector branch is not a relator defect, and the next
  moving transition still needs a full-Gram ungauged occurrence in the fixed
  Hecke frame.

- The tautological orbit choice `E_(i,k)=T_i^kE_0T_i^(-k)` has zero
  transition boundary, but it does not authenticate the coefficient label at
  any intermediate stage and allows seven independent multiplicity gauges.
  `moving-order-seven-stage-gauges-have-coboundary-drift` gives an exact
  finite-packet model of this ambiguity: even with zero leakage and the
  initial chart fixed, intermediate chart changes can realize
  `(D_0,D_1,D_2,...,D_6)=(V,V,1,...,1)`.  The needed new input is therefore
  a named family of full-EL20 coefficient intertwiners fixing all six chart
  transitions, not merely seven separate occurrence typings.
- Saturating one signed-Hecke cut under both heads cannot work: the exact
  EL20 commutator identity forces every such common reducing cut to be zero.
- The fixed marked/Fano atom is a genuine finite packet, but on that packet
  both selector scales are `1/1`; it is orthogonal to the signed source and
  cannot retain the unequal selector meanings needed by the decoder.
- Moving through the nonconstant Fano orbit does not repair the typing.
  `fano-moving-packet-retains-actor-holonomy` tensors the full seven-pair
  Schrodinger packet with the regular representation of its finite actor
  group.  All moving boundaries vanish and the signed source has positive
  mass, but the common reservoir return is an arbitrary order-seven actor
  holonomy rather than the native/Hecke involution `D_i`.
- What remains is a coefficient-sensitive growing atlas which retypes every
  transition while transporting one multiplicity involution around the
  whole seven-cycle in the **fixed Hecke frame**.  A transported-conjugacy
  construction is not enough: the moving-stage gauge fence gives an exact
  seven-dimensional reservoir in which all moving boundaries vanish, all
  stages have the right label matrix, and all gauges are conjugates of one
  involution, but their norm product is one while the involution is
  nontrivial.  `six-ungauged-moving-squares-lock-seven-gauges` gives a sharp
  quantitative endpoint: six parallel ungauged coefficient bridges and
  their mixed squares force all stage gauges to agree.  The concrete word
  problem is isolated in `el20-six-moving-coefficient-square-bridges`; no
  such full-Gram bridge is currently known.
- The exact gauge model
  `order-seven-moving-cuts-realize-both-affine-profiles` also installs the
  two precise positive-sign fractions forced by the quarter and eighth
  selector rows.  Both affine covariances, both seventh-power telescopes,
  and all moving boundaries can therefore be exact while the two initial
  gauges remain nonconjugate.  Taking the native head itself as each
  parallel bridge makes every mixed square tautological.  This rules out an
  operator-norm or polar argument based only on the actual order-seven heads;
  the independently ungauged occurrence typing in the six-bridge claim is
  load-bearing.
- Recentering the Pauli center to `x_(18,19)(q)` does make the marked overlap
  reduce both order-seven heads, so there is no moving-cut boundary.  It
  instead enlarges the native label algebra by the two center-chain hub
  pairs.  `recentered-order-seven-heads-have-actor-holonomy` tensors the
  resulting finite `GL_5(F_2)` actor subgroup by its regular representation:
  `T_i^7=1` then constrains only `(D_iE_i)^7`, where `E_i` is the independent
  gauge of `v_i`, while `D_i` remains a nontrivial involution.  Thus even
  this zero-boundary recentering still needs an ungauged typing of the
  center-chain factor.
