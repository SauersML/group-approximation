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

- The tautological orbit choice `E_(i,k)=T_i^kE_0T_i^(-k)` has zero
  transition boundary, but it does not authenticate the coefficient label at
  any intermediate stage and allows seven independent multiplicity gauges.
- Saturating one signed-Hecke cut under both heads cannot work: the exact
  EL20 commutator identity forces every such common reducing cut to be zero.
- The fixed marked/Fano atom is a genuine finite packet, but on that packet
  both selector scales are `1/1`; it is orthogonal to the signed source and
  cannot retain the unequal selector meanings needed by the decoder.
- What remains is a coefficient-sensitive growing atlas which retypes every
  transition while transporting one multiplicity involution around the
  whole seven-cycle. No construction or finite countermodel is currently
  known.
