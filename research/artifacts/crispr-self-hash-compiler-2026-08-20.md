# CRISPR / self-hash compiler: audited reduction

**Date:** 2026-08-20  
**Status:** the cyclic-trace and one-overlap reductions are proved; the
ordinary group actuator forcing the overlap remains open.  This artifact is
not a claim that a non-hyperlinear group has been constructed.

## Compressed architecture

Use the computable Fanizza BCS family rather than exposing a raw unbounded
Turing tape to a group microstate.  On a NONHALT instance its finite BCS
soundness already forces the native signal projection to vanish in every
near-perfect finite strategy.  The groupifier only has to compile one fixed
finite BCS at each source index; constants may depend computably on that
index.

For every forbidden context assignment, the Schur--Clifford rank compiler
creates a restriction-multiplicity jump.  On the adjoint Hilbert space this
is the established Reynolds gap

```text
tr_ad(R_A)-tr_ad(R_B)>=c_f q_f^2.
```

For one actuator `T=Ad_(U(t))`, define

```text
Theta=tr_ad(R_A T^*R_BTR_A).
```

Finite-rank geometry gives `Theta<=tr_ad(R_B)` and

```text
tr_ad(R_A)-Theta=||(I-R_B)TR_A||_(HS,ad)^2.
```

Therefore a single lower bound

```text
Theta>=tr_ad(R_A)-K eta
```

kills forbidden mass by `c_f q_f^2<=K eta`.  Expanding the Reynolds averages
expresses `Theta` as a finite average of squared normalized traces of the
ordinary words `a_1 t^-1 b t a_2`.  This is the literal self-hash: one finite
word-moment list authenticates whether the whole active Reynolds carrier
returned.

The reduction is syntactic, not a weakening of the geometric burden:
`tr_ad(R_A)-Theta` is exactly the squared HS mass of the part of `T range(R_A)`
outside `range(R_B)`.  A proof of the scalar inequality therefore controls
the entire average leakage, even though it need not establish termwise packet
covariance.

## What is gained

- spectator tensor amplification leaves every normalized adjoint rank and
  moment unchanged;
- no one-copy integer discrepancy is divided by ambient dimension;
- no full returned multiplicity atlas or termwise packet covariance is
  logically required;
- any computable vanishing modulus at the fixed Fanizza index suffices for
  reverse Kleene;
- the HALT witness may absorb the cell at infinite multiplicity and need not
  be tracial after groupification.

## Firewalls

1. A finite-group-only return is stationary and has regular finite models.
2. A bare ascending HNN extension of a hyperlinear base stays hyperlinear.
3. A universal tracial identity equating unequal carriers would also attack
   the exact witness and is not permitted.
4. The actuator must preserve context ownership and must not impose new
   commutations among original variables from different BCS contexts.
5. The current theorem is only the reduction to the scalar overlap.  No
   valid group relation forcing the overlap lower bound is yet known.
6. On a finite HNN edge the conditioned overlap follows the induced central
   character permutation exactly.  In the paired frame the hard carrier
   still escapes through `101<->011`; scalarization does not erase ownership.

## Primary next search

Search the existing S3/Schur, signed-Hecke, and Leavitt/Steinberg vocabularies
for a finite positive-semidefinite certificate whose expansion in fixed group
words gives the overlap lower bound.  Test the scalar moment directly before
attempting a stronger operator return.
