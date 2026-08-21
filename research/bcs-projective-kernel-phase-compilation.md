---
rg: 2
id: bcs-projective-kernel-phase-compilation
kind: claim
title: A tracial non-RU BCS can be compiled so one predicate commutator is a negative projective-kernel phase
distinct_from:
  phase-safe-toric-gap-game-exists: that asks for the finished toric game and normal-closure certificate; this is the source-engineering step that puts a designated finite-gadget word in the tracial GNS projective kernel.
  boolean-predicate-central-phase-word: that supplies the local finite phase reader for any predicate; this must couple it equivariantly to the violation structure without adjoining selector shifts that destroy the BCS constraints.
  finite-packet-central-sign-cannot-enforce-nonlinear-support: that proves the finite packet by itself has unwanted marked irreducible sectors; this claim can only survive through payload-coupling relations which prevent every such sector from extending to the full compiled presentation.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

Engineer the fixed Fanizza/Paddock--Slofstra BCS and attach the finite gadget
of `boolean-predicate-central-phase-word` so that one designated word `W`
satisfies, in a perfect tracial model,

```text
pi_tau(W)=-I,                                               (PKP1)
```

while every finite-dimensional approximate model with `W` near `-I` pays a
uniform BCS/LCS energy gap.  The completion must be equivariant for the
**violation projection family**: conjugate partners may permute or count
forbidden atoms, but may not map a satisfied context relation to a violated
one while that relation is imposed as zero.

The compiled presentation must also prove that the central phase survives the
normal closure of the game clauses.  A perfect tracial representation of the
full universal algebra is an acceptable certificate.  No selector sector is
deleted; violation density is read through the projective phase.

## Exact audit of the proposed finite-packet construction

The currently recorded ingredients do **not** establish this claim.  The word
from `boolean-predicate-central-phase-word` has the desired nonlinear sign only
in its chosen assignment-coordinate representations.  It does not have that
sign rule on every irreducible representation of the finite packet.  In fact
`finite-packet-central-sign-cannot-enforce-nonlinear-support` proves the exact
opposite global statement: every character of the commuting selector subgroup
compatible with the marked central sign occurs in some irreducible packet
representation.  Thus adjoining the finite packet and imposing only its group
table leaves forbidden selector sectors with the same marked sign.

Gowers--Hatami stability cannot remove those sectors: they are exact
finite-dimensional representations, so their packet defect is already zero.
Likewise, the raw projective GNS kernel supplies phase safety but not the
finite-dimensional gap, by
`non-ce-trace-does-not-promote-to-subgroup-character-gap`.  Consequently a
valid proof here must exhibit explicit **payload-coupling relations** and prove
both of the following statements:

1. the selected tracial BCS representation extends across those relations
   with `W=-I`;
2. every marked finite-dimensional representation of the full coupled
   presentation decodes to a BCS tuple with quantitatively comparable robust
   energy.

Neither statement follows from the local phase calculation, finite-group
stability, or non-Connes-embeddability alone.  No such coupled presentation or
decoder is presently specified, so the claim remains open rather than
established or refuted.

## Attempts

- Insert the unitriangular phase word into the fixed Fanizza predicate menu and
  search its tracial GNS representation for a central `-1` lift.
- Permit conjugate partners only when they permute forbidden atoms and preserve
  total violation projection. A naive Weyl selector shift fails this test.
- A candidate satisfying `(PKP1)` without a full universal-algebra model does
  not certify normal-closure survival and is rejected before toric compilation.
- The standalone finite-packet attachment is ruled out: induction supplies
  exact forbidden marked sectors, and stability has no defect on which to act.
  Any further attempt must couple the infinite BCS payload so those sectors do
  not extend, while proving the quantitative decoder demanded above.
- Cross-context scalar buses do not provide that coupling.
  `scalar-bus-packet-couplings-retain-all-global-assignments` proves that
  assignment-coordinate sectors with the marked predicate phase glue around
  every finite amalgam/HNN graph whenever all edge restrictions are scalar.
  Cross-amplification equalizes their dimensions and makes cyclic holonomy
  vacuous.  Hence the first genuinely new relation must act nonscalarly on
  the assignment sectors, or constrain edge intertwiners through a two-cell;
  adding more central selector/phase identifications cannot close the claim.
- Diagonal trace powers do not preserve the full GNS tensor algebra, by
  `diagonal-tensor-trace-powers-forget-full-gns-tensor`; even their proposed
  raw indicator limit fails on nontrivial unit phases.  They therefore do not
  automatically preserve the non-CE payload needed here.
- Free labels erase every payload moment only while the labels remain
  uncancelled.  `free-label-orthogonalization-erases-payload-trace` shows that
  adjoining enough label data to recover the original observables restores
  the entire payload trace and destroys the claimed canonical-free joint
  distribution.  This is not the required selective payload coupling.
- The claimed Shulman stable-double trace shortcut is a citation error, as
  recorded in `shulman-symmetric-double-has-no-stable-trace-upgrade`.
  arXiv:2603.13564v2 proves operator-norm MF of a symmetric amalgam of an MF
  algebra, not MF-ness of every hyperlinear trace on a double of an
  Hilbert--Schmidt-stable algebra.
