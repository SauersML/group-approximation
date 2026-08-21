---
rg: 2
id: single-triangle-trace-cyclic-return-cell
kind: claim
title: Build one trace-cyclic proper-corner cell for the native Fanizza triangle
distinct_from:
  s3-active-packet-proper-corner-return: that places a three-atom allowed S3 sum into the recurrent carrier; this acts only on the one native Fanizza triangle chord after all tree incidences are normalized.
  schur-reynolds-one-overlap-actuator: that asks for one adjoint Reynolds overlap for every forbidden Schur packet; this asks for the fixed D8 holonomy projection of a single source-specific cycle.
---

OPEN.  Construct one finitely presented ordinary-group cell attached to the
last chord of the native Fanizza context triangle such that:

1. after fixed packet exactification **and using the prescribed native
   machine-word identities on the three separators**, the chord mismatch is
   the rational D8 group-algebra projection
   `H=(1-[R_F,R_G])/2`, or a fixed nonzero scalar multiple of it;
2. every finite-dimensional microstate decodes two block maps `X,Y` with the
   scalar trace estimates

   ```text
   |tr(YX)-tr(E)|+|tr(XY)-tr(E-H)| <= omega(def),      (STR1)
   ```

   where `omega(t)->0` and all carriers are the ones selected by the same
   triangle occurrence;
3. the exact gauge-covariant marked Fanizza representation, after countable
   amplification, extends across the cell by a one-sided Toeplitz/Hilbert-
   hotel realization; and
4. no relation turns `(STR1)` into a universal tracial identity in the group
   von Neumann algebra.

Finite-dimensional cyclicity gives `tr(YX)=tr(XY)`, hence

```text
tr(H) <= omega(def).                                   (STR2)
```

The exact canonical packet moment is `tr(H)=1/8`, so canonical matrix
microstates cannot satisfy vanishing defect.  Clause 3 keeps the mark
algebraically nonzero; clause 4 is the regular-representation firewall.

Because the native additive incidence graph has only one cycle, this cell is
source-specific and local.  It does not have to return an arbitrary BCS
atlas, synchronize a long computation, or provide a uniform family of
proper-corner gadgets.  What remains open is still genuine: ordinary group
words are invertible, so the one-sided maps must arise only after
finite-dimensional packet compression, not as literal group equations.

The triangle alone supplies no charge.  It is classically flat, with all
eight separator assignments extendible.  Hence clause 1 must fail if the
separator signs are treated as free Boolean variables.  The prospective
holonomy is a semantic machine-word/corner effect, not a contextuality proof
on the abstract three-cycle.

The global-Pauli shortcut does not remove this target:
`fanizza-pauli-guard-switches-off-at-the-terminal-cell` proves that the C18
parity guard fails exactly on the terminal HALT block.  Thus the chord is a
genuine part of the native source and its one proper-corner return is again
the load-bearing local theorem.
