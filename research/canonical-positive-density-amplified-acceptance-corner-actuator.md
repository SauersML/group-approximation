---
rg: 2
id: canonical-positive-density-amplified-acceptance-corner-actuator
kind: claim
title: Charge one arbitrary return word by an amplified acceptance block on a fixed canonical corner
distinct_from:
  acceptance-return-is-one-corner-word: That identifies the remaining analytic coefficient as one capacity-gated corner-word norm; this asks ordinary relations to charge an externally prescribed return word by that coefficient.
  canonical-positive-density-hs-power-overlap-return: That controls many powers of one return word; this asks for one selected compression of one arbitrary ambient word.
  capacity-gated-common-source-gram-word-cell: That decodes a common Fanizza source and all context intertwiners; this uses the already block-encoded cyclic game contraction and asks only for one amplified return coefficient.
---

Fix a Culf--Mastel game with finite-matrix cyclic acceptance norm
`rho<1`, and fix its authenticated rational packet idempotent `q` with
canonical trace `tau(q)=alpha>0`.  Given a prescribed integer `L` and an
ambient unitary group word `r`, construct effectively a finite ordinary-group
extension such that:

1. the packet subgroup remains embedded and `tau(q)=alpha`; the selected
   trace does not depend on `L`;
2. every canonical-profile normalized-HS microstate, after packet
   exactification, satisfies

   ```text
   ||q r q||_2^2 <=(alpha+o(1))rho^(2L)+o(1);          (ACA1)
   ```

3. whenever the ambient perfect model has `r q=q r=q` and the game has its
   perfect acceptance carrier, that model extends exactly with `q!=0`.

Only the selected corner is to be identified with the amplified acceptance
block.  A global relator `r=W_game^L` is not allowed: the block encoders need
not satisfy the ambient cycle relations away from `q`, and global equality
would generally destroy perfect completeness.

## Attempts

- `acceptance-return-is-one-corner-word` and
  `pauli-zero-atom-removes-acceptance-source-deficit` already reduce the
  one-cycle analytic loss to one positive-density corner coefficient.  They
  do not make that coefficient an ordinary relator payment.
- Repeating the fresh-control block encoder `L` times with independent
  controls proves `(ACA1)` only on a head whose trace decays exponentially
  with `L`.  That violates clause 1 and can cancel the gain `rho^(2L)`.
- Reusing the same controls keeps `alpha` fixed but permits amplitude to
  leave and return, so the compression of the repeated unitary is not the
  `L`-th power of the acceptance contraction.
- Finite-cocycle SELECT synchronizes the controller gauge for one one-shot
  norm, but its payload list must obey a finite cocycle law and its own exact
  finite-character models return with full mass.  It therefore does not
  supply the amplified actuator.
- **Use one-shot control leakage instead of returning a high power.**
  `finite-control-acceptance-leakage-is-a-zero-corner-sum` proves that for an
  ideal finite-control block unitary `W`, zero-control atom `P_0`, and the
  control flips `X^a`, unitarity gives the exact identity

  ```text
  sum_(a!=0)||P_0 X^a W P_0||_2^2
    =tau(P_0)-||P_0 W P_0||_2^2.                       (ACA2)
  ```

  Hence a strict head compression would force a fixed one-cycle leakage
  floor, and finitely many selected zero-compression cells would be enough;
  no power amplification would remain.  This does not yet groupify the
  Culf--Mastel verifier.  Its `W_game` is a left--right superoperator acting
  on one tracial Gram vector.  The corners in `(ACA2)` are therefore
  superoperator-vector coefficients, not ordinary matrix corners of group
  words.  `controlled-swap-wordizes-matrix-corner-without-adjoint-dilution`
  proves that replacing the Gram vector by the positive-density left module
  charges vectors which an exact perfect model need not fix.  Moreover
  `doubled-controllers-do-not-preserve-game-gap` shows that independent
  multiplicity orientations can interleave between the acceptance tests and
  make the dressed product have norm one.  Thus `(ACA2)` is a valid analytic
  shortcut only after the same common-source, orientation-synchronized
  wordization which is missing from the selected-corner actuator.
- The viable object must be a payload-sensitive, selected Hecke-corner
  relation: it may be exact on the distinguished perfect corner and
  quantitatively sound only in matrices.  A functorial tracial corner
  identity would also hold in the regular representation and is too strong.
