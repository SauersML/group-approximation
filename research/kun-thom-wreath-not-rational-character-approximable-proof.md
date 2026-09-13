---
rg: 2
id: kun-thom-wreath-not-rational-character-approximable-proof
kind: route
title: A rational-character model is an approximation by a finite subgroup of a unitary group, which the wreath does not admit
target: kun-thom-wreath-is-not-rational-character-approximable
requires:
  - hilbert-embeddable-witness-impossible
---

Let `(F, rho, phi)` be a rational-character model on a window `S`, with
precision `eps`.

1. **Orthonormalize.** Orthonormalize `q`. Then `rho(F)` is a finite subgroup of
   `U(d)`, and `phi` composed with `rho` is `(S, eps)`-multiplicative in the
   normalized Hilbert--Schmidt norm.
2. **Separation.** For `s != e`, `||rho phi(s) - 1||_2^2 = 2 - 2 Re (1/d) Tr rho phi(s) >= 2 - 2 eps`.
3. **A witness.** So these models are approximations of `W` by finite subgroups
   of unitary groups in normalized Hilbert--Schmidt, with maximal separation.
   - The length `ell(k) = ||k - 1||_2` on the finite group `rho(F)` is
     conjugation invariant.
   - It is Hilbert embeddable, being the square root of the conditionally
     negative definite `1 - Re (1/d) Tr`.
   - So the models are Hilbert embeddable weak-soficity witnesses, with defect
     tending to `0` and separation near `sqrt 2`.
4. **Contradiction.** `hilbert-embeddable-witness-impossible` says `W` has no
   such witness (`W` is not in `C_FU`). QED
