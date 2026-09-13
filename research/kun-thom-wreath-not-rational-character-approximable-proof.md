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
     conjugation invariant, and `ell(a^-1 b) = ||a - b||_2`.
   - **`ell` is Hilbert embeddable** in the convention of
     `hilbert-embeddable-length-hyperlinearity`, where the kernel
     `(a, b) -> ell(a^-1 b)` must be conditionally negative definite.
     - `psi(a, b) = ||a - b||_2^2` is a squared Hilbert distance, hence
       conditionally negative definite.
     - `ell(a^-1 b) = psi(a, b)^(1/2)`, and `t -> t^(1/2)` is a Bernstein
       function: `t^(1/2) = c ∫_0^∞ (1 - e^(-s t)) s^(-3/2) ds` with `c > 0`.
     - Each `1 - e^(-s psi)` is conditionally negative definite by Schoenberg's
       theorem, since `e^(-s psi)` is positive definite with `1` on the
       diagonal. Positive combinations stay conditionally negative definite.
     - So `ell` itself is conditionally negative definite. It is bounded by `2`
       and has defect at most `eps` and separation at least `sqrt(2 - 2 eps)`.
       After dividing by `2` it is a witness.
   - **Second route (ex-verify2-quantum-l2, 2026-09-13).** The witness notion
     refuted by `hilbert-embeddable-witness-impossible` allows one `n`-independent
     increasing `f` with `f(0) = 0`, continuous at `0`, such that `f o ell` is
     Hilbert embeddable and bounded by `1`
     (`hilbert-embeddable-witness-for-kun-thom-wreath`).
     - Take `f(t) = t^2/4`: `f o ell = psi/4` is a squared Hilbert distance over
       `4`, with defect at most `eps^2/4` and separation at least `(1 - eps)/2`.
     - This argument needs no Bernstein-function input.
   - **Wording note.** A 2026-09-13 correction said `ell` "need not be"
     conditionally negative definite, only its square. That sentence is false:
     square roots of conditionally negative definite kernels are conditionally
     negative definite, as shown above. The conclusion was unaffected, and both
     routes stand.
4. **Contradiction.** `hilbert-embeddable-witness-impossible` says `W` has no
   such witness (`W` is not in `C_FU`). QED
