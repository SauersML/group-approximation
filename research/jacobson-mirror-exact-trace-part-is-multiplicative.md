---
rg: 2
id: jacobson-mirror-exact-trace-part-is-multiplicative
kind: claim
title: Class-kill for wall-asymmetric traces of the Jacobson mirror fibre product - the mirror-exact part of a trace is multiplicative, so products, mixtures and ambient restrictions never create a head-seeing trace
distinct_from:
  jacobson-mirror-head-swap-kills-ambient-approximations: that kills approximations of an overgroup containing one wall swap that are asymptotically trivial on L_-, at the head only; this works with arbitrary traces of P (no triviality on L_- assumed), extracts their mirror-exact part tau^flat, shows it is constant on all of L_+ for every restriction from an overgroup with finitary site permutations, and shows tau^flat is multiplicative, so wall-asymmetric traces are inert under products and mixtures.
  bilateral-envelope-fuses-the-mirror-kernel-with-the-head: that shows a character of E whose pullback to P extends to <P,c> is trivial on L; this treats traces of P that are not pullbacks from E, and its survivor list ("approximations of P with trace 1 on L_- that are not restrictions") is refined here to the mirror-exact face, which products and mixtures cannot reach from the wall-asymmetric traces.
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that writes EL_n(J) = P/L_- with P LEF; this is the trace-level analysis of the quotient step, via the central projection onto L_--invariant vectors.
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that is the all-or-nothing statement for CE characters of E; this transports it to P and shows which traces of P can feed it.
  fell-models-inherit-walls-from-coefficients: that computes relative commutants of models tensored with the regular representation; this computes invariant vectors of tensor products of representations of a locally finite simple group, using that it has no nontrivial finite-dimensional unitary representation.
---

**ESTABLISHED** (route `jacobson-mirror-exact-trace-part-multiplicative-proof`).

**Notation.** As in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`.
- `E = EL_n(J) = GL_n(J)` with `n >= 3`, `P = E_+ x_(SL_n(A)) E_- <= H_bi` (LEF), and `E = P/L_-`.
- `L_+ = GL_fin(V_+) x {1}` and `L_- = {1} x GL_fin(V_-)`. Both are normal in `P`, and `L_+` maps isomorphically onto
  `L = GL_fin(V_+) <= E`.
- The head is `w = (x_13(Q),1) in L_+`; the mirror head is `w' = (1,x_13(Q)) in L_-`.
- A *trace* of `P` is a normalized, conjugation-invariant, positive definite function. It need not be extremal.
- `F_1 <= F_2 <= ...` is any increasing chain of finite subgroups with union `L_-`, for instance
  `F_j = GL(span{e_(k,i) : -j <= k < 0})`.

**(MX1) The mirror-exact part.** For every trace `tau` of `P` and every `g in P` the limit

```text
tau^flat(g) = lim_j  avg_(y in F_j) tau(y g)                                            (MX1)
```

exists and does not depend on the chain. In a GNS triple `(pi,H,xi)` it equals `<z pi(g) xi, xi>`, where `z` is the
projection onto the `L_-`-invariant vectors. The projection `z` is central in `M = pi(P)''`.
- `tau^flat` is positive definite, `P`-invariant, and constant on cosets of `L_-`. So it factors through `E`, with
  mass `m(tau) = tau^flat(1) = tau(z)`.
- If `tau` is CE and `m(tau) > 0`, then `tau^flat / m(tau)` is a CE character of `E`: it is the trace of the corner
  `zMz`.
- If `tau` is extremal, then `z` is `0` or `1`. So `tau^flat = tau` when `tau` is `1` on `L_-`, and `tau^flat = 0`
  otherwise. In general `tau^flat` is exactly the part of the extremal decomposition of `tau` carried by characters
  trivial on `L_-`, the *mirror-exact face*.

**(MX2) Reduction.** `E` is hyperlinear iff some CE trace `tau` of `P` has `tau^flat` nonconstant on `L_+`.
- Forward: take `delta_E` pulled back to `P`.
- Backward: apply Theorem JH to the CE character `tau^flat/m(tau)` at any point of `L_+` where it is not `1`.

**(MX3) Multiplicativity.** For all traces `tau_1, tau_2` of `P`,

```text
(tau_1 tau_2)^flat = tau_1^flat  tau_2^flat.                                            (MX3)
```

This rests on the representation identity `(H_1 (x) H_2)^(L_-) = H_1^(L_-) (x) H_2^(L_-)`. That identity holds because
`GL_fin(V_-)` is simple and contains `(Z/2)^k` for every `k`, so it has no nontrivial finite-dimensional unitary
representation. A nonzero `L_-`-invariant vector in `K_1 (x) K_2`, with `K_i` the complements of the invariants,
would be a Hilbert--Schmidt intertwiner, and that yields a finite-dimensional subrepresentation of `conj(K_1)`.

**(MX4) The inert class.** Let `N` be the set of traces `tau` of `P` with `tau^flat` constant on `L_+`. Equivalently,
`m(tau) = 0`, or `tau^flat / m(tau)` is trivial on `L` and so factors through `SL_n(A)`. Then:
1. **Closure.** `N` is closed under products, finite and countable convex combinations, complex conjugation, and
   composition with automorphisms of `P` that preserve `L_-` and `L_+`, including all inner ones.
2. **Wall-asymmetric traces are in `N`.** `N` contains every trace with no `L_-`-invariant vectors (`m = 0`). This
   includes `delta_P`, every extremal trace that is not `1` on `L_-`, and the rank characters
   `psi_a (x) psi_b` of `L_+ x L_-` extended by zero, with `psi_c(g) = 2^(-c rank(g-1))` and `b >= 1`. The last are
   wall-asymmetric when `a != b`, and they separate `w` from `w'`.
3. **Ambient restrictions are in `N`.** Let `G` be any group containing `P` and the finitary site permutations of
   `Z x {1..n}`, for example `H_bi`. Then `N` contains `sigma|_P` for every trace `sigma` of `G`. This is list-free: no
   classification of the characters of `GL(infinity,2)` is used. It covers the limit traces of all periodic finite
   models.
4. **Consequence.** Every trace of `P` built from members of `N` by products, tensor powers, direct sums, mixtures and
   conjugation lies in `N`, so its mirror-exact part is blind to the head. Wall-asymmetry of the ingredients does not
   help: a product `tau_1 tau_2` with `m(tau_2) = 0` has `(tau_1 tau_2)^flat = 0`, however asymmetric `tau_2` is.

**Invariant and death step.**
- **Invariant.** The mirror-exact functional `tau -> tau^flat|_(L_+)`.
- **Death step.** The tensor-invariant identity behind (MX3). The `L_-`-invariant part of a product is the product of
  the invariant parts, so the head-blindness of the factors carries over to the product.

**Survivor (the only open operation).** Pointwise limits.
- `m` is upper semicontinuous: `m(tau) = inf_j avg_(F_j) tau`. So a limit of traces in `N` might gain mirror-exact
  mass.
- `|tau^flat(g) - avg_(F_j) tau(y g)| <= (avg_(F_j) tau - m(tau))^(1/2)`. So if the convergence
  `avg_(F_j) tau -> m(tau)` is uniform in `tau`, then `tau -> tau^flat` is weak*-continuous and `N` is weak*-closed.
- That uniformity holds if the extreme characters of `GL(infinity,2)` are exactly `psi_k`, for
  `k = 0, 1, ..., infinity` (Skudlarek's list). It holds because `avg_(GL_N(F_2)) psi_k <= 8 * 2^(-N)` uniformly in
  `k >= 1`. This list is **not imported**: the graph cites only the countability statement of GKV
  (arXiv:1209.4945). So `N` being closed under limits is conditional.

**Impact on `agent-leavitt-not-bcs-negative-root-corner`.**
- **Calibration of the recorded next step.** The step "an approximation of `P` that is not asymptotically
  `s`-invariant, one that distinguishes the two walls" is necessary but not sufficient.
  - Wall-distinguishing CE traces exist trivially inside `N`, for example `psi_a (x) psi_b` extended by zero, if CE.
  - Such traces are inert: they cannot be combined with the LEF ambient traces, by any of the operations in (MX4), into
    a head-seeing trace.
- **The correct target.** A CE trace of `P` whose mirror-exact face, the part equal to `1` on `L_-`, charges the
  head. By (MX2) that is the hole itself. So wall-asymmetry is not an intermediate step.
- **What a construction must use.** A positive construction must produce mirror-exact mass by a limit process. The
  only open operation is the non-uniform pointwise limit, and it is closed too if Skudlarek's list holds.
- **The negative direction.** It is unaffected. `non-hyperlinear-group` stays OPEN.

DERIVATION
jacobson-mirror-exact-trace-part-multiplicative-proof
