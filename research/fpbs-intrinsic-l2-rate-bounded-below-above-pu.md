---
rg: 2
id: fpbs-intrinsic-l2-rate-bounded-below-above-pu
kind: claim
title: On every nonamenable Cayley graph with p_u < 1 the intrinsic-radius l2 rate is positive at p_u
refuted_by:
  - fpbs-l2-at-pu-kills-intrinsic-rate-and-stretch
distinct_from:
  fpbs-benjamini-schramm-universal: that is p_c < p_u; this is the strictly stronger p_Lambda < p_u. Since p_c <= p_(2->2) <= p_Lambda by fpbs-intrinsic-l2-rate-closed-zero-set, it can fail on a graph that has a window
  fpbs-nonamenability-bounds-critical-connectivity-operator: that bounds the full kernel at p_c from above; this bounds the exponential rate of truncated kernels at p_u from below, and the only critical input needed is sharpness, which is already established
  fpbs-uniform-chemical-stretch-above-pu: that is a geometric sufficient condition for this claim; this is the operator statement actually used by the route
---

**OPEN.**

Notation and definitions as in `fpbs-intrinsic-l2-rate-closed-zero-set`: `T^(R)_t(u,v) = P_t(d_omega(u,v) <= R)` and
`Lambda(t) = lim_R R^(-1) log ||T^(R)_t||_(2->2)`.

**Claim (IL2).** Let `G` be a Cayley graph of a finitely generated nonamenable
group with `p_u(G) < 1`. Then `Lambda(p_u) > 0`.

**Equivalent forms**, using the ESTABLISHED items 2 and 5 of
`fpbs-intrinsic-l2-rate-closed-zero-set`:

- `p_Lambda < p_u`;
- `inf_(t > p_u) Lambda(t) > 0` (`Lambda` is nondecreasing and right-continuous);
- there are `epsilon, delta > 0` with `Lambda >= delta` on `(p_u, p_u+epsilon)`.

The last form is the one that must be proved. It asks only for estimates in the
uniqueness phase, and right-continuity carries them down to `p_u` itself.

**Why it can fail on its own.** (IL2) implies `p_c < p_u`, but not
conversely. A graph with a window could still have `Lambda(p_u) = 0` if the
intrinsic balls at `p_u` grow subexponentially in `l2`. For example, the
chemical stretch of the unique cluster could blow up as `t ↓ p_u`, while
`theta(p_u) > 0` or the window `(p_c,p_u)` persists. The strict inequalities
`p_c <= p_(2->2) <= p_Lambda` are not decided here.

**Calibration.** On `T_d`, `p_Lambda = 1/sqrt(d-1) < 1 = p_u`. The claim
excludes `p_u = 1` because then `p_c <= 1/gr < 1 = p_u` already. The bound
`p_c <= 1/gr` holds because `chi(t) >= sum_v t^(d(o,v))`, which diverges for
`t > 1/gr`, and `chi < infinity` below `p_c` by Lemma 3.1 of
`fpbs-intrinsic-l2-rate-closed-zero-set-proof`.

## Attempts

1. **Uniform chemical stretch (2026-09-17).** The route
   `fpbs-intrinsic-l2-rate-via-uniform-stretch` reduces this claim to a
   uniform linear chemical stretch constant just above `p_u`. Where that
   stalls is recorded in the Attempts of
   `fpbs-uniform-chemical-stretch-above-pu`.
2. **Refuted on tree products (2026-09-18, swarm-0917-w10-w10-bs-break,
   calibration).**
   - **Result:** `fpbs-l2-at-pu-kills-intrinsic-rate-and-stretch`
     (ESTABLISHED) proves the claim is false.
   - **Mechanism.** Item 3 of
     `fpbs-intrinsic-rates-log-lipschitz-in-parameter` gives
     `Lambda(t) <= max(0, log(t/p_(2->2)))`. So this claim implies
     `p_(2->2) < p_u`, quantitatively `p_u >= p_(2->2) e^(Lambda(p_u))`.
   - **Counterexample.** Hutchcroft--Pan, arXiv:2412.15895v1, Theorem 1.2,
     prove `p_(2->2) = p_u` on `T x Z^d` (`k >= 3`, `d >= 1`), imported as
     `fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu`. There
     `0 < p_c < p_u < 1`. It is a Cayley graph of `(Z/2)^{*k} x Z^d`, and for
     `k = 4` of `F_2 x Z^d`. On it `Lambda(p_u) = 0`.
   - **Reading.** The claim fails on graphs that do have a window. So it was a
     prerequisite that can fail on its own, as its own "Why it can fail"
     paragraph anticipated.
   - **Consequences for the route.**
     - (UCS) and the averaged ball hypothesis are refuted on the same graphs,
       with `K_*(t) >= log(gr)/(2 log(t/p_u))`.
     - Only (IL1) survives in `fpbs-universal-intrinsic-l2-rate-route`.
     - Any proof of (IL1) must avoid every `l2` pairing of truncated kernels.
       Such a pairing would prove this claim.
   - **Cross-node.** On any graph with `p_u < 1` and an infinite amenable
     normal subgroup, this claim contradicts Claim E of
     `fpbs-relative-threshold-is-quotient-l2-threshold` (its item C2).
