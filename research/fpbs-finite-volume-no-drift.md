---
rg: 2
id: fpbs-finite-volume-no-drift
kind: claim
title: Finite-volume no-drift, on Cayley graphs a summable Green function of the pushed DT boundary measure forces the quotient l2 threshold, so the Green and l2 thresholds of the pushed measure coincide
distinct_from:
  fpbs-relative-dt-green-threshold-splits-identity-e: that proves p^Q <= p^G and that E is (E-a) and (E-b) together; this is the open equality (E-b) alone.
  fpbs-nonunimodular-level-sets-break-identity-e: that computes the l2 and diagonal thresholds on nonunimodular level sets; the transitive analogue of this statement fails there on the whole window (p_c, p_t), so any proof of this must use the Cayley symmetry tau(x^(-1)) = tau(x).
  fpbs-quotient-dt-threshold-is-quotient-l2-threshold: that proves the l2 (spectral radius) certificate of the pushed DT measure has threshold p^Q; this asks that the weaker return-rate certificate have the same threshold.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is Claim E; this is strictly weaker (it drops relative DT sharpness), and is equivalent to E on every pair where (E-a) holds.
---

**OPEN.**

**Statement (E-b).** Let `G = Cay(Gamma, D)`, `N` an infinite normal
subgroup, `Q = Gamma/N`. With the notation of
`fpbs-relative-dt-green-threshold-splits-identity-e`,

```text
p^G(N;G) = p^Q_(2->2)(N;G).
```

By item 7 of that node, this says: whenever some finite `S` has
`D_p(S) = sum_k (mu_{S,p}^{*k} * a_S)(e_Q) < infinity`, every `p' < p` has
some finite `S'` and `eps > 0` with
`sum_n (mu_{S',p'} + eps a_{S'})^{*n}(e_Q) < infinity`. That is, a finite
return certificate survives, after a small decrease of `p`, the insertion of
the `S`-mass between steps of the chain.

**Why it matters.** Item 6 of the split node: under (E-a), the type (ii)
pairs of C1 of Claim E are exactly the failures of (E-b) at `p_c`. A pushed
critical DT measure would return to `e_Q` at exponential rate below one
while its `l2(Q)` spectral radius is at least one. That is a drift in the
return chain which no finite ball removes.

**Known cases.** `Q` trivial or amenable (item 4 of the split node), and
every class where Claim E is ESTABLISHED: tree Cayley graphs, free products
along commuting quotients, and complete-block free products.

## Attempts

**Calibration off Cayley graphs (2026-09-20, swarm-0917-w23-w23-bs-follow).**
Item 8 of the split node: on `T_k` with the horocycle `L` of an end, the ball
`B_R` at `p in (1/(k-1), 1/sqrt(k-1))` has pushed measure of mass
`p^(R+1) k (k-1)^R`, which tends to infinity. Since `(k-1)^Z` is amenable,
that mass is its `l2` spectral radius. Its Laplace value at the half tilt is
`Phi_R(p) = (p sqrt(k-1))^(R+1) (2 + R(k-2)/(k-1))`, which tends to `0`. So
the transitive analogue of (E-b) fails there on the whole window, while that
of (E-a) holds.

**Invariant and where a proof must use Cayley structure.** The invariant is
the gap between the return rate and the `l2(Q)` spectral radius of
`mu_{S,p}`. For a symmetric finitely supported measure on a group, these
coincide (Kesten: the return rate of a symmetric walk is its spectral
radius). The pushed DT measure is not symmetric even on Cayley graphs:
`nu_{S,p}(g)` weights the outer endpoint of a boundary edge by the
connection probability of the inner endpoint. The Cayley input that makes
`sigma^N_p` symmetric is `tau(x^(-1)) = tau(x)` (item (0d) of the sandwich
proof), and it is exactly what fails on the horocycle, where
`sigma_p(c^(-1)) = c sigma_p(c)`. So a proof of (E-b) must transfer the
symmetry of `sigma^N_p` to some finite-volume symmetrization of `mu_{S,p}`
without changing its return rate. In symbols, with the reflection
`mu~(q) = mu(q^(-1))`, `mu^{*k}(e_Q) <= ||rho_Q(mu)||^k`, and
`||rho_Q(mu)||^2` is the return rate of the symmetric measure `mu * mu~`
(Kesten). A drift is a strict gap `r(mu)^2 < r(mu * mu~)`. On the horocycle
this gap is the tilt: `mu` is concentrated at low heights with weights
`(k-1)^n`, `mu * mu~` is not, and the half tilt `c^(1/2)` is what
symmetrizes `sigma_p` there. On a Cayley graph `sigma^N_p` is already
symmetric, but `mu_{S,p}` need not be, and nothing on the board transfers
the symmetry. Not proved (reframing only).
