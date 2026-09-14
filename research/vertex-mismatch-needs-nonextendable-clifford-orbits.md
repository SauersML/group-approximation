---
rg: 2
id: vertex-mismatch-needs-nonextendable-clifford-orbits
kind: claim
title: Stable-vertex MF-trace models of an infranormal Kazhdan double need an uncancellable non-extendable mismatch
distinct_from:
  stable-vertex-mf-trace-models-need-inequivalent-marginals: that proves the Kazhdan marginals must be inequivalent; this proves the inequivalence cannot be repaired by small padding and must sit on Clifford orbits that do not extend.
  kt-double-stable-vertex-mf-trace-models: that is the open existence question; this sharpens the only shape it can take.
---

ESTABLISHED.  Keep the hypotheses of
`stable-vertex-mf-trace-models-need-inequivalent-marginals`, and assume also that
`Gamma` is infranormal in `G`.  Let `K_n` be the closure of
`{(pi^1_n(g), pi^2_n(g))}` in `U(d_n) x U(d_n)` and let `L_n` be the closure of
the image of `Gamma`.  Then:

1. **`L_n` is normal in `K_n`**, and the multiplicity functions of
   `pi^1_n|_(L_n)` and `pi^2_n|_(L_n)` are `K_n`-invariant.  So their
   difference `Delta_n` is constant on `K_n`-orbits of irreducible
   representations of `L_n`.
2. **Mismatch size.**  `mu_n = sum_omega |Delta_n(omega)| dim(omega)
   <= 2 (delta_n/epsilon)^2 d_n`.
3. **No small cancellation.**  Suppose representations `rho^1_n, rho^2_n` of
   `G` of total dimension `m_n` make `(pi^1_n + rho^1_n)|_Gamma` and
   `(pi^2_n + rho^2_n)|_Gamma` equivalent.  Then `m_n/d_n` does not tend to `0`
   along any subsequence.
4. **Extendable orbits cancel cheaply.**  Call an orbit extendable if its
   irreducibles extend to their inertia groups in `K_n`.  The part of
   `Delta_n` on extendable orbits is cancelled by representations of `G` of
   dimension at most `mu_n`.

So at every large stage some Clifford orbit carries a nonzero mismatch whose
irreducibles do not extend to their inertia groups; the obstruction classes
live in `H^2(S/L_n, U(1))` for the inertia groups `S`.  The total cost of
cancelling the mismatch is not `o(d_n)`.
