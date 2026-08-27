---
rg: 2
id: kazhdan-almost-invariant-corner-proof
kind: route
title: Lazy Kazhdan averages keep positivity and contractivity, then cut the spectrum at one half
target: kazhdan-almost-invariant-corner-near-invariant-projection
requires: []
---

Write `xi = P / sqrt d`, a unit vector in the Hilbert space `HS(H)`
carrying the unitary representation `Ad pi(g) : X -> pi(g) X pi(g)^*`.
By `(KA1)`, `max_s || Ad pi(s) xi - xi || <= eta`.

**Step 1 (nearest invariant vector).**  Let `P_inv` be the orthogonal
projection of `HS(H)` onto the `Ad pi(Gamma)`-invariant vectors, i.e.
onto `pi(Gamma)' cap HS(H)`.  For a Kazhdan pair `(S, kappa)` one has
`|| xi - P_inv xi || <= (1/kappa) max_s || Ad pi(s) xi - xi || <= eta / kappa`
(Bekka--de la Harpe--Valette Prop. 1.1.9: `xi - P_inv xi` lies in the
orthocomplement of the invariants and has the same displacement as `xi`).

**Step 2 (realize it by averages).**  Let
`M = (1/2)(1 + |S|^(-1) sum_(s in S) Ad pi(s))`.  `M` is self-adjoint on
`HS(H)` (`S` symmetric), fixes invariant vectors, and on their
orthocomplement has spectrum in `[0, 1 - kappa^2/(4|S|)]`: indeed for a unit
vector `zeta` there, `<M zeta, zeta> = 1 - (1/(4|S|)) sum_s || Ad pi(s) zeta - zeta ||^2
<= 1 - kappa^2/(4|S|)` since some `s` has `|| Ad pi(s) zeta - zeta || >= kappa`, and `M >= 0` as the lazy half-sum of a contraction with
the identity.  Hence `M^k xi -> P_inv xi` in `HS`-norm.  Each `M^k` is a
convex combination of maps `X -> u X u^*` with `u` unitary, so
`M^k(P)` is a positive operator of operator norm at most `1`, and
`HS`-convergence implies strong convergence, under which positivity and
`|| . ||_op <= 1` pass to the limit.  Therefore

```text
Q := sqrt(d) P_inv xi  is a positive contraction in pi(Gamma)',
|| Q - P ||_HS <= (eta / kappa) sqrt d =: delta sqrt d.             (KA3)
```

**Step 3 (spectral cut).**  Put `D = Q - P`; then `|| D ||_op <= 2` and
`Q^2 - Q = PD + DP + D^2 - D`, so `|| Q^2 - Q ||_HS <= 5 delta sqrt d`.
For real `x`, `| 1_([1/2, infinity))(x) - x | <= 2 | x^2 - x |`
(check `x < 0`: `|x| <= 2|x|(1+|x|)`; `0 <= x < 1/2`: `x <= 2x(1-x)`;
`1/2 <= x <= 1`: `1 - x <= 2x(1-x)`; `x > 1`: `x - 1 <= 2x(x-1)`).  With
`E := 1_([1/2, infinity))(Q)` the functional calculus gives
`|| E - Q ||_HS <= 10 delta sqrt d`, hence `|| E - P ||_HS <= 11 delta sqrt d`,
the first line of `(KA2)`.  `E` is a spectral projection of the compact
positive operator `Q` away from `0`, hence finite rank, and commutes with
`pi(Gamma)` as a function of `Q`.

**Step 4 (rank).**  For projections `E, P`,
`|| E - P ||_HS^2 = Tr E + Tr P - 2 Tr(EP) >= | Tr E - Tr P |` because
`Tr(EP) <= min(Tr E, Tr P)`; so `| d' - d | <= 121 delta^2 d`, the second
line of `(KA2)`.

**Step 5 (partial isometry).**  Let `X = E P = W |X|` be the polar
decomposition, `|X| = (PEP)^(1/2)`.  Since `0 <= PEP <= P` and
`|| PEP - P ||_HS = || P(E - P)P ||_HS <= 11 delta sqrt d`, and
`0 <= 1 - sqrt y <= 1 - y` on `[0, 1]`, `|| |X| - P ||_HS <= 11 delta sqrt d`.
Also `|| X - P ||_HS = || (E - P)P ||_HS <= 11 delta sqrt d`, and `W = W P`
(initial space inside `ran P`), so
`|| W - P ||_HS <= || W(P - |X|) ||_HS + || X - P ||_HS <= 22 delta sqrt d`.
`W` maps `ran P` into `ran X subseteq ran E`.  The condition `eta < 1/22`
only guarantees `22 delta < 1` when `kappa = 1`; in general it is
cosmetic, the estimates hold for every `eta`.

**Step 6 (compression).**  For any `g`,
`|| E pi(g) E - P pi(g) P ||_HS <= || (E - P) pi(g) E ||_HS + || P pi(g) (E - P) ||_HS
<= 22 delta sqrt d`, which is the last assertion after dividing by `sqrt d`.
