---
rg: 2
id: cubic-division-congruence-sc-from-two-sectors
kind: route
title: The congruence norm is the larger of the vector-sector and Gelfand--Graev-sector norms, so strong convergence of both sectors for one cubic division algebra gives the target
target: cubic-division-congruence-representations-converge-strongly
requires: [cubic-division-congruence-norm-splits-into-two-sectors, cubic-division-vector-sector-converges-strongly, cubic-division-gelfand-graev-sector-converges-strongly]
---

Take `D = D_7 = (K/Q, sigma, 2)` with `K = Q(2 cos 2pi/7)` and `sigma` a generator of `Gal(K/Q)`, a maximal
order `O_D`, `Gamma_D = SL_1(O_D)` and `P_D` as in the target.

1. **`D_7` is a central division algebra of degree 3 over `Q`.**
   - `K/Q` is cyclic of degree 3 and conductor 7.
   - At 2: `2` has order 3 in `(Z/7)^x / {+-1}`, so 2 is inert in `K`, and `v_2(2) = 1` gives local
     invariant `+-1/3`.
   - At 7: `K` is totally ramified, and `2` is not a cube mod 7 (the cubes are `1, 6`), so the norm residue
     symbol is nontrivial and the invariant is again `+-1/3`.
   - At every other prime `K` is unramified and `2` is a unit, so the invariant is 0.  At infinity the
     degree is odd, so it is 0.
   - The invariants sum to 0, so they are `1/3` and `-1/3`.  They have order 3, so `D_7` is a division
     algebra.  This agrees with the header of `experiments/cubic-division-sc/sc_p2.c`.
2. **Split.**  By `cubic-division-congruence-norm-splits-into-two-sectors`, part 1, for `p` not in `P_D`
   and every `z in C[Gamma_D]`, `||pi_p(z)|| = max(||sigma_p^0(z)||, ||GG_p(z)||)`.
3. **Both sectors.**  By `cubic-division-vector-sector-converges-strongly` and
   `cubic-division-gelfand-graev-sector-converges-strongly`, both terms of the maximum tend to
   `||lambda_(Gamma_D)(z)||`.  Hence so does `||pi_p(z)||`; this is the "if" half of part 2 of the
   splitting node.
4. **Existential target.**  The target asks for some `D`, and `D = D_7` is one.

The reduction loses nothing for `D_7`.  By part 2 of the splitting node, the target for `D_7` holds iff
both sector claims hold.
