---
rg: 2
id: char-uniform-v-rank-firewall-proof
kind: route
title: Evaluate every expression of a uniform argument over C and apply the von Neumann rank
target: char-uniform-identities-cannot-force-v-rank-triviality
requires: []
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md
---

Artifact Section 3.

1. **Von Neumann values** (Theorem 3.1).
   - For `g` of order `n`, the spectral idempotents `e_zeta = (1/n) sum_j zeta^(-j) u_g^j` have trace `1/n`,
     because `tau(u_h) = 0` for `h != 1`. `q(u_g)` kills exactly the `e_zeta` with `q(zeta) = 0`.
   - For infinite order, the spectral measure at `delta_1` is Haar measure, so finite spectral sets have trace `0`.
2. **Firewall** (Corollary 3.2). Put `rho(E) = rk_vN(E~)` on expressions evaluated in `R[V] ⊆ C[V]`.
   - Sylvester premises hold because `rk_vN` is a rank function.
   - Uniform equalities hold because they hold in `R[V]`.
   - Single-element conjugacy data hold because the values depend only on `q` and `ord(g)`.
   - The conclusion `rho(1 - [g]) < 1 - 1/ord(g)` contradicts step 1.
3. **Examples** (Corollary 3.3). `(1 - u_s)^p` is nonzero on the eigenspaces `zeta != 1`, so `(1 - [s])^p = 0` is not
   uniform.
4. **Tools** (Corollary 3.4). The values of step 1, with `a = phi_V = 0`, satisfy the conclusions of the torsion law,
   the fixed-rank identification, uniform displacement and wandering freeness. `l^2(V)` has no invariant vectors,
   and `tau(e_chi) = 1/|P|` on finite abelian `P`.

Import at statement level: the trace of the range projection is a Sylvester matrix rank function on `C[G]`
(standard von Neumann dimension theory).

*Verification by `w3-vf-linear` (2026-09-12), Section 31.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Re-derived: `tau(e_zeta) = 1/n` and the Haar spectral measure; (U1)-(U3) for `rho(E) = rk_vN(E~)`; `(1 - u_s)^p != 0`. Every Corollary 3.4 instance lifts: exact isotypic idempotents over `Z[1/p, zeta_p]` with `p != char F`, and `rk_vN col(1 - u_(s_i)) = 1`.*
