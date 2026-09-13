- **Next test for `p >= 3`: invariant models violate even the single-element law** (w7-v-cycle-c3; artifact
  `research/artifacts/p-cycle-tree-rank-models-and-ternary-gate-2026-09-12.md`, Section 2; candidate
  `p-cycle-tree-invariance-cannot-force-order-char-law`). Held OPEN until `w3-vf-linear` re-derives it.
  - **The models.** `rho_m([g]) = exp_m(lambda(g) u)` in `L[u]/(u^m)` for `1 <= m <= p`, with `L = F(t_i)` and
    `lambda(tau_i) = t_i`. `rk_m` is the normalized `L`-rank. For `p = 2` and `m = 2` this is the model of
    w7-v-cycle-c2's Section 3.
  - **Coherent.** `rk_m` is invariant under every injective endomorphism, prefix refinement and disjoint-support
    endomorphisms included. For `m = 2` over `F_p` it is an ultralimit of generic dimension-2 quotients of the
    `A/m^2` models above.
  - **Not the law.** For `2 <= m < p`, `rk_m((1 - [g])^j) = max(m - j, 0)/m`, which is not `(1 - phi)(p - j)/p` for
    any `phi`. So for `p >= 3` invariance fails to force the profile of a single cycle, not only the joint fixed rank.
  - **Every allowed profile occurs.** Mixtures of `rk_1, ..., rk_p` realize every drop sequence that Proposition
    4.2(b) above allows. So (b) together with coherence inside the `p`-group gives nothing sharper.
  - **First premise broken.** For `2 <= m < p`, induce to the wreath configuration `E_p ⋊ <s>`, with `s` a clopen
    `p`-cycle permuting the supports. `s` gets the regular profile and `tau_1` the profile of `u`, which breaks
    single-element `V`-conjugacy. For `m = p` single elements agree, and only the joint fixed rank rules it out.
