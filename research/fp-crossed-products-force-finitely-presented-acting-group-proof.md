---
rg: 2
id: fp-crossed-products-force-finitely-presented-acting-group-proof
kind: route
title: Lift the configurations to a truncated presentation of the group, where the algebra relators still hold but a missing group relator fails
target: fp-crossed-products-force-finitely-presented-acting-group
requires: []
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
---

This is Theorem B of the artifact (Sections 1 and 3).

1. **Truncation.** Write `P = F(S)/N`. Let `n` bound the relator degrees as in
   `fp-crossed-products-force-sft-over-any-group-proof`, let `M = 2n`, let `N_M` be the normal
   closure of the elements of `N` of length `<= M`, and let `P_M = F(S)/N_M`. Words of length `<= n`
   agree in `P_M` iff they agree in `P`, so the `n`-balls of `P_M` and `P` are identified.
2. **Model.** Let `Z_M ⊆ A^(P_M)` be the set of configurations all of whose `n`-windows, transported
   through the identification, lie in `L_(B_n)(X)`. It contains `x∘π_M` for `x ∈ X`, so it is
   nonempty.
3. **Relators survive.** The monomial bookkeeping of the SFT route uses only group words of length
   `<= n`, whose coincidences are the same in `P_M` and `P`. So each relator vanishes in
   `LC(Z_M,k) ⋊ P_M`, and `E_a -> e_a`, `U_s -> u_([s])` defines `ψ_M` on `B_X`.
4. **Contradiction.** If `P` is not finitely presented, pick `w ∈ N \ N_M`. The element `U_w - 1`
   is `0` in `B_X`, hence `u_([w]_M) - 1 = ψ_M(U_w - 1) = 0`. But `[w]_M ≠ 1` and
   `LC(Z_M,k) ≠ 0`, so the `u_q` are independent, a contradiction. So `N = N_M` is the normal closure
   of finitely many words. `∎`
