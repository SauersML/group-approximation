---
rg: 2
id: braided-v-max-n-above-lower-central-terms-proof
kind: route
title: Bounded-depth max-n for bV from graded noetherianity and downward induction on the lower central series
target: braided-v-max-n-above-lower-central-terms
requires:
  - proper-normal-subgroups-of-braided-v-lie-in-pure-part
  - braided-v-graded-pure-quotients-are-noetherian
artifacts:
  - research/artifacts/zp-braided-v-hopfian-2026-09-13.md
---

Artifact §6. Write `gamma_k` for `gamma_k(P_br)`.

1. A normal subgroup `N` of `V_br` containing `gamma_c` either equals `V_br` or lies in
   `P_br`, by `proper-normal-subgroups-of-braided-v-lie-in-pure-part`. It suffices to
   treat chains inside `P_br`.
2. For such `N` and `k < c`, let `N^(k) = (N ∩ gamma_k) gamma_{k+1} / gamma_{k+1}`. This is
   a `V`-invariant subgroup of `gr_k`, since `N` and `gamma_k` are normal in `V_br`.
3. Along a chain `N_1 <= N_2 <= …`, each chain `N_i^(k)` stabilizes by
   `braided-v-graded-pure-quotients-are-noetherian`. So there is `i_0` with all
   `N_i^(k)` constant for `i >= i_0` and `k < c`.
4. **Downward induction.** Let `H = N_{i_0} <= H' = N_i`. Then
   `H ∩ gamma_c = gamma_c = H' ∩ gamma_c`. Suppose `H ∩ gamma_{k+1} = H' ∩ gamma_{k+1}`, and
   let `x` be in `H' ∩ gamma_k`.
   - Since `H'^(k) = H^(k)`, there is `y` in `H ∩ gamma_k` with `x y^{-1}` in `gamma_{k+1}`.
   - Then `x y^{-1}` is in `H' ∩ gamma_{k+1} = H ∩ gamma_{k+1}`, so `x` is in `H`.
   - At `k = 1` this gives `H' = H`.
5. **Equivalence.** `V_br` is finitely presented, and a quotient by a normal subgroup `N`
   is finitely presented iff `N` is normally finitely generated. If `N` contains
   `gamma_c`, max-n above `gamma_c` makes `N` the normal closure of `gamma_c` and finitely
   many elements. This gives the stated equivalence with finite presentability of
   `V_br/gamma_c(P_br)`.
