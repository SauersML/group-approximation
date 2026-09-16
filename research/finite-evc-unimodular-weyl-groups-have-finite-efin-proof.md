---
rg: 2
id: finite-evc-unimodular-weyl-groups-have-finite-efin-proof
kind: route
title: Unimodularity makes the index of conjugates of C in cell stabilizers constant
target: finite-evc-unimodular-weyl-groups-have-finite-efin
requires:
  - finite-evc-model-restricts-to-commensurators
artifacts:
  - research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md
---

Full proof: Theorem 3 of `research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md`.
Put `N = N_G[C]`. By `finite-evc-model-restricts-to-commensurators`, `Y_C` has finitely many
`N`-orbits of cells, represented by `τ_1, ..., τ_m`, with `W_j = G_{τ_j} = N_{τ_j} ~ C`.

1. **Cells of `X^C`.** A cell of `X^C` has a virtually cyclic stabilizer containing `C`, so it
   lies in `Y_C`. The cells of `X^C` in `Nτ_j` are the `nτ_j` with `n` in
   `T_j = {n in N : n^{-1}Cn <= W_j}`. Their `N_G(C)`-orbits correspond to the double cosets
   `N_G(C)\T_j/W_j`.
2. **Injecting double cosets.** `N_G(C) n W_j ↦` the `W_j`-conjugacy class of `n^{-1}Cn`.
   - It is well defined, since `(mnw)^{-1}C(mnw) = w^{-1}(n^{-1}Cn)w`.
   - It is injective. If `n^{-1}Cn = w^{-1}n'^{-1}Cn'w`, then `n'wn^{-1}` normalizes `C`.
3. **Constant index.** With the generalized index `i(A,B) = [A:A∩B]/[B:A∩B]`, which is
   multiplicative and conjugation invariant,
   `[W_j : n^{-1}Cn] = i(W_j, C) · i(nCn^{-1}, C) = i(W_j, C) · Δ_C(n) = i(W_j, C)`.
   The finitely generated group `W_j` has finitely many subgroups of that index, so there are
   finitely many double cosets.
4. **Conclusions.**
   - `N_G(C)` has type `F_infinity`. For `K <= N_G(C)`, `KC` is a subgroup and
     `(X^C)^K = X^{KC}`. This is nonempty only if `KC`, hence `K`, is virtually cyclic, and it
     is then contractible. So `X^C` is a finite model for `E_𝒢 N_G(C)` for a family `𝒢` of
     virtually cyclic groups. Lück–Weiermann, arXiv:math/0702646, Proposition 5.1(ii) in its
     "finite type" form, applied to `TR ⊆ 𝒢`, gives a finite-type `E N_G(C)`: virtually cyclic
     groups have finite-type `E`, as in artifact item (F1'). This replaces an earlier appeal to
     Brown's criterion whose numbering was not verified.
   - `C` acts trivially, so `W = N_G(C)/C` acts on `X^C`. For `L <= W` with preimage `L~`,
     `(X^C)^L = X^{L~}`. If `L` is finite, `L~` is virtually cyclic and the fixed set is
     contractible. If `L` is infinite, `L~` is not virtually cyclic and the fixed set is empty.
     Hence `X^C` is a finite `E_FIN W`.
   - For `C = <c>`, `Z_G(c)` has index at most 2 in `N_G(C)`. Type `F_infinity` and finite
     `E_FIN` models pass to finite-index subgroups.
