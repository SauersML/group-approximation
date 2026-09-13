---
rg: 2
id: labbe-full-group-finite-small-growth-models-are-trivial-proof
kind: route
title: Limits of small-growth models are standard, so balls look orbital, and orbital charts would build a periodic Wang tiling
target: labbe-full-group-finite-small-growth-models-are-trivial
requires:
  - labbe-full-group-small-growth-actions-are-standard
  - zd-derived-full-group-fp-forces-finite-type
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

The full derivation is in the artifact, Sections 3 and 4. Only the generators `s(pi, e)` and Lemma 0 of
`zd-derived-full-group-fp-forces-finite-type-proof` are used from the second required claim.

**Chart lemma.** For every `rho` there is `r_1(rho)` such that isomorphic rooted labelled `r_1`-balls at
`x, x' ∈ Omega_U` force `x|B(rho) = x'|B(rho)`.
- A 3-cycle on a small clopen `D ∋ x` avoiding `x'` separates the stabilisers of `x` and `x'`.
- A ball of radius `r` determines `St(x) ∩ B_r`.
- Compactness finishes, because each condition `wy = y` is clopen.

**Corollary B.**
1. Suppose bad `(O_i, v_i)` exist with `n_i -> ∞`. Pass to `St(v_i) -> K` in `Sub(F(S))`.
2. By exactness, `K` contains every conjugate of every trivial word, so `Y = F(S)/K` is a `Gamma`-set with
   `|B_k| <= C k^2`.
3. By `labbe-full-group-small-growth-actions-are-standard`, `B_r(K)` is trivial or orbital.
4. The ball type is determined by `K ∩ B_{2r+1}`, so the same holds for `v_i` with `i` large. This is a
   contradiction.

**Theorem C.** Let `R_2 >= R_1 + 2`, let `L` bound the `S`-lengths of the `s(pi, e)`, and put
`r_* = r_1(R_2) + 2L`.
1. **Invariant set.** `O_mov`, the set of vertices with non-trivial balls, is invariant.
2. **Charts.** `chi(v) = x|B(R_2)` for any `x` with `B_{r_*}(v) ≅ B_{r_*}(x)`.
3. **Moves.** `T_e v = s(chi(v), e) v`. The chart lemma on `B_{r_* - L}` gives `chi(T_e v) = (sigma^e x)|B(R_2)`.
   Also `T_{-e} T_e = id`.
4. **Commuting.** `T_{e_1} T_{e_2} = T_{e_2} T_{e_1}`, since both words lead to `sigma^{e_1+e_2} x`.
5. **Tiling.** `y(u) = chi(T^u v_0)(0)` has every neighbour pair legal, so `y ∈ Omega_U`. It is invariant under
   a finite-index lattice, contradicting aperiodicity. So `O_mov = ∅`.

**Assembly.** Apply Corollary B with `r = r_*`, then Theorem C. ∎
