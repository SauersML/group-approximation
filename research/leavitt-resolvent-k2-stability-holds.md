---
rg: 2
id: leavitt-resolvent-k2-stability-holds
kind: claim
title: For every N >= 3, K_2(N,R_L) -> K_2(R_L) is an isomorphism, so K_2(N,R_L) = Q^x on the symbols {λ,N+1}, it is central in St_N(R_L), and St_N(R_L) has solvable word problem
distinct_from:
  st-n-leavitt-resolvent-word-problem-reduces-to-k2: that reduces the word problem of St_N(R_L) to injective stability (i) and a computable detector (ii); this proves (i), and (ii) is already proved.
  k2-central-in-steinberg-groups-of-leavitt-resolvent-ring: that asks whether K_2(N,R_L) is central for N >= 5; this proves it for every N >= 3.
  leavitt-resolvent-frame-complex-route-to-injective-stability: that is the route; this carries it out, including the sign step.
---

**ESTABLISHED** through `leavitt-resolvent-k2-stability-holds-proof`. Refereed: gq-referee-b PASS, citation and scope lens (report 740389fd9, W1--W4 applied); proof-gap
review by gq-referee-a pending.
- The group-theoretic core is Khanh's Steinberg comparison argument (arXiv:2609.08428, proof of Theorem
  `thm:raw-criterion`, read in TeX), run for `E_n(R_L)` and modulo a central subgroup.
- Khanh's Borel-construction presentation is used as he verifies it directly through the path groupoid
  (khanh.tex l. 458--460); Brown is not needed.
- GE enters through `leavitt-ge-rings-have-stable-k1-at-rank-three`, pinned in Ara--Goodearl--Pardo
  (math/0111066v1, Theorems 1.6 and 2.4), which cite Menal--Moncasi (not read).
- No priority is claimed.

**Statement.** Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`.
1. **Surjective stability.** For every `m >= 4`, `j_m(K_2(m, R_L)) = K_2(m+1, R_L)`.
2. **Injective stability (condition (i)).** For every `N >= 3`, `K_2(N, R_L) -> K_2(R_L) ≅ Q^x` is an isomorphism. So
   `K_2(N, R_L) = {{λ, N+1}_N : λ in Q^x} ≅ Q^x`. Here `N` in `N+1` is the number operator.
3. **Centrality.** `K_2(N, R_L)` is central in `St_N(R_L)` for every `N >= 3`. This settles
   `k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`.
4. **Word problem (gate 1).** `St_N(R_L)` has solvable word problem for every `N >= 3`: a word is trivial if and only
   if its image in `E_N(R_L)` is `1` and the halting search of `leavitt-resolvent-stable-k2-class-is-computable`
   returns `λ = 1`. With `St_N(R_L)` finitely presented for `N >= 4`, this is gate 1 of the shell route.
