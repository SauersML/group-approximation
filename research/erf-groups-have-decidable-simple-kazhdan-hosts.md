---
rg: 2
id: erf-groups-have-decidable-simple-kazhdan-hosts
kind: claim
title: Every finitely generated effectively residually finite group with solvable word problem embeds in an infinite simple Kazhdan LEF group with solvable word problem
distinct_from:
  perfect-erf-groups-have-decidable-simple-kazhdan-hosts: that is the case where the group lies in the derived subgroup of a computable overgroup, in particular the perfect case; this drops that hypothesis.
artifacts:
  - research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md
  - research/artifacts/sk-decidable-host-2026-09-13.md
---

**ESTABLISHED (unreviewed)**, through `erf-groups-decidable-hosts-via-half-line-proof` (sk-decidable-host,
2026-09-13). Let `Γ` be finitely generated, infinite, effectively residually finite, with solvable word problem.
Then `Γ` embeds in an infinite, finitely generated, simple Kazhdan LEF group whose word problem is solvable.

The effectivity hypothesis is not needed. `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts` gives such a host
for every finitely generated LEF group with solvable word problem, so for every finitely generated residually finite
group with solvable word problem.

**The step that was missing.** `perfect-erf-groups-have-decidable-simple-kazhdan-hosts` needs a finitely generated
overgroup `Δ ⊇ Γ` with `Γ ≤ [Δ,Δ]` that is again effectively residually finite AND has solvable word problem. The
overgroup of `rf-groups-lie-in-derived-subgroups-of-rf-groups` is residually finite, but its word problem is not
controlled. The resolution gives up residual finiteness of the overgroup:
- the half-line overgroup `C(Γ)` is LEF with `WP(C(Γ)) ≡_T WP(Γ)`
  (`half-line-overgroup-keeps-lef-and-solvable-word-problem`);
- the lamplighter host over a LEF acting group replaces the Toeplitz host over a residually finite one.

## Attempts

- **Settled with a non-residually-finite overgroup (sk-decidable-host, 2026-09-13).** `Δ = C(Γ)`, with explicit
  finite models of its balls: a permutation of `Q^({-3r,…,3r})` intertwines the partial level shift. Its word problem
  reduces to `WP(Γ)` through levelwise normal forms, and the lamplighter host `EL_3(LC(2^Δ,F_2) ⋊ (Z/2 ≀ Δ))` has word
  problem reducible to `WP(Δ)`. See `research/artifacts/sk-decidable-host-2026-09-13.md`.
- **The Ore overgroup, as built.** `Δ = ⟨ρ(S), a_s, b_s⟩ ≤ ∏_n Alt(Ω_n)`, with the commutator witnesses chosen in
  each coordinate separately. Every coordinate of a word in these generators is computable, so nontriviality is
  semi-decidable and `WP(Δ)` is co-r.e. Nothing makes it r.e.: the witnesses in different coordinates are unrelated,
  so no computable bound says how far to look before declaring a word trivial. The construction is correct; it
  controls no word problem.
- **Wreath products, dead by abelianization.** For `W = Γ ≀ F` with `F` finite, `W^{ab} = Γ^{ab}`, and the class of
  `(a_1,…,a_k;σ)` is `Σ ā_i`. An injective homomorphism `g ↦ (g, α(g), 1,…)` lands in `[W,W]` only if the
  homomorphism `α` induces `-id` on `Γ^{ab}`, which a general finitely generated group does not admit. The maps that
  would work, such as `g ↦ (g,g^{-1},1)`, are not homomorphisms; this is the same failure as `diag(a,a^{-1},1)` in
  `whitehead-diagonal-map-is-not-multiplicative`.
- **Correcting inside the envelope instead.** `δ ↦ diag(u_δ, v_δ, 1)` needs `v` to be a homomorphism into the units
  with `[u_δ] + [v_δ] = 0` in `K_1`, and `δ ↦ u_{δ^{-1}}` is an anti-homomorphism. Over `Z` the correction exists,
  through the index map, which is how the full group embeds in
  `topological-full-group-embeds-in-subshift-elementary-group`; over a general acting group no such homomorphism is
  known.
- **Coherent Ore witnesses (superseded, not needed).** In the chain the maps `Δ/Δ_{m+1} → Δ/Δ_m` make
  `Ω_{m+1} → Ω_m` fiber-preserving and `λ_{m+1}(s)` covers `λ_m(s)`. Inside the fiber-preserving subgroup
  `Sym(F) ≀ Alt(Ω_m)` the projection is a homomorphism, so the question is whether a commutator decomposition lifts
  along it with prescribed images, correcting arbitrary lifts by kernel elements. Coherent witnesses would present `Δ`
  as an inverse limit of computable finite data, with a decidable word problem. This would give a residually finite
  overgroup, which the half-line route shows is unnecessary.
