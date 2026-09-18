---
rg: 2
id: cd-two-torsion-quotient-counterexamples-embed-in-out
kind: claim
title: In a two-dimensional counterexample, a finitely generated normal N with infinite torsion quotient Q is centreless, Q embeds in Out(N), and H_1(G; U(G)) is exactly the joint cokernel of finitely many averaging idempotents on H_1(N; U(G))
distinct_from:
  amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar: that proves G/N is torsion and that H_1(G; U) is a quotient of the Q-coinvariants; this proves the coinvariant map is an isomorphism, rewrites it through the finite-order generators of Q, embeds Q in Out(N), and makes the torsion case equivalent to a statement about torsion subgroups of Out(N)
  amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical: that excludes EA normal subgroups of G; this uses it for Z(N) and for the centraliser of N, to rebuild G from N and a subgroup of Out(N)
  outer-extension-word-problem-is-kernel-bounded: that embeds an outer extension of a centreless group in Aut(N) for word-problem bounds; here the same embedding is forced by amenability and cd 2, and it is used to rebuild G
  centerless-normal-subgroups-with-locally-finite-out-of-fp-are-fp: that treats normal subgroups of finitely presented groups whose Out is locally finite; here Out(N) must contain an infinite finitely generated torsion group, and no finite presentability is available
---

**ESTABLISHED** through `cd-two-torsion-quotient-out-embedding-proof`, from
`amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`,
`amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar` (item 3(b)) and
`amenable-fp-iff-affiliated-top-homology-vanishes` (item 4). Items 2 and 3 use no amenability of
`N` beyond `H_0(N; U(G)) = 0`.

**Setting.** `G` is a finitely generated amenable group with `cd G = 2` that is not solvable, that
is, a two-dimensional counterexample to Kropholler's question. `1 ≠ N ⊴ G` is finitely generated
with `[G : N] = ∞`. By item 3(b) of `amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar`,
`Q = G/N` is an infinite, finitely generated, amenable torsion group, and `N` is again a
counterexample. Write `G = ⟨N, g_1, …, g_r⟩`, `q_i = g_i N` and `n_i` for the order of `q_i`.
`U = U(G)` is the algebra of affiliated operators.

1. **Q embeds in Out(N).** `Z(N) = 1` and `C_G(N) = 1`. So conjugation gives embeddings
   `G ↪ Aut(N)` and `Q ↪ Out(N)`, and `G` is isomorphic to the full preimage of `Q` in `Aut(N)`.
   The pair `(N, Q ≤ Out(N))` determines `G`. Every `g ∈ G ∖ N` acts on `N` by an automorphism
   `φ_g` that is not inner, with `φ_g^n = inn(g^n)` and `φ_g(g^n) = g^n` for `n` the order of
   `gN`.
2. **Exact coinvariant formula.** Put `V = H_1(N; U)`, a left `U`-module on which `Q` acts
   `U`-linearly. Then
   `H_1(G; U) ≅ H_0(Q; V) = V / Σ_{i=1}^r (1 − e_i) V`, where `e_i = (1/n_i) Σ_{k<n_i} q_i^k`.
   The map `V → H_1(G; U)` is onto, and this is an isomorphism, not only a surjection. For each
   `i`, `H_1(⟨N, g_i⟩; U) ≅ e_i V`, and `e_i V ≠ 0`. So `H_1(G; U) = 0` holds exactly when
   `V = Σ_i ker(e_i)`: the `r` finite-group averages have no common nonzero quotient.
3. **Every finite linear shadow of the action is finite.** The image of `Q` in `Aut(N^ab)` is
   finite. So is its image in `Out(N/C)` for every characteristic subgroup `C` of finite index in
   `N`. Hence some finite-index `G_0 ≤ G` containing `N` acts trivially on `N^ab`, and
   `Q_0 = G_0/N` is again infinite, finitely generated, amenable and torsion. For such `G_0`,
   `H_2(Q_0; Q) → H_1(N; Q) → H_1(G_0; Q) → 0` is exact, so `b_1(G_0) ≤ b_1(N)`.
4. **Equivalent form of the torsion case.** The following are equivalent.
   - (A) No finitely generated amenable group of cd 2 has a finitely generated normal subgroup
     with infinite torsion quotient.
   - (B) For every finitely generated, centreless, amenable group `N` with `cd N = 2`, and every
     finitely generated infinite amenable torsion subgroup `Q ≤ Out(N)`, the preimage of `Q` in
     `Aut(N)` has cd at least 3.

   With (A), a two-dimensional counterexample has no nontrivial finitely generated normal
   subgroup of infinite index.

**What this leaves.** By item 2, the torsion case is the vanishing of `V/Σ(1 − e_i)V` for the
dimension-zero `U`-module `V`. The obstruction node
`cd-two-kazhdan-kernel-with-grigorchuk-quotient` shows that (A) is false once amenability of `N`
is dropped. So a proof must use amenability of the kernel, not only that of `Q`.
