---
rg: 2
id: cd-two-torsion-quotient-out-embedding-proof
kind: route
title: The EA-radical theorem kills Z(N) and C_G(N); vanishing of H_0(N; U) collapses the LHS sequence to one column; averaging over finite cyclic groups rewrites the coinvariants; Schur's theorem makes linear shadows finite
target: cd-two-torsion-quotient-counterexamples-embed-in-out
requires:
  - amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical
  - amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar
  - amenable-fp-iff-affiliated-top-homology-vanishes
---

Notation as in the target. `G` is torsion-free, since `cd G < ∞`.

## Cited facts (recalled, not re-checked to the page)

- **(Sch)** Burnside–Schur: a finitely generated torsion subgroup of `GL_b(k)`, for a field `k` of
  characteristic 0, is finite.
- **(J)** `U(N) ⊗_{ZN} Z` is a finitely presented `U(N)`-module of dimension `b_0^(2)(N) = 0` when
  `N` is infinite and finitely generated, hence zero. This is (J1)–(J3) as used in
  `ascending-hnn-quotients-affiliated-h1-proof`, Step 4, and in item 4 of
  `amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar`.
- **(LHS)** The Lyndon–Hochschild–Serre spectral sequence
  `E^2_{p,q} = H_p(Q; H_q(N; M)) ⇒ H_{p+q}(G; M)` for a right `ZG`-module `M`. For
  `M = U = U(G)`, the left `U`-action commutes with everything, so it is a spectral sequence of
  left `U`-modules.

## Item 1

- **`Z(N) = 1`.** `Z(N)` is characteristic in `N`, so it is normal in `G`. It is abelian, so it is
  an elementary amenable normal subgroup of `G`. By item 2 of
  `amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`, a nontrivial one would force
  `G ≅ BS(1,m)`, which is solvable. So `Z(N) = 1`.
- **`C_G(N) = 1`.** `C = C_G(N)` is normal in `G`, and `C ∩ N = Z(N) = 1`. So `C` maps
  injectively to `Q`, which is torsion. Hence `C` is a torsion subgroup of the torsion-free group
  `G`, so `C = 1`.
- **Embeddings.** The conjugation map `c : G → Aut(N)` has kernel `C = 1`. Since `Z(N) = 1`,
  `c|_N : N → Inn(N)` is an isomorphism. If `c(g)` is inner, say `c(g) = c(n)`, then `g n⁻¹ ∈ C`,
  so `g = n ∈ N`. Hence `c(G) ∩ Inn(N) = c(N)`, and `Q = G/N ↪ Aut(N)/Inn(N) = Out(N)`.
- **Preimage.** Let `Q̄ ≤ Out(N)` be the image and `P ≤ Aut(N)` its preimage. Then
  `c(G) ⊆ P`. Both contain `Inn(N)` with the same image `Q̄` in `Out(N)`, so `c(G) = P`.
- **Powers.** If `gN` has order `n`, then `g^n ∈ N` and `φ_g^n = c(g^n) = inn(g^n)`. Also
  `φ_g(g^n) = g g^n g⁻¹ = g^n`. If `g ∉ N`, then `φ_g` is not inner by the embedding. ∎

## Item 2

**Collapse.** By (J), `H_0(N; U) = U ⊗_{ZN} Z = U ⊗_{U(N)} (U(N) ⊗_{ZN} Z) = 0`. So
`E^2_{p,0} = H_p(Q; 0) = 0` for every `p`.

- `E^2_{0,1} = H_0(Q; V)` receives only `d^2 : E^2_{2,0} → E^2_{0,1}`, which is zero.
- `E^2_{0,1}` has no outgoing differentials.
- `H_1(G; U)` is filtered by `E^∞_{0,1}` and `E^∞_{1,0} = 0`.

So `H_1(G; U) ≅ E^2_{0,1} = H_0(Q; V)`, an isomorphism of left `U`-modules, and the edge map
`V → H_1(G; U)` is onto.

**The Q-action.** For a projective `ZG`-resolution `P_•` of `Z`, the group `G` acts on
`U ⊗_{ZN} P_•` by `u ⊗ x ↦ u g⁻¹ ⊗ g x`. This commutes with left multiplication by `U`, and `N`
acts trivially on homology. So `Q` acts `U`-linearly on `V`.

**Generators.** `I_Q V = Σ_i (q_i − 1) V`. This holds because `(ab − 1)v = a(b − 1)v + (a − 1)v`
and `(a⁻¹ − 1)v = −(a − 1)(a⁻¹ v)`. So every `(q − 1)v` lies in `Σ_i (q_i − 1)V`.

**Averaging.** `V` is a `Q`-vector space, because `Q ⊆ U`. Fix `i` and put
`e = e_i = (1/n) Σ_{k<n} q_i^k`, with `n = n_i`.

- `e` is an idempotent `U`-linear endomorphism of `V`, and `e(q_i − 1) = 0`, so
  `(q_i − 1)V ⊆ ker e = (1 − e)V`.
- Conversely, `(1 − e)v = −(1/n) Σ_k (q_i^k − 1)v`, and `q_i^k − 1 = (q_i − 1)(1 + … + q_i^{k−1})`.
  So `(1 − e)v ∈ (q_i − 1)V`.

Hence `(q_i − 1)V = (1 − e_i)V`, and `H_0(Q; V) = V / Σ_i (1 − e_i)V`.

**The subgroups `H_i = ⟨N, g_i⟩`.**
- `H_i/N = ⟨q_i⟩` is finite, so `N` is normal of finite index in `H_i`.
- The same collapse applies to `1 → N → H_i → ⟨q_i⟩ → 1` with coefficients in `U`, because
  `H_0(N; U) = 0`. So `H_1(H_i; U) ≅ V/(1 − e_i)V ≅ e_i V`.
- `H_1(G; U)` is a quotient of `V/(1 − e_i)V`.
- `G` is a counterexample, so `H_1(G; U) ≠ 0` by item 4 of
  `amenable-fp-iff-affiliated-top-homology-vanishes`. Hence `e_i V ≠ 0` for every `i`.

Finally, `V/Σ_i(1 − e_i)V = 0` exactly when `V = Σ_i ker(e_i)`. ∎

## Item 3

**On `N^ab`.** `N^ab = Z^b ⊕ T` with `T` finite, since `N` is finitely generated. Every
automorphism preserves `T`. Consider the homomorphism `ρ : Aut(N^ab) → GL_b(Z) × Aut(T)` given by
the actions on `N^ab/T` and on `T`.

- An element of `ker ρ` is `x ↦ x + h(x)` for some `h : N^ab → T` that kills `T` and lands in `T`.
  So `ker ρ` injects into `Hom(Z^b, T)`, which is finite.
- `Q` acts on `N^ab`, because inner automorphisms act trivially there. The image of `Q` in
  `GL_b(Z) ≤ GL_b(Q)` is a finitely generated torsion group, so it is finite by (Sch).
- `Aut(T)` is finite.

Hence the image of `Q` in `Aut(N^ab)` is finite.

**On finite characteristic quotients.** If `C` is characteristic of finite index in `N`, then
`N/C` is finite, so `Out(N/C)` is finite, and `Q` acts on `N/C` through `Out(N/C)`.

**The subgroup `G_0`.** Let `Q_0` be the kernel of the action of `Q` on `N^ab`, and `G_0` its
preimage. `Q_0` has finite index in `Q`, so it is infinite, finitely generated, amenable and
torsion.

**The exact sequence.** The five-term sequence of `1 → N → G_0 → Q_0 → 1` with rational
coefficients is
`H_2(G_0; Q) → H_2(Q_0; Q) → H_0(Q_0; H_1(N; Q)) → H_1(G_0; Q) → H_1(Q_0; Q) → 0`.

- `H_1(Q_0; Q) = Q_0^ab ⊗ Q = 0`, because `Q_0^ab` is a finitely generated torsion abelian group.
- `H_0(Q_0; H_1(N; Q)) = H_1(N; Q)`, because the action is trivial.

This gives the stated exact sequence, and so `b_1(G_0) ≤ b_1(N)`. ∎

## Item 4

**(B) ⇒ (A).** Let `G` be finitely generated amenable with `cd G = 2`, and let `N ⊴ G` be finitely
generated with `G/N` infinite torsion.

- If `G` were solvable, then `G/N` would be a finitely generated solvable torsion group, hence
  finite. So `G` is a counterexample.
- `N ≠ 1`, because `G` is torsion-free and infinite.

By item 3(b) of `amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar`, `N` is finitely
generated, amenable, with `cd N = 2`. By item 1 it is centreless, and `Q = G/N` embeds in
`Out(N)` as a finitely generated infinite amenable torsion subgroup whose preimage is `G`. Since
`cd G = 2`, this contradicts (B).

**(A) ⇒ (B).** Let `N`, `Q` be as in (B), and let `P ≤ Aut(N)` be the preimage of `Q`.

- Since `Z(N) = 1`, `Inn(N) ≅ N`, and `P/Inn(N) ≅ Q`.
- `P` is finitely generated, because `N` and `Q` are.
- `P` is amenable, as an extension of amenable groups.
- `cd P ≥ cd N = 2`.

If `cd P ≤ 2`, then `P` has cd 2 and a finitely generated normal subgroup `Inn(N)` with infinite
torsion quotient, which contradicts (A). So `cd P ≥ 3`.

**Last sentence.** Under (A), item 3(b) of `amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar`
says that `G/N` is torsion for every nontrivial finitely generated `N ⊴ G`. (A) excludes an
infinite torsion quotient, so `[G : N] < ∞`. ∎

## Calibration

- **BS(1,m) (m ≥ 2).** Every nontrivial normal subgroup of `BS(1,m)` meets `Z[1/m]`, and the
  finitely generated normal subgroups have quotients that are finitely generated and metabelian.
  A torsion quotient of that kind is finite. So the hypotheses of the target are never met in the
  solvable case, consistent with item 4.
- **Where amenability of `N` enters.** Items 2 and 3 use only `H_0(N; U(G)) = 0`, which holds for
  every infinite finitely generated `N`. Item 1 uses the EA-radical theorem, which needs `G`
  amenable of cd 2. The Ollivier–Wise example in `cd-two-kazhdan-kernel-with-grigorchuk-quotient`
  satisfies the conclusions of items 2 and 3 with non-amenable `N`.
