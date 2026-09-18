---
rg: 2
id: amenable-cd-two-ascending-hnn-bs-proof
kind: route
title: Exact vanishing of H_1 with U-coefficients plus the dimension-2 FP criterion forces BS(1,m), and the EA-radical theorem turns every Z-quotient over a finitely generated kernel into a contradiction
target: amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar
requires:
  - ascending-hnn-quotients-have-vanishing-affiliated-first-homology
  - amenable-fp-iff-affiliated-top-homology-vanishes
  - amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical
---

`G` is amenable with `cd G ≤ 2`, hence torsion-free. Subgroups of `G` are amenable, with cd at
most 2. `BS(1,m) = ⟨a, t | t a t⁻¹ = a^m⟩` with `m ≠ 0`, so `BS(1,1) = Z²` and `BS(1,−1)` is the
Klein bottle group.

## Cited facts (recalled, not re-checked to the page)

- **(SS)** Stallings--Swan: a group of cd 1 is free. An amenable free group is trivial or `Z`.
- **(C)** C. Chou, "Elementary amenable groups", Illinois J. Math. 24 (1980): an elementary
  amenable torsion group is locally finite. So a finitely generated infinite EA group has an
  element of infinite order.
- **(Gi)** D. Gildenhuys, "Classification of soluble groups of cohomological dimension two",
  Math. Z. 166 (1979): a finitely generated solvable group of cd 2 is `BS(1,m)`, `m ≠ 0`. Used
  only in item 5, and also recorded in `amenable-cd-two-solvable-iff-coherent-rational-group-algebra`.
- **(GS)** A torsion-free abelian group of rank 1 that is not finitely generated has cd 2
  (Gildenhuys--Strebel; R. Bieri, *Homological dimension of discrete groups*, Theorem 7.10). This is
  the same citation as (GS) in `amenable-cd-two-ea-radical-via-commensurated-cyclic-splitting`.
  Used only in item 5.

## Item 1

`G = ⟨K, t⟩` is finitely generated and maps onto `Z`, so it is infinite and `cd G ∈ {1, 2}`.

- If `cd G = 1`, then `G ≅ Z` by (SS).
- If `cd G = 2`, then `H_1(G; U(G)) = 0` by `ascending-hnn-quotients-have-vanishing-affiliated-first-homology`,
  item 1. Item 4, (c) ⇒ (a), of `amenable-fp-iff-affiliated-top-homology-vanishes` gives
  `G ≅ BS(1,m)`.

**The base.** `K ≤ ker χ`, and `K` is finitely generated.
- If `G ≅ Z`, then `ker χ = 1`, so `K = 1`.
- If `G ≅ BS(1,m)` with `m ≠ 1`, then `G^ab = Z ⊕ Z/|m − 1|`, so every homomorphism to `Z` kills
  `a`. Hence `ker χ ⊇ ⟨⟨a⟩⟩ = Z[1/m]`, and since `G/Z[1/m] ≅ Z`, `ker χ = Z[1/m]`.
- If `m = 1`, then `ker χ ≅ Z`.

In every case `ker χ` is locally cyclic, so `K` is trivial or infinite cyclic. ∎

## Item 2

`H = N⟨t⟩` for any `t` mapping to a generator of `H/N ≅ Z`. Then `t N t⁻¹ = N`, and
`χ : H → H/N ≅ Z` kills `N` with `χ(t) = 1`. Item 1 applies to `H`:
- if `H ≅ Z`, then `N = ker χ = 1`;
- if `H ≅ BS(1,m)`, then `N = ker χ`, which is `Z[1/m]` for `m ≠ 1` and `Z` for `m = 1`.
  `Z[1/m]` is finitely generated only for `|m| = 1`, and then it is `Z`.

So `N ∈ {1, Z}`.

For the normaliser form, let `g ∈ N_G(N)` with `⟨g⟩ ∩ N = 1`. Then `H = N⟨g⟩` has `N ⊴ H` and
`H/N ≅ ⟨g⟩ ≅ Z`, since `g` is of infinite order because `G` is torsion-free. Apply the above.

If `N` is finitely generated and not cyclic, then `N ∉ {1, Z}`. So every `g ∈ N_G(N)` has a
nontrivial power in `N`, that is, `N_G(N)/N` is torsion. ∎

## Item 3

Let `G` be finitely generated and not solvable with `cd G = 2`. By item 1 of
`amenable-cd-two-solvable-iff-coherent-rational-group-algebra` (as used in
`amenable-cd-two-ea-radical-via-commensurated-cyclic-splitting`), `G` is then not virtually
solvable either.

**(a).** If `G` had the form of item 1, it would be `Z` or `BS(1,m)`, both solvable.
- If `Σ¹(G) ≠ ∅`, then `H_1(G; U(G)) = 0` by item 2 of
  `ascending-hnn-quotients-have-vanishing-affiliated-first-homology`, and so `G ≅ BS(1,m)`.
- An ascending HNN extension `K *_φ` with `K` finitely generated has the form of item 1 via the
  canonical character.

**(b).** Let `1 ≠ N ⊴ G` be finitely generated, and suppose `gN ∈ G/N` has infinite order. Then
`⟨g⟩ ∩ N = 1`, and item 2 gives `N ≅ Z`. That is a nontrivial elementary amenable normal subgroup,
so `G ≅ BS(1,m)` by item 2 of `amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`, a
contradiction. So `G/N` is torsion.

Now suppose `[G : N] = ∞`. `G/N` is finitely generated and amenable, and it is infinite.
- `N` is finitely generated and amenable with `cd N ≤ 2`.
- If `cd N ≤ 1`, then `N ≅ Z` by (SS), since `N ≠ 1`. This is excluded as above.
- If `N` were solvable, it would be a nontrivial EA normal subgroup, which is excluded by the same
  theorem.

So `N` is finitely generated, amenable, of cd 2, and not solvable.

**(c).**
- `G/1 = G` is not elementary amenable: an EA group of finite cd is virtually solvable (the (HL)
  citation of `amenable-cd-two-ea-radical-via-commensurated-cyclic-splitting`).
- For `N ≠ 1` finitely generated and normal, if `G/N` were infinite and EA, it would be finitely
  generated, so by (C) it would have an element of infinite order, contradicting (b). ∎

## Item 4

- The first sentence is item 2, applied with `g` of infinite order modulo `N`.
- The second is the EA-radical theorem.
- The third follows from them.
- The last case is (b).

**Why the tool stops there.** Every exact-vanishing argument available here produces, for some
subgroup `H ⊇ N`, a finite partial presentation complex whose relation module over `U(H)` has
full rank. The mapping-torus theorem supplies one exactly when `H/N ≅ Z`.

When `Q = G/N` is an infinite torsion group, there is no such `H`. Put `U = U(G)`.

- **`H_0(N; U) = 0`.** `N` is infinite and finitely generated. So
  `U(N) ⊗_{ZN} Z` is finitely presented, of dimension `b_0^(2)(N) = 0`, hence zero by (J1) and (J2) of
  `ascending-hnn-quotients-affiliated-h1-proof`.
  Then `H_0(N; U) = U ⊗_{U(N)} (U(N) ⊗_{ZN} Z) = 0`.
- **The five-term sequence** of `1 → N → G → Q → 1` with coefficients in `U` then gives a
  surjection
  `H_0(Q; H_1(N; U)) ↠ H_1(G; U)`, where `H_1(N; U) = U ⊗_{U(N)} H_1(N; U(N))`.
- **This module is not zero** when `G` is a counterexample, because it surjects onto
  `H_1(G; U) ≠ 0`.

So `H_1(G; U) = 0` would follow from the vanishing of these `Q`-coinvariants.

- For `Q = Z`, the coinvariants are `coker(1 − t_*)`. Its vanishing for finitely generated `N` is
  exactly what `ascending-hnn-quotients-have-vanishing-affiliated-first-homology` proves, and it
  does so through a finite mapping torus rather than through the module.
- For torsion `Q`, the coinvariants are taken along a group with no `Z`-direction, and there is no
  mapping torus.

Moreover, `N` is again a counterexample, so any inductive descent `G ⊃ N ⊃ N' ⊃ …` needs a
termination argument that is not available. Følner and Lück approximation arguments give only
dimension 0. The graph records the same gap at the Jacobian-rank level in the root node's
w3-112 attempt.

Two things would resolve it:
- a proof that no finitely generated amenable group of cd 2 has an infinite torsion quotient with
  finitely generated kernel; or
- an example of one, which would itself be a counterexample.

## Item 5

`Γ = Z[1/6] ⋊ ⟨s, t⟩`, with `s` acting by `×2` and `t` acting by `×3`, and `a = 1 ∈ Z[1/6]`.

- **Γ is an ascending HNN extension of `B = ⟨a, s⟩ ≅ BS(1,2)`.** `t a t⁻¹ = a³` and `t s t⁻¹ = s`,
  so `t B t⁻¹ ⊆ B`. Hence `cd Γ ≤ cd B + 1 = 3`.
- **The kernel.** Let `χ(a) = 0` and `χ(s) = χ(t) = 1`. Then `N = ker χ = Z[1/6] ⋊ ⟨u⟩` with
  `u = s t⁻¹` acting by `2/3`.
- **`N` is finitely generated, by `a` and `u`.** The span contains `1` and `(2/3)^{±k}`, hence
  `3^{-k}` and `2^{-k}`, hence `6^{-k}`, because `gcd(2^k, 3^k) = 1`.
- **`N` is not `BS(1,m)`.**
  - `N^ab = Z[1/6]/(2/3 − 1)Z[1/6] ⊕ Z = Z`, since `1/3` is a unit of `Z[1/6]`.
  - `BS(1,m)^ab` is `Z ⊕ Z/|m − 1|` (or `Z²` when `m = 1`), so only `m = 2` or `m = 0` fits, and
    `m = 0` is excluded.
  - `[N, N] = Z[1/6]`, but `[BS(1,2), BS(1,2)] = Z[1/2]`, and `Z[1/6] ≇ Z[1/2]` because only the
    first is 3-divisible.
- **So `cd N = 3`.** `N` is finitely generated and solvable but not `BS(1,m)`, so `cd N ≠ 2` by
  (Gi). `cd N ≥ cd Z[1/6] = 2` by (GS). Hence `cd N = 3 = cd Γ`.

This matches the higher-dimensional form of item 1: the kernel is not of type `F_2`, which is what
a dimension-`n` version would need. So in amenable dimension 3, a finitely generated normal
subgroup with quotient `Z` need not drop dimension. Item 2 is a genuinely two-dimensional
phenomenon, because there the only finitely generated amenable groups of cd at most 1 are `1` and
`Z`, and item 1 pins down the whole group. ∎
