---
rg: 2
id: bg-chains-are-residually-tf-solvable-so-g1n-targets-die
kind: claim
title: Every finite Baumslag-Gersten chain <c_0, …, c_m | c_{i+1}^-1 c_i c_{i+1} = c_i^n> is residually 𝒮, so the kernel of G(1, n) → Z is locally residually 𝒮 and every map from the six commutator-root groups (all 26 open words) to any Baumslag-Gersten group G(1, n) kills y
distinct_from:
  commutator-root-frontier-kills-pl-and-bi-ordered-targets: its item 5 kills targets whose kernel image is locally residually 𝒮 and leaves G(1, n) open because it does not know whether the finite chains in the kernel are residually 𝒮; this proves they are, for every n ≠ 0, so G(1, n) falls under its item 5. Its item 6 search for maps to G(1, n) is superseded for every n.
  bg-shift-chains-die-in-residually-linear-alphabets: that kills infinite forward chains in residually solvable groups; this shows the opposite behaviour for finite chains, which are residually solvable with torsion-free factors, and that is what the kill here needs.
  baumslag-gersten-elementary-amenable-quotient-keeps-a: that gives one elementary amenable quotient of BG keeping a; this is about the finitely generated subgroups of the kernel of BG itself, and gives no quotient of BG.
---

**ESTABLISHED** (written proof, unreviewed) by [[bg-chains-are-residually-tf-solvable-so-g1n-targets-die-proof]].
It decides every `G(1, n)` target for the 26 commutator-root words at once (negatively), so no search with
larger caps is needed. Nothing is new for the zero-divisor conjecture.

**Setting.** As in [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]]: `𝒮` is the class of groups with
a finite normal series (every term normal in the whole group) with torsion-free abelian factors. For `n ≠ 0`,
`G(1, n) = <c, s | (c^s)^{-1} c c^s = c^n>` and `c_i = s^{-i} c s^i`. The six groups are
`G(K; α, β) = <y, t | y_1^K = [y_0^α, y_2^β]>`, `K ∈ {2, 3}`, `α, β = ±1`, `N` the normal closure of `y`.

## Theorem

1. **Amalgamation lemma.** Let `Γ ∈ 𝒮` have an element `z` of infinite order and a retraction `ρ: Γ → <z>`.
   Let `B ∈ 𝒮` and `c ∈ B` of infinite order. Then `Δ = Γ *_{z = c} B` is residually 𝒮. More precisely, with
   `L = ker(Δ → B)` and `K = ker(L → ⊕ J_i)`:
   - `L` is a free product of `B`-conjugates `J_i` of `J = ker ρ`, one for each coset in `B/<c>`;
   - `K` is free and normal in `Δ`;
   - `Δ / K^{(k)} ∈ 𝒮` for every `k`, and `∩_k K^{(k)} = 1`.
2. **Finite chains.** For every `n ≠ 0` and `m ≥ 0` the chain `C_m(n) = <c_0, …, c_m | c_{i+1}^{-1} c_i c_{i+1} = c_i^n>`
   is residually 𝒮. It has a nested family of normal subgroups `X_k ⊂ ker(C_m → <c_m>)`, with trivial
   intersection and `C_m / X_k ∈ 𝒮`.
   - The proof is an induction on `m`, since `C_{m+1} = C_m *_{<c_m>} BS(1, n)`, where `BS(1, n) = <c_m, c_{m+1}>`.
     At each step item 1 is applied to `C_m / X_k`.
   - The same induction works for chains with a different `n_i ≠ 0` on each edge.
3. **Kernel of `G(1, n)`.** The kernel `M` of the `s`-exponent map `G(1, n) → Z` is the directed union of
   segments `<c_a, …, c_b> ≅ C_{b-a}(n)`. So `M` is locally residually 𝒮. It is not residually solvable
   ([[bg-shift-chains-die-in-residually-linear-alphabets]]), and item 3 is the local statement that
   [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]] item 5 needs.
4. **The kill.** For each of the six groups, each `n ≠ 0` and every homomorphism `φ: G(K; α, β) → G(1, n)`, we have
   `φ(y) = 1`.
   - `N^ab` is torsion, so `φ(N) ≤ M`. Then item 5 of the frontier node applies.
   - So none of the 26 open commutator-root words is certified by a Baumslag-Gersten target, for any `n`,
     including `|n| ≥ 3`.
   - The same holds for any target whose image of `N` lies in a directed union of finite chains of this kind.
     An example is a tree of groups obtained from `𝒮`-groups by repeated amalgamation along retract copies of `Z`.

## Where it stops

- The remaining named candidates for the six groups are:
  - bi-orderings of `G(K; 1, ±1)` itself;
  - elementary amenable or other quotients of `G(1, n)` whose kernel image is not locally residually 𝒮, such as
    the quotient of [[baumslag-gersten-elementary-amenable-quotient-keeps-a]], which is locally solvable-by-`Z`
    but is not known to be locally residually 𝒮 on its kernel;
  - groups in `𝓗` whose kernel image contains an infinite forward chain that is not locally residually 𝒮.
- A target now has to be both outside the PL groups and "genuinely non-𝒮" on finitely generated subgroups of
  the image of `N`. For `(α, β) = (-1, 1)` it must also contain generalized torsion
  ([[commutator-root-minus-one-groups-have-generalized-torsion]]).
