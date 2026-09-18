---
rg: 2
id: higman-chain-configuration-reduction-proof
kind: route
title: Both factors of the chain embed as soon as c has infinite order; separate them by the centralizer of (b, m) in M × L_1, using the retraction of BS(b,c) onto <b>
target: higman-chain-group-pbh-iff-chain-configuration
requires:
  - pbh-amalgams-over-centralizer-separated-edges
  - bs12-base-generator-is-a-centralizer-in-b-a
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - higman-group-splits-as-amalgams-over-free-subgroups
  - baumslag-gersten-splits-over-bs12-edges
---

Lane proof (bh-free-49, 2026-09-18), not reviewed.

**(1) ⟹ (2).** `G_1` itself contains the configuration `(a, b, c)`: `c` has infinite
order because it generates the base of the factor `<b, c> ≅ BS(1,2)`.

**(2) ⟹ (1).** Let `M ∈ B_A` contain a configuration.
- `b` has infinite order: if `b^n = 1` then `c = b^-n c b^n = c^(2^n)`, so `c` has finite
  order.
- So `X = <a, b>` and `Y = <b, c>` are quotients of `BS(1,2)` in which the base generator
  (`b`, respectively `c`) has infinite order. By Step 0 of
  `bs12-base-generator-centralizer-proof` both are isomorphic to `BS(1,2)`, by the obvious
  maps.
- `r : Y -> <b>`, `c -> 1`, `b -> b` is a retraction, since the relation maps to `1 = 1`.
- In `Y = Z[1/2] ⋊ <b>`, an element commuting with `b` has zero base part, so
  `C_Y(b) = <b>`. Take `S = {b}`, which commutes with `<b>`.
- By `bs12-base-generator-is-a-centralizer-in-b-a`, `<b>` is realized in `X ≅ BS(1,2)`.

These are the hypotheses of item 3 of `pbh-amalgams-over-centralizer-separated-edges`
with `L = M`, so `X *_<b> Y ∈ B_A`. The presentation of `X *_<b> Y` is the presentation of
`G_1`. []

**(1) ⟺ (3).** Finitely presented twisted Brin--Thompson groups are simple and highly
transitive, so they lie in `B_A` by BFFHZ Theorem C, (iii) ⟹ (i)
(`fp-simple-highly-transitive-groups-satisfy-pbh`). This gives (3) ⟹ (2). Conversely, if
`G_1 ∈ B_A`, then (i) ⟹ (iv) of Theorem C puts `G_1` in a finitely presented simple MIF
group. BFFHZ Corollary D ("Finitely presented (simple) twisted Brin--Thompson groups are
universal among finitely presented simple highly transitive groups, and more generally
among finitely presented simple MIF groups", arXiv:2503.21882v2, read in the TeX source
`BHC_for_AutFn.tex` on MSI in this lane) puts that group inside a finitely presented
twisted Brin--Thompson group. []

**Necessity for H4 and BG.** `G_1` is the vertex group `<a, b, c>` of
`higman-group-splits-as-amalgams-over-free-subgroups`, in the same presentation.
By item 1 of `baumslag-gersten-splits-over-bs12-edges`, `BG ≅ K*_ψ` with
`K = <a_0, a_1, a_2 | a_1 a_0 a_1^-1 = a_0^2, a_2 a_1 a_2^-1 = a_1^2>`. The map
`a -> a_2^-1`, `b -> a_1^-1`, `c -> a_0` is an isomorphism `G_1 -> K`:
- `a_2 a_1^-1 a_2^-1 = a_1^-2`;
- `a_1 a_0 a_1^-1 = a_0^2`.

These are exactly the two relations of `G_1` under the substitution. Both test cases
contain `G_1`, and `B_A` is closed under subgroups. []

**Linear groups.** Let `(a, b, c)` be a configuration in `GL_n(F)`. Squaring permutes the
eigenvalues of `b`, so they are roots of unity; the same holds for `c`.
- **Characteristic `p`.** `b` has finite order `n'`, and `c = c^(2^n')` has finite order.
- **Characteristic `0`.** Some `b^N` and `c^L` are unipotent. Write `c^L = exp(X)` with
  `X` nilpotent. From `b^-N c^L b^N = c^(L 2^N)`, injectivity of `exp` on nilpotent
  matrices gives `Ad(b^-N) X = 2^N X`. But `Ad(b^-N)` is unipotent, so `X = 0` and `c^L = 1`.

In a finite product of linear groups the order of `c` is the least common multiple of
finitely many finite orders. []

**Metabelian groups.** `a^-1 b a b^-1 = b` and `b^-1 c b c^-1 = c` show `b, c ∈ G'`. []

**The group `M_1`.** Let `A = <a, b>`. Then `r_A : G_1 -> A`, `c -> 1`, is a retraction
with kernel `N`, and `G_1 = A *_<b> (N_0 ⋊ <b>)` with `N_0 = Z[1/2]` the base of `<b, c>`.
Bass--Serre theory gives `N = *_(g <b> ∈ A/<b>) g N_0 g^-1`. So
`N^ab = ⊕_(A/<b>) Z[1/2]`, the induced module, and `c` maps to the generator of the summand
at the base coset, which has infinite order. So `(a, b, c)` stays a configuration in
`M_1 = G_1 / [N, N]`. `M_1'' <= N^ab`, which is abelian, so `M_1` is solvable of derived
length at most 3, and it is not metabelian by the previous paragraph. For `n >= 0`,
`a^-n b a^n = b^(2^n)` lies in `<b>`, so `b` stabilizes the coset `a^n <b>` and acts on its
summand as `b^(2^n)` acts on `N_0`, that is by `2^(±2^n)`. []
