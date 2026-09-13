# bV is rationally acyclic: part 2, labelled Thompson groups and products of Cantor sets

Lane z2-09-bv-acyclic, 2026-09-13. Unreviewed. Notation as in part 3.

## Step B: `C(C^j, Q)` is V-acyclic for every `j ≥ 1`

**Input (Palmer–Wu, arXiv:2510.16879, §2.1).** For a discrete group `G`,
elements of the labelled Thompson group `V(G)` are classes of G-tables
`({w'_1, ..., w'_n}, ((g_1, ..., g_n), σ), {w_1, ..., w_n})` under G-expansion
and G-reduction. G-expansion at position `i` replaces `w_i` by `w_i0, w_i1`
(and `w'_{σ(i)}` likewise) and **duplicates the label**:
`(..., g_i, g_i, ...)`.

- Proposition 2.2 realizes `V(G)` as the topological full group of `𝒱_2 × G`.
- Theorem 2.6: "The labelled Thompson group V(G) is acyclic for any discrete group G."

**Lemma B1.** `V(G) ≅ C(C, G) ⋊ V`, where `C(C, G)` is the group of locally
constant maps `C → G` and `V` acts by precomposition.

*Proof.* Forgetting labels is a homomorphism `V(G) → V`, split by the tables
with all labels `1`. Its kernel is the tables `({w}, ((g_i), id), {w})`.
Because expansion duplicates labels, the kernel is the filtered colimit over
dyadic partitions `P` of `G^P` along diagonal refinement maps, which is
`C(C, G)`. Conjugation by a table with permutation `σ` moves labels along the
leaf bijection, which is precomposition by the corresponding element of `V`. ∎

**Lemma B2.** Let `j ≥ 1` and `G = Q^j` (a discrete group). Write
`N = C(C, Q^j) = ⊕_{i=1}^j N_i` with `N_i ≅ C(C, Q)`. Then
`H_p(V; Λ^q_Q N) = 0` for all `(p, q) ≠ (0, 0)`.

*Proof.* `N` is a torsion-free abelian group, so `H_*(N; Q) ≅ Λ^*_Q N`
naturally, hence `V`-equivariantly. The Lyndon–Hochschild–Serre spectral
sequence of `1 → N → V(Q^j) → V → 1` with `Q` coefficients has
`E²_{p,q} = H_p(V; Λ^q_Q N)`. The `V`-stable multigrading gives
`Λ^q_Q N = ⊕_{|μ| = q} ⊗_i Λ^{μ_i} N_i`, where `μ ∈ N^j` and `|μ| = Σ μ_i`.

For `t ∈ (Q^×)^j`, the map `φ_t(f, g) = (t·f, g)` is an automorphism of
`C(C, Q^j) ⋊ V` over the identity of `V`. It commutes with the `V`-action
because `t` acts coordinatewise on labels. It induces an automorphism of the
spectral sequence acting on the `μ`-summand of `E²` by the scalar `t^μ`.

Induction on `r ≥ 2`: suppose `E^r = E²` with this grading, and take `x` in
the `μ`-summand of `E^r_{p,q}`. Write `d^r x = Σ_ν y_ν`. Naturality gives
`t^ν y_ν = t^μ y_ν` for all `t`. The target row is `q + r − 1 ≠ q`, so every
`ν` occurring has `|ν| ≠ |μ|`, hence `ν ≠ μ`. Choosing `t_i = 2` at a
coordinate with `ν_i ≠ μ_i` and `t_k = 1` elsewhere gives `t^ν ≠ t^μ`, so
`y_ν = 0`. Thus `d^r = 0` and `E^{r+1} = E^r`.

So `E² = E^∞`, and `E^∞_{p,q}` are the graded pieces of a finite filtration of
`H_{p+q}(V(Q^j); Q)`. That group is `0` for `p + q ≥ 1` by Theorem 2.6 and
universal coefficients. ∎

**Lemma B3 (= Lemma C3 of part 3).** `C(C^j, Q)` is V-acyclic for every `j ≥ 1`.

*Proof.* The `μ = (1, ..., 1)` summand of `Λ^j_Q N` is `N_1 ⊗_Q ... ⊗_Q N_j`.
This is `V`-isomorphic to `C(C, Q)^{⊗ j} ≅ C(C^j, Q)` with the diagonal action:
indicators of boxes of cones span, and they are independent at each finite
level. Lemma B2 with `q = j ≥ 1` gives `H_p(V; C(C^j, Q)) = 0` for all `p ≥ 0`. ∎

## Integral remark

Over `Z` the scalings `t_i ∈ Z \ {0, ±1}` are only endomorphisms. The same
naturality argument shows that each component of a differential leaving the
multilinear summand is annihilated by the integer `t^ν − t^μ` for all integer
`t`, so by the fixed divisor of `x^ν − x^μ`. That fixed divisor can be `2`, as
for `x² − x`. So integrally only torsion differentials remain possible, and
integral V-acyclicity of `C(C^j, Z)` is open here
(`cantor-power-function-modules-are-v-acyclic`).
