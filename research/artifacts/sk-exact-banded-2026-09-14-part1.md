# sk-exact-banded, part 1 (2026-09-14): reformulations of the exactness question for G_X

Lane sk-exact-banded, wave 12. Plan: `research/artifacts/sk-exact-banded-plan-2026-09-14.md` (b6a40f47f3). The question stays OPEN: is `G_X = EL_3(LC(X,F_2) ⋊ Z)` exact? This part lands two established (unreviewed) transfer results that fix the scope of the problem.

## 1. Linear wobbling group = subshift crossed-product groups
Claim `banded-matrix-groups-are-subshift-crossed-product-groups`, route `banded-matrix-groups-subshift-crossed-product-proof`.
- `GL^band(Z×m;F_q) = GL_m(ℓ^∞(Z,F_q) ⋊ Z) = GL_m(LC(βZ,F_q) ⋊ Z)`.
- A finitely generated subgroup is the faithful orbit-representation image of a subgroup of `GL_m(LC(Y,F_q) ⋊ Z)`, where `Y` is the orbit closure of the point coding its coefficient functions (a transitive subshift). Conversely, every such group embeds.
- So "finitely generated subgroups of the linear wobbling group are exact" is exactly a statement about transitive-subshift crossed-product groups. It implies exactness of every `G_X`, since `G_X ≤ GL^band(Z;F_2)`.

## 2. Transfer across ranks and induced systems
Claim `subshift-el-n-exactness-is-kakutani-invariant`, route `subshift-el-n-exactness-kakutani-invariance-proof`.
- `EL_n(M_k(S)) = EL_{nk}(S)`; `R_{X^{(k)}} ≅ M_k(R_X)` for the `k`-tower system; `EL_n(R_{X_V}) ≤ EL_n(R_X) ≤ EL_{nk}(R_{X_V})` for induced systems.
- Consequences:
  - exactness of `EL_n(R_X)` holds on an initial segment of ranks;
  - "exact in every rank" is a Kakutani-equivalence invariant;
  - "every `G_X` is exact" is equivalent to "every `EL_n(R_X)` is exact".
- What this settles for later work: any exactness proof may pass freely to induced systems (for example, a base with long towers) and to higher rank. Any non-exactness example may be sought in `EL_n` for large `n` over any `X`, and it transfers back to some `G_{X′}`.

## 3. Literature bound
- Two web searches: bounded-displacement and wobbling group exactness; topological full groups and amenable germs.
- One fetch: Corson arXiv:2504.21496, abstract (dyadic rationals in bounded-displacement groups).
- Juschenko–de la Salle, *Invariant means for the wobbling group*, is about invariant means, not exactness.
- No exactness or property A theorem for finitely generated subgroups of `W(Z)`, or for unit groups of algebraic uniform Roe algebras over finite fields, was found.

## 4. What remains (next parts)
- **(P-b)** Uniform property A of the bounded-width fibres `Q_r`. Their coefficient dependency radius `ρ` satisfies `ρ(gh) ≤ ρ(g) + ρ(h) + r`, and `ρ(g) ≤ |g|` in the word metric for the generators `e_ij(u^{±1})`, `e_ij(e_a)`. Words for cylinder transvections of radius `k` can be as short as `O(k log k)`, while general coefficient functions of radius `k` need length exponential in `k`. So the metric on `Q_r` is not comparable to `ρ`, and a direct asdim-0 argument fails.
- **(P-a)** The two-ended lattice space, whose scaling part (locally constant `a` with `a(Tx) ≤ a(x)+1`) has infinite valence. The fibering permanence theorem for property A must be checked at source before use.
- **N3** Faithful banded representations of residually finite non-exact groups. Necessary conditions: no distorted elements (sk-sl3z-bandwidth), and linear Krylov growth `dim span(B_r v) ≤ m(2wr+1)` for finitely supported `v`.
