# EX review, groups: part 4. Permutation stability, Păunescu's class, fixed price, the Q3.4 frame chain

Lane `ex-verify-groups`, 2026-09-13, ~00:30 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 4.1 ex-thompson-v-soficity: `binary-leavitt-unit-group-is-permutation-stable` (8080fb4738). PASS

Re-derived:
- **The fixed-point character.** `χ(g) = lim_ω |Fix φ_n(g)|/k_n` is a character. It is normalized, since
  `φ_n(e)^2 ≈ φ_n(e)` forces `φ_n(e) ≈ id`. It is a class function by bi-invariance. It is positive
  definite by the permutation identity.
- **Two cases.** `binary-leavitt-full-character-simplex` gives `χ = a·1 + (1-a) δ_e`.
  - If `a < 1`, coordinatewise `m`-fold powers have defect at most `m` times larger and fixed-point
    proportion `a^m` off `e`. That is a sofic approximation, which contradicts `openai-leavitt-unit-nonsofic`.
  - So `a = 1` along every `ω`, and `d(φ_n(g), id) -> 0`. The correcting homomorphisms are trivial.
- **Not residually finite.** `V <= H`, and `V` is infinite simple.

Verdict PASS. It is a finitely presented permutation-stable group that is not residually finite. By
Glebsky–Rivera it must be nonsofic, and it is. Novelty: Bradford's 2211.15249 remark is the only source
checked; see the node.

## 4.2 ex-nonsofic-action-entropy: Păunescu's class `𝒮` (3ecde705af, cd3a1a5c40). PASS

- **`sofic-free-actions-are-soe-invariant`.**
  - Feldman–Moore sheets `W_i = {i(w) = i}`.
  - `ι_n(w) = (k_(i(w)) w, i(w))` embeds `R|_(P_n)` into `R|_V x [n]^2`. Sofic products and restrictions
    (Cordeiro 3.5, 3.6, 3.2(a)) make `R|_(P_n)` sofic.
  - Truncation `c_n` costs `O(δ_n)`, and the limit gives amplification. SOE invariance follows through
    Păunescu 1.15.
- **`paunescu-class-is-measure-equivalence-invariant`.**
  - Twisting the coupling by `Z x B`, with `B` the Bernoulli shift of `G x H`, makes both quotient actions
    essentially free and puts `Z` as a factor of `Y_Z`.
  - `R(H ↷ Y_Z) ≅ E|_(D_G^Z)` and `R(G ↷ X_Z) ≅ E|_(D_H^Z)` inside the orbit relation of `G x H`, and both
    domains meet almost every class.
  - SOE invariance carries soficity from `G ↷ X_Z` to `H ↷ Y_Z`. Restricting to the vN algebra of
    `L^∞(Z)` and the `u_h` keeps the diagonal and permutations.
  - Credit note: the node says it may be folklore, after a bounded search.
- **`paunescu-class-closed-under-amenable-extensions`.** The Følner-window induction was checked.
  - Section `s` with `s(1) = 1`, cocycle `h(g,q) = s(gq)^(-1) g s(q) ∈ N`.
  - Exact covariance: `u_h α_(s(q)^(-1))(f) = α_(s(gq)^(-1) g)(f) u_h`.
  - The multiplicative defect lives on `<= |F \ g'^(-1) F|` blocks.
  - The trace is exact: `gq = q` forces `g ∈ N`, and then `h = s(q)^(-1) g s(q) = 1` iff `g = 1`.
  - Completing the block partial permutations costs `O((|F \ g^(-1)F|/|F|)^(1/2))`.
- **`hyperbolic-3-manifold-groups-in-paunescu-class`.**
  - `π_1(S_g) = F_2h *_Z F_2(g-h)`, and 𝒮 is closed under amalgams over amenable subgroups (Păunescu
    Theorem 3.9 import).
  - Agol's virtual fibering gives `π_1(S_g) x| Z`, which is in 𝒮 by the amenable extension theorem.
  - Finite-index overgroups, Selberg's lemma, then measure equivalence between lattices of `PSL_2(C)`.
  - Verdict PASS, resting on the Păunescu permanence and virtual fibering imports.

These results strengthen the lane's positive side (more groups with only sofic actions). None touches
`sl3z-admits-nonsofic-action` or `mixing-free-nonsofic-action-of-sofic-group`, which compute open at
`5e3b2f7eb`.

## 4.3 ex-free-bridges / ex-lueck-approximation: `leavitt-unit-groups-have-fixed-price-one` (b850838e74). PASS

The duplicate `elementary-groups-over-infinite-rings-have-fixed-price-one` was retired by ex-lueck in
e08c416389, in favour of this node.
- Over any ring, `[e_ij(a), e_kl(b)] = 1` for `j != k`, `i != l`, since `E_ij E_kl = E_kl E_ij = 0`.
- Add the root families in the order `E_12, E_13, E_32, E_31, E_23, E_21`. Each new family commutes with
  an infinite family already present: `E_13` with `E_12`, `E_32` with `E_12`, `E_31` with `E_32`, `E_23` with
  `E_13`, `E_21` with `E_23`. So every added generator has an infinite intersection with the current stage.
- Gaboriau's Critère VI.24(3), quoted verbatim in `gaboriau-commensurated-chain-citation`, gives fixed
  price one for `EL_3(R)`, `R` countably infinite. The same works for `r >= 3`.
- `U_K ≅ GL_3(L_K(1,2)) = EL_3` (import). Gaboriau's inequality gives `β_1^(2) <= C - 1 = 0`.

Verdict PASS. Credit: the node assigns the chain to Gaboriau and Furman, and claims only the
noncommutative observation.

## 4.4 ex-q34-collapse: the frame chain (f8d1346e0f, d48bdd179a, 0ae866b209). PASS

- **`block-monomial-hs-models-sofic-mod-amenable-soft-kernel`.**
  - *Hamming comparison.* Columns with `σ(i) != σ'(i)` send `e_i ⊗ v` to orthogonal unit vectors. So
    `||M - M'||_2^2 >= 2 d_H(σ, σ')`, with equality against `(u; id)`. The permutation projection is a
    homomorphism of metric ultraproducts, and `G/A` is sofic for any block size.
  - *Soft kernel.* `ρ(A)` lies in `∏_ω (ℓ^∞_n ⊗ M_k)`, which satisfies Amitsur–Levitzki `S_2k`.
    - Regularity identifies the generated algebra with `L(A)`.
    - A `II_1` summand contains unital `M_m` for `m > k`, where `S_2k` fails. So `L(A)` is type I, hence
      injective, and `A` is amenable.
    - For `k = 1` the algebra is commutative, so `A` is abelian when `ρ` is injective.
- **`coarse-frame-normalizers-are-near-block-monomial`.**
  - `A_ji = Tr(p_j u p_i u^*)/k` is doubly stochastic, and `E_B(u f u^*) = Σ (Af)_j p_j`.
  - Random signs give `(1/n) Σ_(i,j) A_ji^2 >= 1 - δ^2`, hence `(1/n) Σ_i max_j A_ji >= 1 - δ^2`.
  - Argmax is injective where the maximum exceeds `1/2` (row sums are `1`), and at most `2nδ^2` indices
    fail.
  - Orthogonality of the columns `(1 - p_σ(i)) u p_i` gives `3δ^2`.
  - The polar step uses `Tr((1-|b|)^2) <= Tr(1-|b|^2) = k(1 - A_(σ(i) i))`. Total: `2√3 δ`.
- **`monomial-rank-models-are-sofic-over-every-field`.**
  - The column multigraph has degree `<= 2`, with loops, paths and cycles, so
    `|Q|/2 <= rank(A-B) <= |Q|`.
  - Relator holonomies are exact on density `>= 1 - 2Cε`.
  - Labels generate `Z^a x Z/q` (torsion in `K^x` is cyclic). A generic character faithful on torsion
    keeps the finitely many equalities and inequalities.
  - Torsion points are dense in the closed constraint subgroup of the torus, and the inequalities are
    open.
  - The skew product on `[N] x Z/m` is exact. Elek–Szabó amplification finishes.
- **`leavitt-unit-microstates-are-asymptotically-primitive`.** Frame rounding gives block-monomials within
  `2√3 δ`, with multiplicative defect `<= (1 + 6√3) δ`. The permutation skeleton is
  `(F, O(δ^2))`-almost multiplicative. The finitary clause of
  `leavitt-unit-group-has-only-trivial-sofic-morphisms`, consistent with §4.1, fixes all but `εn` blocks.
- **`monomially-hyperlinear-groups-are-sofic` is OPEN,** with Attempts that name the open core (flattening
  curvature with large 2-cycles). Its prediction for the Kun–Thom wreath is recorded, not claimed.

None of these decides Q3.4. `hyperlinear-implies-sofic-via-frame-extraction` requires the open
`hyperlinear-groups-admit-masa-normalizing-microstates`, and `q3-4-resolved` computes open.
