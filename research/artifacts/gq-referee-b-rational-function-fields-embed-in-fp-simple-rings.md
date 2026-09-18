# Referee report (citation/hypothesis lens): gq-ring-fp-simple's envelope theorems

Referee: lane gq-referee-b, 2026-09-17. Reviewed as landed at 36d65161f / fbeff3477:
- `rational-function-fields-embed-in-fp-simple-rings` (+ `-proof`);
- `char-zero-representable-rings-embed-in-fp-simple-rings` (+ `-proof`);
- `field-envelopes-pass-to-algebraic-closures` (+ `-proof`);
- `fp-simple-q-algebras-embed-in-fp-simple-rings` (+ `-proof`);
- the OPEN nodes `countable-char-zero-fields-embed-in-fp-simple-rings` and `char-zero-ring-boone-higman`, with their
  route.

## Verdicts

- All four ESTABLISHED claims: **PASS.** There is one wording amendment (W1).
- Both OPEN nodes: **accurate as stated.**
- Novelty statements are appropriately bounded, with one tightening (W2).

These are not named stepping stones for `G`. The reviews rest on the same unrefereed-then-checked
simplicity criterion as `R_L` (see `gq-referee-b-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md`); the parts used
here are the ones checked there.

## 1. The simplicity criterion with `B = S^{-1}Q[t, registers]`

**Hypotheses.** `K = Q`. `B` is a commutative unital `Q`-algebra, not finitely generated, which is admissible (the
criterion has no finite-generation hypothesis). `ψ = diag(σ_x)` is unital, `d = 5k+3 >= 2`.
- `σ_x` extends to `B` because `σ_x(T) ⊆ T`. This uses the universal property only, so non-injective `σ_x` such as
  `σ_v` are fine.
- `ψ` is injective, because `σ_n` is the restriction of an automorphism of `Frac(Π)` and `B ⊆ Frac(Π)` (`T` avoids
  0).

**The pieces, checked.**
- **Reach.** The formulas for `σ_x*` are as tabulated.
- **Never zero.** `G(τ)` at `t = c` equals `N+1 >= 1`.
- **Every nonzero `q ∈ Z[t]` is `±` a value.** Take `c` with `q(c) ≠ 0` and `N = |q(c)| − 1`.
- **Product-set lemma.** A nonzero polynomial over a domain does not vanish on a product of infinite sets. The sets
  used, `Z`, `{t_1^j}` and `Z_{>=0}`, lie in Reach, which needs `k >= 1` for `{t_1^j}` to be infinite.
- **ψ-minimality.** `(σ_v∘σ)(b) ∈ Q(t)^× ⊆ B^×`.
- **Aperiodicity.**
  - `ψ_{xv}(w)` is a constant fixed by every later letter.
  - Of `xvy` and `xvy'`, at most one is a prefix of `ω^∞`.
  - `w` vanishes on Reach, so `w = 0`.
- **The maps `R_k → O_ψ → R_k`.**
  - `t_uΓs_u` is a two-sided inverse of `ψ_u(G)`, using `Gs_u = s_uψ_u(G)` and `t_uG = ψ_u(G)t_u`.
  - Inverses of units commuting with the commutative image of `Π` commute with it, so `B → R_k` exists.
  - The back map sends `Γ ↦ G^{-1}`.

**Correct.**

**The model and the embeddings.**
- The model is faithful on `B`.
- `F_k` is central, by `ψ(f) = fI`.
- The prefix code `x_i ↦ s_{y'}^{i−1}s_y` gives `F_k`-independent words, so `F_k⟨x⟩ ↪ R_k`. **Correct.**

## 2. The tensor lemma and the centre `Z(L_Q) = Q`

- **Tensor lemma** (`polynomially-representable-envelopes-via-leavitt-tensors` §2): `A` simple and `B` simple with
  centre `K` imply `A ⊗_K B` simple.
  - The standard minimal-length proof is correct as written: normalize the first coefficient to `1` using the
    simplicity of `B`, reduce the other coefficients to central ones, and use the simplicity of `A`.
  - Uses: `A = R_k`, `R` or `S` (simple); `B = L_Q` or `R_L` (centre `Q`). **They match.**
- **Criterion part 4.**
  - The centre computation is: components commute with the core, aperiodicity kills nonzero degrees, and a level-`N`
    matrix commuting with all matrix units is scalar.
  - I read it in `leavitt-nekrashevych-completion-simplicity-proof` §4. For `B = K` it gives `Z(L_K) = K`.
    **Correct.**
- **`Z(R_L) = Q`** (`fp-simple-q-algebras…` §1). The same argument, plus the level-`L+1` step
  `σ_1(w) = σ_2(w)`, gives `w(N+1) = w(0) ∈ Q`, so `w` is constant. **Correct.**

## 3. Standard algebra in the representable proof §2

- **Lasker–Noether.** Primary decomposition in the Noetherian ring `Q[y]` gives `C ↪ ∏ Q[y]/q_j`.
- **Primary quotients.** Zero divisors are nilpotent.
- **Noether normalization.** An injective finite map `Q[t_1..t_k] → A`.
  - A nonzero `a ∈ A_0` is not nilpotent, since `A_0` is reduced and the map injective. So `a` is a non-zero-divisor.
  - So `A ↪ A ⊗_{A_0} F_k`, which is finite-dimensional, and the regular representation is unital and injective.
- **Blocks.** Block-diagonal matrices over `F_{max k_j}`. If every `k_j = 0`, use `Q ⊆ F_1`.
- **Correct.** These are standard textbook theorems (Atiyah–Macdonald Ch. 4; Eisenbud §13 for normalization), used
  exactly within their hypotheses.

The remaining steps are correct:
- flatness over `Q`: `C ⊗ Q⟨x⟩ ⊆ M_e(F_k⟨x⟩)`;
- `M_e` of a finitely presented simple ring is finitely presented and simple;
- the special cases, via a transcendence basis and the regular representation of a finite extension.

## 4. Algebraic closures

- **The host.**
  - `R ⊗_Q L_Q = R ⊗_Z L_Z(1,2)`, which is finitely presented: the union of presentations plus commutation.
  - It is simple by §2.
  - `K ⊗_Q L_Q ↪` it, by flatness.
- **Matrix absorption.**
  - `L_F ≅ L_F^r` as right modules, so `L_F ≅ M_r(L_F)` as `F`-algebras.
  - The compatibility `ι_{i+1}∘κ_i = ι_i` holds because `θ_r` is unital and `F`-linear.
  - Ordering the product basis `{bc}` with `b` outer gives `ρ_{i+1}|_{E_i} = κ_i∘ρ_i`.
- `K̄` is countable because a finitely presented `R` is countable.
- **Finite transcendence degree.** Algebraic over `F_k`. For `k = 0`: `Q̄ ⊆ L_Q ⊆ R_L`, where `L_Q → R_L` is injective
  by simplicity (AGP Thm 4.2, verified at source earlier).

**Correct.**

## 5. The equivalence over `Z` versus over `Q`, and the OPEN nodes

- **`fp-simple-q-algebras…` §2.**
  - Presented as `R_L ⊗_Z Z⟨a⟩/(f_j)`, with rational coefficients written through `u_q`.
  - This equals `R_L ⊗_Q (Q⟨a⟩/J)`, because the ideal generated by the `1 ⊗ f_j` is `R_L ⊗ J` and `R_L ⊗_Q −` is
    exact.
  - **Correct.**
- **W1 (wording, §3).** The rings-to-`Q`-algebras direction writes "put `e = 1_A`" although `A` may be non-unital.
  Use any nonzero `a ∈ A`: if `p·1_R = 0` then `a = p·((1/p)a) = 0`. The conclusion is unchanged.
- **The equivalence** "char-0 ring BH ⇔ algebra BH at `K = Q`". Both are stated for finitely generated
  `Q`-algebras with solvable word problem: `char-zero-ring-boone-higman`, and the root "every finitely generated
  associative `K`-algebra with solvable word problem …". Part 3 transfers envelopes in both directions, so the
  equivalence holds as stated.
- **`countable-char-zero-fields-embed-in-fp-simple-rings`.**
  - The reduction to `K_∞ = Q(t_1, t_2, …)` is correct: a countable transcendence basis gives `K ⊆` the closure of
    `Q(T)`, and the finite-`T` case is already covered.
  - The Attempts remark ("commutative subfields of the core are algebraic over `Frac(B)` by Cayley–Hamilton") is a
    heuristic in an Attempts section. It is not load-bearing and not reviewed. Its coefficients lie in scalar
    matrices `cI`, which are core elements, so it is plausible as stated.

## 6. Evans–Mandelberg–Neff and novelty

- **EMN.** The abstract (ScienceDirect) returned 403 to me, so I cannot confirm the node's quotation. The survey
  arXiv:2306.16356v3 §3, read in the LaTeX in context, says: "analogs of the Boone–Higman theorem have been proven
  for … rings of characteristic p, magmas, loops, and lattices [EMN]". The Boone–Higman theorem there is Theorem 3.6,
  the computably presented simple envelope, which is the weak form. So the node's reading is consistent with the
  survey. Mark the abstract quotation "not re-read by referee".
- **W2 (novelty).** The statements "no priority beyond a bounded search" are appropriate. `char-zero-ring-boone-higman`
  says "found no source for characteristic 0 in either form"; add the MathSciNet/Dniester gap recorded in my `R_L`
  report.
- None of the four claims answers a printed question: the characteristic-0 ring question has no printed source found
  (see the `R_L` report). Keep them described as new constructions, not as answers to open problems.
