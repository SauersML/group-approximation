# Leavitt tensor hosts over every prime field, 2026-09-12

Lane `boone-higman`. This artifact extends
`research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md` (the `F_2`
artifact) from `F_2` to every prime `p`. Write `L_p = L_(F_p)(1,2)`. Boone--Higman
stays open.

**Results.**
1. Khanh's acyclicity criterion (arXiv:2609.08428v1, Theorem 2.2) holds for
   every nonzero unital `F_p`-algebra `A` with `A^2 ≅ A`.
2. His Steinberg comparison criterion (Theorem 5.1) holds for every nonzero
   unital ring, once the transporters are signed.
3. **Host theorem over `F_p`.** Let `B` be a simple unital `F_p`-algebra and
   `R = B ⊗ L_p`, and suppose `K_1(R) = K_2(R) = 0`.
   - `H_1` and `H_2` of every `GL_r(R)` vanish.
   - `GL_m(R) = E_m(R)` for `m >= 2`, and `St_r(R) ≅ GL_r(R)` for `r >= 3`.
   - `R^x` is finitely presented if `B` is a finitely presented ring.
   - If `B` is central simple, `R^x / F_p^x` is simple.
4. **Two finitely presented simple groups for each `p`:** `L_p^x / F_p^x` and
   `(L_p ⊗ L_p)^x / F_p^x`.
5. **Boone--Higman class.** Every finitely generated linear group over a field
   of positive characteristic with transcendence degree at most two satisfies
   Boone--Higman.

For `p = 2` these are the statements already proved in the `F_2` artifact.

## 1. Khanh Section 2 over `F_p`

**Lemma 1.1 (Khanh Lemma 2.3 over `F_p`).** Let `F = F_(p^m)`, `C = F^x` and
`d = p^m - 1`, and regard an `F`-vector space `V` as a discrete group. For
`1 <= j < m`:
- `H_j(V; Z)` is annihilated by `p`, and the norm `N_C` acts as zero on it;
- the same holds for `H_i(H, H_j(V; Z))` whenever a group `H` acts
  `F`-linearly;
- these groups and all their `C`-stable subquotients have zero
  `C`-coinvariants.

*Proof.* Khanh's proof, with the following changes.
1. **Annihilation by `p`.** The cellular chain complex of `BZ/p` alternates the
   differentials `0` and `p`. The same null-homotopy of multiplication by `p` on
   each two-term summand gives `p H_j(V; Z) = 0` for `j > 0`. Then `Z --p--> Z
   -> F_p` gives an injection `H_j(V; Z) -> H_j(V; F_p)`.
2. **Weights.** For `p` odd, `H*(V; F_p) = Λ(V^∨) ⊗ S(βV^∨)`, naturally in
   linear automorphisms: exterior generators in degree 1, Bockstein generators
   in degree 2. After extending scalars, `V^∨` has eigencharacters
   `λ |-> λ^(p^a)`, `0 <= a < m`. So a class of degree `j` has weight a sum of
   `s` members of `{1, p, ..., p^(m-1)}` with `1 <= s <= j`.
3. **Counting.** Replace `p` counters in position `a` by one counter in position
   `a+1` mod `m`.
   - This preserves the residue mod `d` and strictly lowers the count.
   - It stops at digits `0 <= c_a <= p-1` with `Σ c_a <= s < m`.
   - The value `Σ c_a p^a` lies in `[1, d-1]`: it is positive, and it equals
     `d` only if every `c_a = p-1`, which needs `m(p-1) >= m` counters.

   So every weight in degree `0 < j < m` is a nontrivial character of `C`.
4. **Norm and coinvariants.** `d` is prime to `p`, and on a nontrivial character
   in characteristic `p` the norm is zero. The remaining steps are Khanh's, with
   "odd order" read as "order prime to `p`" and "2-primary" as "p-primary". `∎`

**Lemma 1.2 (Khanh Lemma 2.4 over `F_p`).** Verbatim, with `2^n K_n = 0` read
as `p^n K_n = 0`.

**Theorem 1.3 (Khanh Theorem 2.2 over `F_p`).** Let `A` be a nonzero unital
`F_p`-algebra with `A^2 ≅ A`, satisfying hypotheses (1) and (2) of Khanh's
Theorem 2.2. Then `H_n(A^x; Z) = 0` for `n > 0`. The step in degree `n` uses
(1) in degree `n` only and (2) at `r = n+3` only.

*Proof.* Khanh's proof, embedding `F_(p^m)` in `A` through `A ≅ M_m(A)` and
the regular representation `F_(p^m) -> M_m(F_p)`. `∎`

## 2. The Steinberg comparison in every characteristic

**Theorem 2.1.** Let `B` be a nonzero unital ring and `n >= 4`, and assume
hypotheses (1)--(3) of Khanh's Theorem 5.1. Then `φ_n : St_n(B) -> GL_n(B)`
is an isomorphism.

*Proof.* Khanh's proof, with three changes.

1. **Signed transporters.**
   - Let `τ'` send `b_1 -> b_2` and `b_2 -> -b_1`, and `h'` send `b_2 -> b_3`
     and `b_3 -> -b_2`, both fixing the other standard columns. Then `τ' b_1 = b_2`
     and `h' ∈ J`.
   - For `k = k(a,b,H) ∈ K`, conjugation gives
     `η(k) = τ' k τ'^-1 = k(-b, a, H)`.
   - Both `τ' h' τ'` and `h' τ' h'` send `b_1 -> b_3`, `b_2 -> -b_2`,
     `b_3 -> b_1`, so they are equal.
   - The path description of the triangle relation is Khanh's. Hence the
     Borel-construction presentation is
     `Π = <J, T | T k T^-1 = η(k) (k ∈ K), T h' T = h' T h'>`.
2. **Weyl lifts.**
   - Put `W = X_12(-1) X_21(1) X_12(-1)` and
     `W_23 = X_23(-1) X_32(1) X_23(-1)`. They map to `τ'` and `h'`.
   - The Steinberg relations alone give, for `j, i >= 3`:
     - `W X_1j(c) W^-1 = X_2j(c)` and `W X_2j(c) W^-1 = X_1j(-c)`;
     - `W X_i1(c) W^-1 = X_i2(c)` and `W X_i2(c) W^-1 = X_i1(-c)`;
     - `W` commutes with `X_ij(c)` for `i, j >= 3`.
   - For example, conjugating `X_1j(c)` successively by `X_12(-1)`, `X_21(1)`,
     `X_12(-1)` gives `X_1j(c)`, then `X_2j(c) X_1j(c)`, then `X_2j(c)`.
   - Writing `X_12(c) = [X_13(c), X_32(1)]` gives `W X_12(c) W^-1 = X_21(-c)`,
     and similarly for `X_21`.
   - So conjugation by `W` is the substitution
     `X_ij(c) |-> X_(π(i)π(j))(ε_i c ε_j^-1)` read off from the signed matrix
     `τ'`, and likewise for `W_23` and `h'`.
   - Hence `W σ(k) W^-1 = σ(η(k))` for `σ(k(a,b,H)) = ℓ_0(H) x_2(b) x_1(a)`.
     Also `σ(h') = ℓ(H') = W_23`, because `ℓ` does not depend on the elementary
     word.
3. **Central correction.**
   - Composites of substitutions correspond to products of the signed matrices.
     `τ' h' τ' = h' τ' h'`, so `W W_23 W` and `W_23 W W_23` induce the same
     substitution on every generator.
   - So `z = (W_23 W W_23)(W W_23 W)^-1` is central in `St_n(B)` and maps to `1`.
   - Put `ψ(T) = W z`. Centrality keeps `ψ(T) σ(k) ψ(T)^-1 = σ(η(k))`, and
     `ψ(T) σ(h') ψ(T) = z^2 W W_23 W = z W_23 W W_23 = σ(h') ψ(T) σ(h')`.
   - The rest of Khanh's proof is unchanged: `ψ` is a surjective section of
     `φ_n`. `∎`

In characteristic two all signs are trivial and this is Khanh's argument.

## 3. The host theorem over `F_p`

**Theorem 3.1.** Let `B` be a simple unital `F_p`-algebra, `R = B ⊗ L_p`, and
`N >= 1`.
1. If `K_i(R) = 0` for `1 <= i <= N`, then `H_n(GL_r(R); Z) = 0` for
   `1 <= n <= N` and all `r`.
2. If `N >= 2`, then `GL_m(R) = E_m(R)` for `m >= 2` and `St_r(R) ≅ GL_r(R)` for
   `r >= 3`.
3. If moreover `B` is a finitely presented ring, `R^x` is finitely presented.

*Proof.* Sections 2--4 of the `F_2` artifact with `F_2` replaced by `F_p`:
- the division Lemmas 2.1 and 2.2, the frame extension Proposition 2.4 and the
  compression Proposition 3.1 are characteristic-free;
- Theorem 1.3 replaces Khanh's Theorem 2.2;
- Theorem 2.1 replaces his Theorem 5.1;
- Menal--Moncasi GE, Voronetsky's refinement and Krstić--McCool need no
  characteristic hypothesis. `∎`

## 4. Simplicity modulo the centre

**Theorem 4.1.** Let `B` be central simple over `F_p`, `R = B ⊗ L_p` and `n >= 3`.
- `E_n(R)` modulo its centre, the scalars `F_p^x ∩ E_n(R)`, is simple.
- If `K_1(R) = K_2(R) = 0`, then `R^x / F_p^x` is simple, infinite and
  nonabelian.

*Proof.*
1. **Centre.** `Z(R) = Z(B) ⊗ Z(L_p) = F_p`, using
   `leavitt-center-is-coefficient-field`. A matrix commuting with every
   elementary matrix is scalar with central entry, so the centre of `E_n(R)` is
   `F_p^x ∩ E_n(R)`.
2. **Where triviality of the centre enters.** `exists_elGen_mem_of_diagonal` in
   `GroupApproximation/Leavitt/DiagonalNormalExtraction.lean` uses `hcentral`
   only through `center_elementaryGroup_eq_bot_of_units`, to know that the chosen
   `g ∈ N`, `g != 1`, is not central. Its docstring: "Trivial central units rule
   out the only exceptional case: a diagonal element commuting with every
   elementary root."
3. **Root detection.** For a normal `N` not contained in the centre, choose
   `g ∈ N` noncentral. Root detection then gives `e_ij(x) ∈ N` with `x != 0`, and
   strong division gives `N = E_n(R)`.
4. **The unit group.** `R^x ≅ GL_3(R) = E_3(R)` by Theorem 3.1(2), and
   `F_p^x` is its centre. `∎`

## 5. Finitely presented simple groups over each prime field

**Theorem 5.1.** For every prime `p`, the groups `L_p^x / F_p^x` and
`(L_p ⊗ L_p)^x / F_p^x` are finitely presented and simple.

*Proof.*
- **`K`-theory.** ABC Theorem 7.6 with the regular field `F_p` gives
  `K(L_p) = 0`, since `1 - N^t = -1`. Ara--Cortiñas Lemma 6.1 and Proposition 6.2
  over `k = F_p` give `K(L_p ⊗ L_p) = 0`.
- **Coefficients.** Take `B = F_p` or `B = L_p`. Both are central simple and
  finitely presented rings (Khanh's relators (6.1), with `p` in place of `2`).
- **Conclusion.** Theorems 3.1 and 4.1 apply. A finitely presented group modulo
  a finite central subgroup is finitely presented. `∎`

## 6. Linear groups in positive characteristic

**Theorem 6.1.** Let `K` be a field of characteristic `p > 0` with transcendence
degree at most `2`. Every finitely generated `H <= GL_n(K)` embeds in
`(L_p ⊗ L_p)^x / F_p^x`, so it satisfies Boone--Higman.

*Proof.* Lemma 7.1 and Theorem 7.2 of the `F_2` artifact, over `F_p`.
1. **Finite fields.** `F_q` embeds in `M_k(F_p)` through a companion matrix.
2. **Monic normalization.** Put `f = t h / lc(h)`, and in two variables
   `f = t_2 h / c`. Leading coefficients are units after inverting `c`.
3. **The Laurent unit.** The Thompson unit
   `g = s_0 t_0 t_0 + s_1 s_0 t_1 t_0 + s_1 s_1 t_1` of
   `char-two-laurent-linear-groups-proof` acts on the test module over `F_p`
   with pairwise distinct `g^k(v)`. So `F_p[g^±] -> L_p` is injective; that
   argument is characteristic-free.
4. **Embedding.** `H <= GL_N(L_p ⊗ L_p) ≅ (L_p ⊗ L_p)^x`.
5. **Avoiding the centre.** Compose with `x |-> diag(x, 1)` in
   `M_2(L_p ⊗ L_p) ≅ L_p ⊗ L_p`. `diag(x, 1)` is scalar only when `x = 1`, so `H`
   meets `F_p^x` trivially and embeds in the quotient. `∎`

**Examples.**
- `SL_n(F_p[t_1, t_2])` for `n >= 3`.
- The finitely generated subgroups of `GL_n(F_q(t_1, t_2))`.
- `Z/p wr Z^2`.
- Baumslag's finitely presented metabelian group
  `<a, s, t | a^p, [s,t], [a, a^t], a^s = a a^t>`, which is
  `F_p[x^±, (1+x)^-1] ⋊ Z^2 <= GL_2(F_p(x))`. It contains `Z/p wr Z` and is a
  positive-characteristic case of Problem 5.3(7) (finitely presented metabelian
  groups) in the Belk--Bleak--Matucci--Zaremsky survey.

## 7. Limits

- **Characteristic zero.** Lemma 1.1 needs finite fields inside `A`. `L_Z(1,2)`
  contains none, so characteristic zero with positive transcendence degree
  (`GL_n(Q(t))`, `SL_3(Z[t])`) is not reached. Only `GL_n(Q)` is known, by
  Zaremsky.
- **Transcendence degree `>= 3`.** This needs `K_1 = K_2 = 0` for `L_p^(⊗d)`, the
  analogue of `leavitt-tensor-powers-have-trivial-k-theory`.
- **Trust.** Khanh's preprint is unrefereed. Theorem 2.1 reruns his Brown
  presentation with signs, and Lemma 1.1 reruns Quillen's weight count at odd
  `p`. Neither is formalized.
