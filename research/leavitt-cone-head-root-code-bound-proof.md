---
rg: 2
id: leavitt-cone-head-root-code-bound-proof
kind: route
title: Expand the commutator of a product of commuting root elements whose sum lies in the congruence ideal, and absorb the head, which commutes with the root group
target: leavitt-cone-head-is-bounded-by-root-code-leavitt-defects
requires:
  - leavitt-cone-head-bound-is-finite-congruence-gluing
  - leavitt-cuntz-cone-halves-have-rf-amalgam-cover
---

**§0 Conventions.**
- `[a,b] = a b a^(-1) b^(-1)`, and `||.||` is a unitarily invariant norm on `M_d(C)`.
- For unitaries, `||UV - 1|| <= ||U - 1|| + ||V - 1||` and `||W U W^(-1) - 1|| = ||U - 1||`.

**§1 The relators lie in K.**
- Fix `N`, `c ∈ {1,q}`, and words `w, w'` of length `N`.
- `t_w ∈ R_-`, so `x_12(t_w) ∈ Delta_-`. `s_(w') c ∈ R_+`, since `q ∈ R_+`, so `x_23(s_(w') c) ∈ Delta_+`.
- `δ_(w w') c ∈ R_0`, so `x_13(δ_(w w') c) ∈ Delta_0`. Hence `l^c_(w,w')` is a well-defined word in `Gamma`.
- In `Delta = St_20(R)`, `[x_12(a), x_23(b)] = x_13(ab)`.
- In `R`, `t_i s_j = δ_ij`. By induction on `N`,
  `t_w s_(w') = t_(w_N)...t_(w_1) s_(w'_1)...s_(w'_N) = δ_(w w')`.
- So `l^c_(w,w')` maps to `x_13(t_w s_(w') c) x_13(δ c)^(-1) = 1`, i.e. `l^c_(w,w') ∈ K`.

**§2 Items 1 and 2.**
- (Item 1.) `B_- = R_-/I_-` is an `F_2`-vector space of dimension `k_- = log_2 [R_- : I_-] <= d`.
  - The map `F_2^({1,2}^N) -> B_-`, `S -> sum_S t_w mod I_-`, is linear.
  - `C_N(rho)` is its kernel, of codimension at most `k_-`.
- (Item 2.) Let `S ∈ C_N(rho)` be nonzero and `w_0 ∈ S`. Put `b = s_(w_0) c`, `X = rho(x_23(b))`,
  `A_w = rho(x_12(t_w))`, and `Z = rho(x_13(c))`.
  - The `A_w` pairwise commute, since `x_12(R_-)` is abelian in `Delta_- <= GL_20(R)`.
  - `prod_(w∈S) A_w = rho(x_12(sum_S t_w)) = 1`, because `rho` kills `x_12(I_-)`
    (`leavitt-cone-head-bound-is-finite-congruence-gluing` (1)).
- Enumerate `S = {w^1, ..., w^m}` and put `P_j = A_(w^1) ... A_(w^(j-1))`. The identity
  `[UV, X] = U [V, X] U^(-1) [U, X]`, iterated, gives

  ```text
  1 = [A_(w^1) ... A_(w^m), X] = prod_j P'_j E_j P'_j^(-1),         E_j = [A_(w^j), X],     (E)
  ```

  where the `P'_j` are products of the `A_w` and the product runs over `j` in some order.
- By definition `E_j = rho(l^c_(w^j, w_0)) · Z^(δ_j)`, with `δ_j = 1` iff `w^j = w_0`.
- `Z` commutes with every `A_w`: `x_13(c)` and `x_12(t_w)` both lie in `Delta_- <= GL_20(R)`, where
  `x_12(a) x_13(b) = x_13(b) x_12(a)` holds as matrices, and `rho|Delta_-` is a homomorphism.
- So `P' E_j P'^(-1) = (P' D_j P'^(-1)) Z^(δ_j)`, with `D_j = rho(l^c_(w^j, w_0))`.
- `Z` occurs exactly once in (E). So `1 = Y_1 Z Y_2`, where `Y_1` and `Y_2` are products of conjugates of the
  `D_j` in which each `D_j` appears once. Hence `Z = Y_1^(-1) Y_2^(-1)` and

  ```text
  ||Z - 1|| <= ||Y_1 - 1|| + ||Y_2 - 1|| <= sum_j ||D_j - 1||.
  ```

  This is (RC). ∎

**§3 Item 3 (approximate codewords).**
- Let `S` be arbitrary and nonempty, with `A = prod_S A_w = rho(x_12(a))`, `a = sum_S t_w`, and `η = ||A - 1||`.
- Then `||[A, X] - 1|| = ||A X A^(-1) - X|| = ||A X - X A|| <= 2 ||A - 1||`.
- The left side of (E) is now `[A, X]` rather than `1`. The same absorption gives `[A,X] = Y_1 Z Y_2`, hence
  `||Z - 1|| <= ||[A,X] - 1|| + sum_j ||D_j - 1|| <= 2η + sum_j ||D_j - 1||`.
- *Hamming reading.* `rho` restricted to the finite elementary abelian 2-group `x_12(B_-) ≅ (B_-, +)` is a direct
  sum of characters `χ : B_- -> F_2`, acting by `(-1)^(χ(·))`, with normalized multiplicities `μ(χ)`. So
  `||rho(x_12(a)) - 1||_2^2 = sum_χ μ(χ) |(-1)^(χ(a)) - 1|^2 = 4 μ{χ : χ(a) = 1}`. ∎

**§4 Items 4–6 and the class kill.**
- *Collision.* `B_-` has `2^(k_-)` elements. If `2^N > 2^(k_-)`, two words have equal images, or one image is `0`.
  This gives a codeword of weight at most 2.
- *Singleton.* If `2^N > k_-`, the `2^N` images are dependent in a `k_-`-dimensional space. A minimal dependence has at
  most `k_- + 1` terms.
- *General.* (RC) applied to a minimum-weight codeword gives `||Z - 1|| <= d_N · D_N`.
- *Mirror.* Use the codeword `S` of the `s_w c` modulo `I_+`, `A = rho(x_12(t_(w_0)))`, and `X_w = rho(x_23(s_w c))`,
  with the identity `[A, XY] = [A, X] · X [A, Y] X^(-1)`. Now `Z` commutes with every `X_w`, because
  `x_13(c)` and `x_23(·)` commute in `Delta_+`.
- *Cohn shadow (item 5).*
  - The ring maps `s_1, s_2, q -> e_11, e_21, e_11` and `t_1, t_2 -> e_11, e_12` are those of
    `leavitt-cone-head-bound-is-finite-congruence-gluing` (5).
  - Depth 1, `c = q`:
    - `t_1 s_1 q -> e_11`, `t_2 s_2 q -> e_12 e_21 e_11 = e_11`, `t_1 s_2 q -> e_11 e_21 e_11 = 0`, and
      `t_2 s_1 q -> e_12 e_11 e_11 = 0`.
    - So each depth-1 relator maps to `x_13(T S Q - δ Q) = 1`. It is a genuine Steinberg relation in `E_20(M_2(F_2))`.
  - Depth 2:
    - `t_(12) = t_2 t_1 -> e_12 e_11 = 0`, so `S = {12}` is a weight-1 codeword.
    - `s_(12) q = s_1 s_2 q -> e_11 e_21 e_11 = 0`, so `l^q_(12,12) -> x_13(0) z^(-1)`.
- *Truncation ideal.*
  - Let `F = F_2<t_1, t_2, q | q^2 = q, t_1 q = t_1, t_2 q = 0>`.
    - These relations hold in `R`: `t_1 q = t_1 s_1 t_1 = t_1`, and `t_2 q = t_2 s_1 t_1 = 0`.
    - Rewriting `q q -> q`, `t_1 q -> t_1`, `t_2 q -> 0` shows that `F` is spanned by `t_w` and `q t_w`.
  - Their images in `R` are `(s_w)^*` and `(s_w q)^* = (s_w s_1 t_1)^* = s_1 t_(w1)`.
  - These are distinct elements of the standard basis `{s_μ t_ν}` of `L_(F_2)(1,2)`: no `s_μ t_ν` with both `μ` and
    `ν` ending in `2`, where `t_ν := (s_ν)^*`. So `F -> R_-` is an isomorphism with basis `{t_w, q t_w}`.
  - Grade by `deg t_i = 1`, `deg q = 0`. The relations are homogeneous, so `R_-^(>M)` is a two-sided ideal and
    `B_-^(M)` has basis `{t_w, q t_w : |w| <= M}`. In particular the `t_w` with `|w| = N <= M` are independent, and
    `C_N = 0`.
  - `q` survives in `B_-^(M)` for every `M >= 0`.
  - The same holds for `R_+` with basis `{s_w, s_w q}`. On the `+` side this is the path algebra of the quiver with
    vertices `q, 1-q` and arrows `q s_1 q`, `q s_1 (1-q)`, `(1-q) s_2 q`, `(1-q) s_2 (1-q)`.
- *Death step.* A bounded-depth argument in the class must evaluate (RC), or any consequence of exact codes, at a
  codeword of depth `<= N_0`. For `rho` whose negative half factors through `B_-^(M)` with `M >= N_0`, such as the
  regular representation of `E_20(B_-^(M))` restricted to `Delta_-`, none exists.
- This kills only the use of exact ring data. It says nothing about whether such `rho` extend to `Gamma` with small
  `k_i`; that is the open (BW). ∎

**§5 Census (calibration, not load-bearing).**
- `experiments/leavitt-root-code-2026-09-17/root_code_census.py` enumerates the ring maps `R_- -> M_k(F_2)` with
  `Q != 0` up to conjugation of `Q`: exhaustively for `k <= 3`, and 5000 samples per rank for `k = 4`.
- It records the first codeword depth and an upper bound on `min_(N <= 6) N·d_N`, recording weights 1, 2 or 3
  exactly and otherwise the Singleton bound.
- The output is in `census-output.txt`.
  - The maximum cost is 4 at `k = 2`, 6 at `k = 3`, and 8 at `k = 4` (at `r = 2`).
  - The first codeword depth reaches 5 at `k = 4`, `r = 2`.
  - Every shadow with `Q = 1` has `t_2 = 0`, a weight-1 codeword at depth 1.
