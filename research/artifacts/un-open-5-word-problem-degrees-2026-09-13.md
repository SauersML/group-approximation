# Word problems of the subshift Kazhdan groups: every Turing degree, all simple, Kazhdan and LEF

Lane `un-open-5`, 2026-09-13. Status: complete written proof by this lane, UNREVIEWED.
It builds on `research/artifacts/un-open-5-marked-subshift-groups-2026-09-13.md` (notation `R_X, G_X, S_X, σ_X, W_w`,
Sturmian subshifts `X_α`).

## 0. Statements

**Theorem 4 (word problem = language).** Let `X ⊆ A^Z` be an infinite minimal subshift and `q` a prime power.
The word problem of `S_X` with respect to `σ_X` is truth-table equivalent to `L(X)`.

**Theorem 5 (Sturmian languages).** For irrational `α ∈ (0,1)`, `L(X_α) ≡_T α`, where `α` stands for its binary
expansion.

**Corollary 6.** For every prime power `q` and every Turing degree `d`, there is an infinite, finitely generated,
simple, Kazhdan, LEF (hence sofic and hyperlinear) group whose word problem has degree `d`. Groups with different
word-problem degrees are not isomorphic. This gives explicit pairwise non-isomorphic continua: `α, β` of
different Turing degree give `S_(X_α) ≇ S_(X_β)`.

Comparison. `fixed-mf-quotient-kazhdan-extensions-realize-all-word-degrees` realizes all degrees by Kazhdan
EXTENSIONS of one fixed LEF endpoint group. There the groups are not simple. Here each group is itself simple.

## 1. Proof of Theorem 4

**(a) `L(X)` reduces to the word problem.** `w ↦ W_w` is computable, and `W_w(σ_X) = 1` iff `w ∉ L(X)`
(`marked-subshift-elementary-group-determines-language`). This is a many-one reduction of the complement of
`L(X)` to the word problem, hence a truth-table reduction of `L(X)`.

**(b) The word problem reduces to `L(X)`.** Let `R_full = LC(A^Z,F_q) ⋊ Z`, the crossed product for the full shift.
- **Data.** An element of `R_full` is a finite sum `Σ_(|j|≤J) f_j u^j`. Each `f_j` is given by a radius `m` and
  a table `A^([−m,m]) → F_q`, meaning `f_j(x) = table(x_[−m,m])`.
- **Operations.** Sums are table addition after padding to a common radius. Products use
  `(f u^i)(g u^j) = f · (g∘T^(−i)) u^(i+j)`, where `g∘T^(−i)` is the same table shifted by `i` coordinates, with
  the radius enlarged by `|i|`. Both are computable.
- **Matrices.** Every entry of a standard generator `e_ij(s)^(±1) = e_ij(±s)`, `s ∈ S_0`, lies in
  `{0, 1, ±u^(±1), ±χ_a, ±θ}`. So for a word `g` in `σ^(±1)` we can compute a matrix `M_g ∈ M_3(R_full)` by
  multiplying out.
- **Restriction.** `π : R_full → R_X`, `f u^j ↦ (f|_X) u^j`, is a ring homomorphism, because restriction
  `LC(A^Z) → LC(X)` is `T`-equivariant. It sends each full-shift generator to the corresponding generator of
  `G_X`. So the image of `g` in `G_X` is `π(M_g)`.
- **Vanishing test.** For `r = Σ_j f_j u^j` with tables of radius `m`: `π(r) = 0` iff `f_j(v) = 0` for every `j`
  and every `v ∈ A^(2m+1)` occurring as `x_[−m,m]` for some `x ∈ X`. By shift invariance, those `v` are exactly
  `L_(2m+1)(X)`. So `π(r) = 0` is decided by finitely many queries `v ∈ L(X)?`, and the list of queries is
  computable from `r`.
- **Triviality in `S_X`.** `g = 1` in `S_X` iff `π(M_g) ∈ Z(G_X)`. Since `Z(G_X) ⊆ F_q^× I_3`
  (`subshift-elementary-group-is-simple-modulo-centre`) and every scalar `c I_3` with `c ∈ F_q^×` that lies in
  `G_X` is central, this holds iff:
  - `π((M_g)_(kl)) = 0` for `k ≠ l`, and
  - there is `c ∈ F_q` (finitely many candidates) with `π((M_g)_(kk) − c·1) = 0` for `k = 1,2,3`.
  All of these are vanishing tests. The queries are fixed in advance, so this is a truth-table reduction. ∎

## 2. Proof of Theorem 5

**(a) `α` reduces to `L(X_α)`.** By the counting identity in `continuum-many-infinite-minimal-binary-subshifts`,
every legal word of length `n` contains `k ∈ {⌊nα⌋, ⌊nα⌋+1}` ones, so `|k/n − α| < 1/n`. With oracle `L(X_α)`,
test the finitely many `w ∈ {0,1}^n` (at least one is legal) and read off `k`. This computes `α` to precision
`1/n` for every `n`. Since `α` is irrational, its binary expansion is computable from such approximations
(no dyadic ties). ∎

**(b) `L(X_α)` reduces to `α`.** Fix `n` and the points `p_t = −tα mod 1` for `0 ≤ t ≤ n`.
- They are pairwise distinct, since `α` is irrational. With oracle `α`, their circular order is computable:
  approximate until all gaps between approximations exceed the error.
- The complementary open arcs (gaps) `Γ_1, …, Γ_(n+1)` are computable, with rational interior points `y_i`
  computable too.
- For `y` in an open gap and `0 ≤ t < n`, we have `y + tα ≢ 0` (else `y = p_t`) and `y + tα ≢ 1−α` (else
  `y = p_(t+1)`). So each coordinate of the length-`n` coding is locally constant on each gap. The word
  `c(y)_[0,n)` is constant on `Γ_i`, and it is computable from a rational `y_i ∈ Γ_i` and approximations of `α`
  (strict comparisons only).
- Every nonempty `J_w` is a union of half-open arcs whose endpoints lie among the `p_t`, so it contains an open
  gap.
- By shift invariance, `L_n(X_α) = {c(y)_[0,n) : y ∈ [0,1)}`, which equals `{c(y_i)_[0,n) : i ≤ n+1}`. This is
  decidable relative to `α`. ∎

## 3. Proof of Corollary 6

- **Choosing `α`.** Given `d`:
  - if `d = 0`, take `α = √2 − 1`;
  - otherwise pick `B ∈ d` and let `α` have binary expansion `0.1 b_0 1 b_1 1 b_2 …`, where `b_i` is the
    indicator of `i ∈ B`. This expansion is not eventually periodic (otherwise `B` would be computable), so `α`
    is irrational. It computes `B` and is computed by `B`, so `α ∈ d`.
- **The group.** By Theorems 4 and 5, the word problem of `S_(X_α)` has degree `d`. By
  `simple-kazhdan-lef-group-from-minimal-subshift`, `S_(X_α)` is infinite, finitely generated, simple, Kazhdan
  and LEF.
- **Isomorphism invariance.** The degree of the word problem does not depend on the finite generating set: a
  change of generators is a computable translation of words. So isomorphic finitely generated groups have equal
  degrees. There are continuum many degrees, which gives explicitly separated continua. ∎

## 4. Scope notes

- Theorem 4 uses neither (T) nor LEF. It holds for `EL_3(R_X)/Z` for every infinite minimal `X`.
- The reduction in Theorem 4(b) is uniform in `X`: one algorithm, with oracle `L(X)`.
- Recalled, not load-bearing: Kuznetsov's theorem that recursively presented simple groups have solvable word
  problem. It is consistent with Corollary 6: for `d ≠ 0`, `S_(X_α)` is not recursively presented. Nothing above
  uses it.
