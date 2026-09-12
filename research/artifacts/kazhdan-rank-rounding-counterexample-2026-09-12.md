# Property (T) does not round almost-invariant subspaces in normalized rank

Lane `gk-kdf-structure`, 2026-09-12. Supports the Cairn claims
`kazhdan-group-rank-models-admit-no-expander-decomposition` and
`kazhdan-rank-ultraproducts-can-have-diffuse-commutants`, and the Attempts added to
`f2-linear-sofic-groups-kill-rigid-compression-defects`.

## 0. Question and answer

The step (K) of the Hamming normalization proof rounds the approximate action of a
Kazhdan group into expanding pieces
(`research/artifacts/rank-row-compression-audit-2026-09-12.md`, Section 3). The question
was whether property (T) gives this in normalized rank over `F_2`: are almost-invariant
subspaces of rank almost-representations of a Kazhdan group `o(n)`-close to invariant
ones, with constants from the Kazhdan pair? A weaker form asks for a decomposition into
almost-invariant pieces that expand internally.

**No, in any of these forms.** An explicit Kazhdan group has honest irreducible
`F_2`-representations with almost-invariant subspaces of every normalized dimension,
with boundary bounded independently of the dimension (Section 2). Its models admit no
expander decomposition: in every decomposition, the internally expanding pieces carry
total dimension at most `20/kappa` times the leakage (Section 3). In the rank ultraproduct
the relative commutant contains a continuous chain of idempotents, although each
representation is irreducible (Section 4). In normalized Hamming distance and in
normalized Hilbert--Schmidt norm, property (T) rules out each of these phenomena.

The mechanism is the cyclic shift of the audit. It is not carried by the group, which
is Kazhdan, but by the coefficient ring: multiplication by a field generator is a
companion-matrix shift, and its degree truncations are almost invariant.

## 1. The representations

**The group.** `Gamma = EL_3(F_2[t])` with

```text
S = { e_ij(1), e_ij(t) : 1 <= i != j <= 3 },     e_ij(a) = 1 + a E_ij .
```

`S` is a Kazhdan set for `Gamma` by `elementary-group-property-t-over-free-algebras`:
the control set there is every scalar multiple of the unit and every free generator in
each of the six roots, and `F_2[t]` is the free algebra on one generator. Each element of
`S` is an involution, so `S = S^-1`.

**The models.** Fix `k >= 2`, `q = 2^k`, and `alpha` in `F_q` with `F_2[alpha] = F_q`,
whose minimal polynomial has degree `k`. The ring map `t -> alpha` gives

```text
rho_k : Gamma -> EL_3(F_q) = SL_3(F_q) <= GL(F_q^3) = GL_(3k)(F_2),
```

in the `F_2`-basis `alpha^l e_i` (`0 <= l < k`, `i = 1,2,3`). Put `N = F_q^3` over `F_2`,
`n = 3k`, `C` = multiplication by `alpha` on `F_q`, and for `0 <= m <= k`

```text
S_m = span_(F_2){ 1, alpha, ..., alpha^(m-1) },   W_m = S_m^3,   pi_m = the coordinate projection onto S_m,
```

with `pi = pi_m (x) 1_3` projecting onto `W_m`. So `dim W_m = 3m`.

For a subspace `X` and `g` in `Gamma` write

```text
e_g(X) = dim X - dim(X n rho_k(g) X) = dim(X + rho_k(g) X) - dim X,     b(X) = sum_(s in S) e_s(X).
```

The subspace metric is `d(X,Y) = dim X + dim Y - 2 dim(X n Y)`, so `d(X, gX) = 2 e_g(X)`.

**Lemma 1.1 (irreducible).** `rho_k` is surjective onto `SL_3(F_q)`, and its only
invariant `F_2`-subspaces are `0` and `N`. So the only idempotents in `End_Gamma(N)` are
`0` and `1`.

*Proof.*
* **Surjective.** `F_2[t] -> F_q` is onto, so `rho_k` maps the elementary generators onto
  those of `EL_3(F_q)`, and `EL_3 = SL_3` over a field.
* **Irreducible.** `SL_3(F_q)` is transitive on nonzero vectors of `F_q^3`. A nonzero
  invariant subspace therefore contains every nonzero vector.
* **Idempotents.** The image of an idempotent in `End_Gamma(N)` is invariant. QED

**Lemma 1.2 (subadditivity).** For subspaces `X, Y` and `g, h` in `Gamma`:

```text
e_(gh)(X) <= e_g(X) + e_h(X),        e_s(X n Y) <= e_s(X) + e_s(Y).
```

*Proof.*
* **First inequality.** `e_g(X) = d(X, gX)/2`, and
  `d(X, ghX) <= d(X, gX) + d(gX, ghX) = d(X, gX) + d(X, hX)`.
* **Second inequality.** `(X n Y)/(X n Y n sX)` embeds in `X/(X n sX)`, and likewise for
  `Y`. The subspace `(X n Y) n s(X n Y) = (X n Y n sX) n (X n Y n sY)` has codimension in
  `X n Y` at most the sum of the two codimensions. QED

**Lemma 1.3 (the truncations almost commute).** For `0 <= m <= k` and `s` in `S`:

```text
rank[pi, rho_k(e_ij(1))] = 0,    rank[pi, rho_k(e_ij(t))] <= 2,
e_(e_ij(1))(W_m) = 0,            e_(e_ij(t))(W_m) <= 1,             so b(W_m) <= 6.
```

*Proof.*
* **Unit generators.** On `F_2^3 (x) F_q`, `rho_k(e_ij(1)) = 1 + E_ij (x) 1`, which
  commutes with `1_3 (x) pi_m` and preserves `W_m`.
* **The commutator with C.** `rho_k(e_ij(t)) = 1 + E_ij (x) C`, so
  `[pi, rho_k(e_ij(t))] = E_ij (x) [pi_m, C]`. For `m` in `{0, k}` the commutator
  vanishes. For `1 <= m <= k-1`, check on basis vectors:
  * `(pi_m C - C pi_m)(alpha^l) = pi_m(alpha^(l+1)) - alpha^(l+1) = 0` for `l <= m-2`;
  * it equals `-alpha^m` for `l = m-1`;
  * it equals `pi_m(alpha^(l+1)) = 0` for `m <= l <= k-2`;
  * it equals `pi_m(alpha^k)` for `l = k-1`.

  So `rank[pi_m, C] <= 2`.
* **The boundary of W_m.** Write `s = e_ij(t)`. A vector `x` in `W_m` has `s x` in `W_m`
  exactly when `alpha x_j` lies in `S_m`, that is, when `x_j` lies in `S_(m-1)`, because
  `alpha^m` is a basis vector outside `S_m` when `m <= k-1`. So `W_m n s W_m` has
  codimension at most `1` in `W_m`. QED

## 2. No rounding modulus, and not dimension expanders

**Theorem 2.1.** Let `m = floor(k/2)`.
1. `b(W_m) <= 6`, and every `rho_k(Gamma)`-invariant subspace `W'` satisfies
   `d(W_m, W') >= 3 floor(k/2) >= (n-3)/2`.
2. **No rounding modulus.** There is no function `delta` with `delta(eps) -> 0` such that
   every subspace `W` of every honest representation `rho: Gamma -> GL_n(F_2)` with
   `e_s(W) <= eps n` for all `s` in `S` lies within `delta(eps) n` of an invariant
   subspace. A fortiori the same fails for almost-multiplicative maps.
3. **Not dimension expanders.** No `kappa > 0` makes every honest irreducible
   `F_2`-representation of `Gamma` satisfy `b(W) >= kappa dim W` for all `W` with
   `dim W <= n/2`.
4. **Every normalized dimension.** For every `beta` in `[0,1]`, subspaces of normalized
   dimension within `1/k` of `beta` have `b <= 6`.

*Proof.*
1. The bound is Lemma 1.3. By Lemma 1.1, `W'` is `0` or `N`, at distances `3m` and
   `3k - 3m`.
2. Take `rho = rho_k`, `eps = 2/(3k)` and `W = W_m`. The distance is at least
   `(1/2 - 1/(2k)) n`, which does not tend to `0`.
3. `b(W_m)/dim W_m <= 2/floor(k/2) -> 0`.
4. Take `W_(round(beta k))`. QED

The generating set only changes constants: by Lemma 1.2, a finite generating set whose
elements have word length at most `L` in `S` gives boundaries at most `6L`.

**Remark 2.2 (characteristic zero, unitary argument).** Over `C`, (T) does give
dimension expansion. Let `(S, kappa)` be a Kazhdan pair and `pi` an irreducible unitary
representation on `C^n`. Let `W` be a subspace with `dim W <= n/2` and `P` its orthogonal
projection.
* `pi(s) P pi(s)^* - P` vanishes on `(W n sW) (+) (W + sW)^perp`, so it has rank at most
  `2 e_s(W)`. Its operator norm is at most `1`, so its unnormalized squared
  Hilbert--Schmidt norm is at most `2 e_s(W)`.
* `Ad pi` on `HS(C^n)` has only the scalars as invariant vectors, by Schur. The vector
  `xi = P - (dim W/n) 1` is orthogonal to them, with `||xi||_HS^2 = dim W (1 - dim W/n) >= dim W/2`.
* The Kazhdan inequality gives `max_s ||Ad pi(s) xi - xi||_HS >= kappa ||xi||_HS`, hence
  `sum_s e_s(W) >= kappa^2 dim W / 4`.

The argument uses a Hilbert structure that the rank metric over `F_2` lacks. Theorem 2.1
shows the conclusion itself fails there.

## 3. Expander decompositions leak linearly

**Definition.**
* **Decomposition and leakage.** A decomposition of `N` is a family of independent
  subspaces `P_1, ..., P_r`. Its leakage is `Lambda = sum_j b(P_j)`.
* **Internal expansion.** A piece `P` is internally `kappa`-expanding if `b(U) >= kappa dim U`
  for every subspace `U` of `P` with `0 < dim U <= dim P/2`.

The Hamming step (K) uses the stronger notion that counts only the boundary inside the
piece. Projecting along the decomposition shows it is at least as strong as this one, so
the theorem below covers it too.

**Theorem 3.1.** Let `0 < kappa <= 1`.
1. **Exact models.** For every decomposition of `N` for `rho_k`, every internally
   `kappa`-expanding piece `P_j` other than `N` has `dim P_j < 20 b(P_j)/kappa`. `N` itself
   is not internally `kappa`-expanding once `3 floor(k/2) kappa > 6`, and then the expanding
   pieces have total dimension less than `20 Lambda / kappa`. The condition matters: for
   small `k` the decomposition `{N}` can be expanding with `Lambda = 0`. (Scope added by
   gk-verify-pos, 2026-09-12.)
2. **Linear leakage.** Let `3 floor(k/2) kappa > 6`. If the internally `kappa`-expanding
   pieces carry total dimension at least `(1 - lambda) n`, and `Lambda <= lambda n`, then
   `lambda > kappa/21`.
3. **Perturbed models, linear-size pieces.** Let `rho'_k(s)` differ from `rho_k(s)` in
   rank at most `delta_k n` for `s` in `S`, with `delta_k -> 0`. Fix `c > 0`. For large
   `k`, no subspace `P` with `dim P >= c n` and `b'(P) = o(n)` is internally
   `kappa`-expanding for `rho'_k`. Here `b'` and expansion are computed with `rho'_k`.

*Proof.*
1. Let `P = P_j` be proper and nonzero, with `p = dim P` and `U_m = P n W_m`.
   * **Boundary of the piece.** `P` is not invariant (Lemma 1.1), so `b(P) >= 1`.
   * **A half-size subspace.** `U_0 = 0`, `U_k = P`, and `U_(m+1)/U_m` embeds in
     `W_(m+1)/W_m`, which has dimension `3`. Let `m` be largest with `dim U_m <= p/2`.
     Then `p/2 - 3 < dim U_m <= p/2`.
   * **Its boundary.** By Lemmas 1.2 and 1.3, `b(U_m) <= b(P) + 6`.
   * **Large pieces.** If `p >= 8`, then `U_m != 0`, and internal expansion gives
     `kappa (p/2 - 3) < b(P) + 6`. Hence
     `p < 2(b(P) + 6)/kappa + 6 <= 20 b(P)/kappa`, using `b(P) >= 1` and `kappa <= 1`.
   * **Small pieces.** If `p < 8`, then `p < 8 b(P) <= 20 b(P)/kappa`.

   Summing over the expanding pieces gives the bound. For `N` itself, take `U = W_(floor(k/2))`.
2. `(1 - lambda) n < 20 lambda n / kappa`.
3. For `s` in `S` and any subspace `X`, `|e'_s(X) - e_s(X)| <= delta_k n`: the subspaces
   `rho'_k(s) X` and `rho_k(s) X` differ in the subspace metric by at most `2 delta_k n`.
   * **The half-size subspace.** Let `U = P n W_m` be as in 1, computed with the exact
     `rho_k`, so `dim U > p/2 - 3`.
   * **Its boundary for rho'.** `b'(U) <= b(U) + 12 delta_k n <= b(P) + 6 + 12 delta_k n <= b'(P) + 24 delta_k n + 6`.
   * **Contradiction.** Internal expansion would give `kappa (c n/2 - 3) <= o(n)`, which is
     false for large `k`. QED

Part 3 does not cover pieces of sublinear dimension in perturbed models, because the
bound `b(P_j) >= 1` uses exact irreducibility.

## 4. A diffuse relative commutant in the rank ultraproduct

Let `M = prod_omega M_(3k)(F_2)` modulo rank-null sequences, with rank function `rk`, and
`sigma = [rho_k]` : `Gamma -> M^x`.

**Theorem 4.1.**
1. **A chain of commuting idempotents.** For `beta` in `[0,1]` choose `m_k` with
   `m_k/k -> beta`, and put `p_beta = [pi_(m_k) (x) 1_3]`. Then `p_beta` lies in
   `sigma(Gamma)' n M`, `rk p_beta = beta`, and `p_beta p_gamma = p_min(beta,gamma)`.
   Each `rho_k` has only `0` and `1` as idempotents in its commutant.
2. **No atoms.** Every `sigma(Gamma)`-invariant right ideal `eM` contains invariant right
   ideals of every rank in `[0, rk e]`.

*Proof.*
1. By Lemma 1.3, `rank[pi_(m_k) (x) 1_3, rho_k(s)] <= 2 = o(3k)`, and the truncations are
   nested. The finite-stage statement is Lemma 1.1.
2. Choose representatives `V_k` of `eM`, so that `b(V_k) = o(k)`. The subspaces
   `V_k n W_m` are almost invariant by Lemmas 1.2 and 1.3, with boundary at most
   `b(V_k) + 6`. Their dimension moves by at most `3` as `m` increases, from `0` to
   `dim V_k`. So some `m_k` gives `dim(V_k n W_(m_k)) = theta dim V_k + O(1)`. QED

**Remark 4.2 (the other two metrics).** Let `Gamma` be Kazhdan.
* **Normalized Hamming.** For finite transitive actions `Gamma -> Sym(X_k)`, the
  invariant sets of the Loeb ultraproduct have measure `0` or `1`. An almost-invariant
  indicator function is almost invariant in `l^2(X_k)`, and the spectral gap on
  `l^2(X_k)` minus the constants is uniform.
* **Normalized Hilbert--Schmidt.** For irreducible unitary `pi_k`, the relative commutant
  `sigma(Gamma)' n prod_omega M_(n_k)` is the scalars. If `x = [x_k]` with bounded
  representatives has `||[x_k, pi_k(s)]||_2 -> 0`, the spectral gap of `Ad pi_k` on
  `HS` minus the scalars gives `||x_k - tau(x_k) 1||_2 -> 0`.

So among the three rows, only the rank row lets an ultraproduct of irreducible
representations of a Kazhdan group have a diffuse relative commutant.

## 5. What this settles and what it does not

**Settled.**
* Property (T) does not supply step (K) in the rank metric over `F_2`, in the rounding
  form, the dimension-expander form, or the expander-decomposition form (Theorems 2.1
  and 3.1).
* A proof of `f2-linear-sofic-groups-kill-rigid-compression-defects` cannot decompose
  rank models of `Gamma` into expanding pieces on the strength of property (T) alone.
  It needs another input or another mechanism.
* **The Theorem E subgroup has the same models.** `Gamma_E = EL_r(F_2[x_1, ..., x_d])`,
  `r >= 3`, maps `x_l -> alpha`, so every `e_ij(x_l)` goes to `e_ij(alpha)`. The spaces
  `S_m^r` and the bounds carry over, with `b <= r(r-1)d` and steps of dimension `r`.

**Not settled.**
* The rank row itself: `DD(F_2-linear sofic)`.
* Expander decompositions with pieces of sublinear dimension, for perturbed models
  (Theorem 3.1, part 3, covers linear-size pieces only).
* Linear soficity of `L_(F_2)(1,2)^x`. That group has no nontrivial finite-dimensional
  representations, so Theorem 3.1 does not apply to its models.
* Whether the relative commutant in Section 4 is commutative, and whether a size on it
  forbids strict compression. Not analyzed.
