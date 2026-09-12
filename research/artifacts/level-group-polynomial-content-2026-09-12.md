# Bounded-degree content on level groups

Lane `gk-rk-composition` (family R), 2026-09-12. Supports
`dyadic-involution-profiles-kill-bounded-degree-content`. Attempts entry on
`leavitt-el3-rank-models-over-finite-fields-are-trivial`.

## 0. Setting and summary

* `k` is a field of characteristic `2`.
* `M` is a ring with a faithful normalized Sylvester rank function `rk`, for instance a rank
  ultraproduct `prod_omega M_(n_i)(k) / d_omega`.
* `H = SL_N(F_2) = GL_N(F_2)`, with natural module `V = V_N` and dual `V*`.
* For `1 <= r <= N/2`, `g_r = 1 + n` is an involution with `n^2 = 0` and `rank n = r`. All
  involutions of the same rank `r` are conjugate in `H`.
* `sigma : H -> M^x` is a homomorphism, typically the restriction of a rank model of a larger
  group. Its **involution profile** is `f(r) = rk(sigma(g_r) - 1)`, well defined by conjugacy.

Results:

1. **Polynomial profiles** (Section 2). If `H` acts through a strict polynomial bifunctor `F` of
   total degree at most `D` in `V` and `V*`, the displacement of `g_r` is a polynomial in `r`
   of degree at most `D` that vanishes at `r = 0`.
2. **Dyadic rigidity kills bounded-degree content** (Sections 3 and 4). Suppose `f(2r) = f(r)`
   for `1 <= r <= N/4`, `N >= 4(D+1)`, and `sigma` splits into orthogonal invariant pieces that
   are trivial, projective, or polynomial of degree at most `D`. Then every polynomial piece is
   trivial.
3. **Leavitt application** (Section 5). For `R = L_K(1,2)`, `char K = 2`, Proposition 2 of
   `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md` gives the dyadic identity at every
   level group `SL_(3·2^(k+1))(F_2)`. So natural, dual, natural-plus-dual, adjoint `V (x) V*`,
   and tensor, exterior and symmetric powers of bounded degree never occur as orthogonal pieces
   at level groups. Projective pieces, the Steinberg module included, have profile exactly
   `1/2`, like free content, and survive.
4. **Coefficient remark** (Section 6). Relations with coefficients in the Jacobson subring
   `F_2<s0, t0 | t0 s0 = 1>` already hold in nontrivial models with free constant restriction.
   The landed calibration is `fd-represented-coefficients-violate-two-root-identities`, from lane
   `gk-rk-unipotent`. Section 6 records the Laurent-quotient instance and what a proof must use.

## 1. Pieces

**Definition.** An *H-piece* of `sigma` is an idempotent `e` in `M` commuting with `sigma(H)`,
together with an isomorphism `eMe ~= M_d(k) (x) C_e` sending `e` to `1 (x) 1`, under which
`sigma(h) e = rho(h) (x) 1` for a representation `rho : H -> GL_d(k)`. The piece is:

* *trivial* if `rho` is trivial;
* *projective* if `rho` is a projective `k[H]`-module, free ones included;
* *polynomial of degree at most `D`* if `rho ~= F(V (x) k, V* (x) k)` for a strict polynomial
  bifunctor `F` of total degree at most `D`.

Polynomial pieces include:
* `V^(x a) (x) V*^(x b)` with `a + b <= D`, in particular `V`, `V*` and the adjoint `V (x) V*`;
* exterior, symmetric and divided powers of degree at most `D`, and their sums, subquotients and
  tensor products within the degree bound;
* every simple algebraic module `L(lambda)` whose highest weight is polynomial of degree at most
  `D`, and its dual. These are values of simple strict polynomial functors.

**Additivity.** If `1 = sum_i e_i` is an orthogonal decomposition into pieces, then
`sigma(h)` is block diagonal and

```text
rk(sigma(h) - 1)  =  sum_i  rk(e_i) · rank(rho_i(h) - 1) / d_i .
```

For the second factor: `rk((A - 1) (x) 1)` on `M_d(k) (x) C_e` equals
`rk(e) · rank(A - 1) / d`, since the `d` diagonal matrix units are equivalent idempotents
summing to `e`.

## 2. Jordan counts of involutions

**Lemma 1.** Let `g` be an involution acting on a finite-dimensional `k`-vector space `W`, with
`char k = 2`. Then `W ~= a J_2 (+) b J_1` as a `k[<g>]`-module, where `J_2 = k[Z/2]` and `J_1` is
trivial, and `rank(g - 1) = a`. A projective `k[<g>]`-module is free, so its normalized
displacement is `1/2`.

**Lemma 2 (polynomial profiles).** Let `F` be a strict polynomial bifunctor of total degree at
most `D`. Put `P_F(r) = rank(F(g_r, g_r^(-T)) - 1)` on `F(V, V*)`. For fixed `N`, `P_F` is given
on `0 <= r <= N/2` by a polynomial in `r` with rational coefficients, of degree at most `D`, with
`P_F(0) = 0`.

*Proof.*
1. **Decompose the modules.** As `<g_r>`-modules,
   `V = B_1 (+) ... (+) B_(N-r)` with `B_1, ..., B_r ~= J_2` and the rest `~= J_1`. `V*` has the
   dual decomposition, with `J_2* ~= J_2`.
2. **Weight decomposition.** A strict polynomial bifunctor carries a natural decomposition
   ```text
   F( (+)_a X_a , (+)_b Y_b )  =  (+)_(alpha, beta)  F_(alpha, beta)( X , Y ),
   ```
   namely the weight decomposition under the torus scaling each summand. Each `F_(alpha,beta)`
   has total multidegree at most `D`. It depends only on the summands where `alpha` or `beta` is
   positive, the *effective* summands, of which there are at most `D`. It is symmetric under
   permuting summands of equal type.
3. **Count blocks.** `g_r` acts summand by summand, so each `F_(alpha,beta)` is `<g_r>`-stable.
   By naturality, its `J_2`-count depends only on the degree pattern and on which effective
   summands are of type `J_2`. Let `j_1, j_2` be the numbers of effective `J_2` summands from
   `V` and `V*`, and `t_1, t_2` the numbers of effective `J_1` summands. The number of
   multidegrees with a given pattern is
   `C(r, j_1) C(r, j_2) C(N - 2r, t_1) C(N - 2r, t_2)` times a constant. That is a polynomial in
   `r` of degree `j_1 + j_2 + t_1 + t_2 <= D`.
4. **Evaluate at 0.** If `j_1 = j_2 = 0`, every effective summand is trivial, so
   `F_(alpha,beta)` is a trivial module with no `J_2` blocks. Every term of `P_F` therefore
   carries a factor `C(r, j_1) C(r, j_2)` with `j_1 + j_2 >= 1`, which vanishes at `r = 0`.
QED

*Examples.*
* `V^(x a) (x) V*^(x b)`, `d = a + b`: the `J_1` part is `(N - 2r)^d`-dimensional, so
  `P = (N^d - (N - 2r)^d) / 2`. Normalized, this is `(1 - (1 - 2x)^d)/2` with `x = r/N`.
* `Lambda^i V`: `P = ( [t^i] (1+t)^N  -  [t^i] (1+t^2)^r (1+t)^(N-2r) ) / 2`, a polynomial of
  degree at most `i` in `r`.

## 3. Dyadic rigidity

**Lemma 3.** Let `Q` be a rational polynomial of degree at most `D` with `Q(0) = 0` and
`Q(2r) = Q(r)` at `D + 1` distinct integers `r`. Then `Q = 0`.

*Proof.* `Q(2r) - Q(r) = sum_(j >= 1) c_j (2^j - 1) r^j` has degree at most `D` and `D + 1`
roots, so it is the zero polynomial. So `c_j = 0` for `j >= 1`, and `c_0 = Q(0) = 0`. QED

## 4. Theorem A

**Theorem A** (`dyadic-involution-profiles-kill-bounded-degree-content`). Let
`N >= 4(D + 1)`, `H = SL_N(F_2)`, and `sigma : H -> M^x` as in Section 0. Suppose:

* `1 = sum_i e_i` is a finite orthogonal decomposition into H-pieces, each trivial,
  projective, or polynomial of degree at most `D`;
* `f(2r) = f(r)` for every integer `1 <= r <= N/4`.

Then every polynomial piece is trivial.

*Proof.*
1. **Profile of the pieces.** By Lemma 1, a projective piece contributes exactly
   `rk(e_i)/2` to `f(r)` for every `r >= 1`, and a trivial piece contributes `0`. By Lemma 2 and
   additivity, for integers `1 <= r <= N/2`,
   ```text
   f(r)  =  w_proj / 2  +  Q(r),      Q(r) = sum_(i polynomial) rk(e_i) P_(F_i)(r) / d_i ,
   ```
   where `Q` is a rational polynomial of degree at most `D` with `Q(0) = 0`.
2. **Dyadic rigidity.** The identity `f(2r) = f(r)` holds at the integers `1, ..., floor(N/4)`,
   and `floor(N/4) >= D + 1`. So `Q(2r) = Q(r)` at `D + 1` integers, and Lemma 3 gives `Q = 0`.
3. **Each piece dies.** At `r = 1`, each summand `rk(e_i) P_(F_i)(1) / d_i` is a normalized rank,
   hence nonnegative, and the summands add to `0`. For a piece with `e_i != 0`, faithfulness
   gives `rk(e_i) > 0`, so `P_(F_i)(1) = 0`. Every transvection acts trivially on `F_i(V, V*)`,
   and transvections generate `SL_N(F_2)`, so `rho_i` is trivial.
QED

**Scope.**
* The theorem is a finite-group statement at one level. It needs nothing from the ambient
  group except the dyadic identity on the profile.
* It does not apply to restrictions that are not finite orthogonal sums of such pieces: non-split
  extensions, or pieces of unbounded polynomial degree.
* Projective content is invisible to it, since its profile is constant.

## 5. Leavitt application

Let `R = L_K(1,2)` with `char K = 2`, and take the level groups
`H_k = EL_3(M_(2^k)(F_2)) = SL_(3·2^k)(F_2)` inside `EL_3(R) = R^x`.

**Input: Proposition 2** of `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md` (lane
`gk-l-gate-neg`). For every characteristic-two rank model `sigma` of `R^x` and every `k`, the
profile of `sigma` on `H_(k+1)` satisfies `f_(k+1)(2r) = f_(k+1)(r)` for
`1 <= r <= 3·2^k / 2 = N_(k+1)/4`. Its ingredients:

* **Doubling.** `g` in `H_k` equals `g (x) I_2` in `H_(k+1)`.
* **Compressor.** For `ts = 1`, `u = [[s, 1 - st], [0, t]]` is invertible in `GL_2(R)`, with
  inverse `[[t, 0], [1 - st, s]]`, and `u diag(a, 1) u^(-1) = diag(s a t + 1 - st, 1)`. The
  artifact uses this to identify `g (+) I` with `g` inside `R^x`.

**Consequence.** At every level `N = 3·2^(k+1) >= 4(D + 1)`: if `sigma|_(H_(k+1))` splits into
orthogonal trivial, projective and degree-`<= D` polynomial pieces, the polynomial pieces are
trivial. In particular no char-two rank model of `R^x` restricts at a level group to
* `natural (x) W (+) trivial`,
* `dual (x) W (+) trivial`,
* `natural (+) dual (+) trivial`,
* `adjoint (x) W (+) free (+) trivial`,
* any bounded-degree tensor, exterior or symmetric content with free and trivial complements,

with a nonzero polynomial part.

**What survives this lever:**
* trivial and projective pieces, the Steinberg module `St_N` included;
* pieces of unbounded polynomial degree, for example simple modules whose highest weights grow
  with `N`;
* restrictions that are not orthogonal sums of pieces.

This matches the survivor list of `gk-rk-unipotent`
(`el3-unit-root-matrix-units-iff-two-root-identities`): adjoint, free and projective content are
exactly where `N_23 N_12 != 0`. Adjoint content is now excluded at level groups whenever it splits
off orthogonally.

## 6. Coefficient remark: the Jacobson subring

`fd-represented-coefficients-violate-two-root-identities` (lane `gk-rk-unipotent`) already
records that regular-representation models over finitely represented coefficient rings violate the
two root identities, even over the Toeplitz subring. A concrete instance with nontrivial models:

* **Laurent quotient.** `J = F_2<S, T | TS = 1>` embeds in `R` by `S -> s0, T -> t0`
  (`prime-characteristic-defect-embeds-the-jacobson-algebra`). Its quotient by `(1 - ST)` is
  `F_2[z, z^(-1)]`.
* **The model.** `EL_3(F_2[z, z^(-1)])` is residually finite
  (`laurent-elementary-groups-are-residually-finite`). The ultraproduct of the left regular
  permutation representations of its finite images, pulled back to `EL_3(J)`, is a homomorphism
  into a characteristic-two rank ultraproduct.
* **Its properties.**
  * `rk(sigma(x_12(s0)) - 1) >= 1/2`, since `x_12(z)` moves every point.
  * The constants `SL_3(F_2)` inject into every finite image, so they act freely.
  * The model kills the finitary root elements `x_ij(a)` with `a` in `(1 - s0 t0)`.

So relations with coefficients in `F_2<s0, t0>`, which include `t0 s0 = 1` and the compressor
identity, never force triviality. A proof must use at least one of:
* **Injectivity.** For simple `R^x` a nontrivial model is injective, so it is nontrivial on the
  finitary part, for example `x_12(s1 t1)`, which is conjugate to `x_12(1)` by Proposition 5 of
  the rigidity artifact.
* **The Cuntz relation.** `s0 t0 + s1 t1 = 1`, which makes `1 - s0 t0` generate the whole ring.

## 7. Where this stops

* **Orthogonal splitting.** A general level restriction need not split into orthogonal pieces,
  and rank is not additive over triangular structure. Lane `gk-rk-extensions` supplies the
  reduction for flags (`flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`, 1940cc8920):
  - if `sigma` preserves a finite-stage flag of `EL_3(R)`-invariant subspaces, the diagonal
    compression `sigma_D` is a rank model of the same group;
  - `sigma` is trivial iff `sigma_D` is.
  Proposition 2 uses only exact identities and conjugacies inside the group, so `sigma_D`
  satisfies the dyadic identity too. So Theorem A applies to the graded pieces of any such flag
  whose level restrictions split orthogonally into trivial, projective and polynomial pieces. That
  covers non-split gluing whenever the flag is invariant under the whole group. Level-group
  structure that is invariant only under `H` is not reached.
* **Unbounded degree.** Content whose polynomial degree grows with the level escapes Lemma 3,
  which needs `D + 1 <= N/4`. Degree comparable to `N` can push the profile close to `1/2`, the
  free profile.
* **Projective content.** Its profile is identically `1/2`, so the involution lever cannot
  distinguish it from free content. Any further progress there needs the non-constant root
  elements and, by Section 6, the Cuntz relation or injectivity on the finitary part.
