# Finite triangular extensions of matrix-unit rank models of EL_3 collapse

Lane `gk-rk-extensions` (family R), 2026-09-12. Supports the established claims
`perfect-groups-have-no-triangular-models-with-trivial-diagonal` and
`filtered-matrix-unit-rank-models-of-simple-el3-are-trivial`. It also records what survives
for the open claim `el3-rank-models-factor-through-ring-rank-models`.

Lane `gk-l-gate-neg` named a surviving shape for rank models of `EL_3(R)`: unit root elements
acting through non-split extensions of the natural module by trivial ones, or with
nontrivial complements. Artifact `el3-rank-ring-rigidity-2026-09-12.md` Section 4c records
this as "not covered". This page settles the triangular part of that shape: every finite
extension of matrix-unit pieces, transposed matrix-unit pieces and trivial pieces is
trivial. No cohomology computation is needed, because perfection of `EL_3` kills the
extension terms once the graded pieces die.

## 0. Setting and conventions

* `M` is a unital ring; from Section 2 on, a rank ultraproduct
  `prod_omega M_(n_i)(k) / d_omega` over a field `k` of characteristic `p`, with faithful
  rank function `rk`.
* A **finite decomposition** is `1 = h_1 + ... + h_m` with `h_s h_r = delta_sr h_s`.
* `g` in `M` is **upper triangular** (UT) for it when `h_s g h_r = 0` for all `s > r`.
  Put `f_t = h_1 + ... + h_t`. Then `g` is UT exactly when left multiplication by `g`
  preserves every right ideal `f_t M`. So a UT homomorphism is the same thing as a model
  preserving the finite flag `f_1 M <= f_2 M <= ... <= M`, split by the idempotents `h_t`.
* The UT elements form a unital subring `T`. The **diagonal compression** is
  `D_t(g) = h_t g h_t`.
* Elementary matrices are `x_ij(a) = 1 + a E_ij`. `EL_3(R)` is perfect for every unital ring
  `R`, since `x_ik(a) = [x_ij(a), x_jk(1)]` for distinct `i, j, k`.

## 1. Triangular models of perfect groups

**Lemma 1.** Let `Gamma` be a perfect group and `sigma : Gamma -> M^x` a homomorphism, UT
for a finite decomposition.
1. Each `sigma_t = D_t o sigma` is a homomorphism `Gamma -> (h_t M h_t)^x`.
2. If every `sigma_t` is trivial, meaning `h_t sigma(g) h_t = h_t` for all `g`, then `sigma`
   is trivial.

*Proof.*
1. For `g, h` in `T`, `h_t g h h_t = sum_r (h_t g h_r)(h_r h h_t)`.
   * The terms with `r < t` vanish, since `h_t g h_r = 0` there.
   * The terms with `r > t` vanish, since `h_r h h_t = 0` there.
   * So `D_t(gh) = D_t(g) D_t(h)` and `D_t(1) = h_t`.
   * `sigma(g^-1)` is also in `T`, so `D_t(sigma(g))` is a unit of the corner, and `sigma_t`
     is a homomorphism.
2. Put `N = sum_(s<r) h_s M h_r`, the strictly upper triangular part.
   * `N` is closed under products, and `N^m = 0`.
   * Let `N_k` be the span of the entries `h_s M h_r` with `r - s >= k`. Then `N_k N_l <= N_(k+l)`,
     each `N_k` is a two-sided ideal of `T`, and `N_m = 0`.
   * `U_k = 1 + N_k` is a subgroup of `T^x`.
   * For `x` in `N_k` and `y` in `N_l`, `(1+x)(1+y) = (1+y)(1+x) + (xy - yx)`. So
     `[1+x, 1+y] = 1 + (xy - yx)(1+x)^-1 (1+y)^-1`, which lies in `U_(k+l)`.
   * Hence the `c`-th term of the lower central series of `U_1` lies in `U_c`, and `U_1` is
     nilpotent of class below `m`.
   * If every `sigma_t` is trivial, `sigma(g) - 1` lies in `N = N_1`, so `sigma(Gamma) <= U_1`.
   * A perfect subgroup of a nilpotent group is trivial: `sigma(Gamma)` equals every term of its
     own lower central series, and those terms sit inside `U_c`, which is 1 for `c >= m`.
QED

So, for a perfect group, the trivial homomorphisms into `M^x` are closed under finite
extensions split by idempotents.

## 2. Filtered matrix-unit models of EL_3

Fix a prime `p`, a simple unital algebra `R` over a field of characteristic `p` that is not
directly finite, and a rank ultraproduct `M` over a field of characteristic `p`. Let
`sigma : EL_3(R) -> M^x` be UT for a finite decomposition. Its graded pieces are the
`sigma_t` of Lemma 1.

**Piece types.** Let `h` be one of the `h_t`.
* **Matrix-unit piece.** There are pairwise orthogonal idempotents `p_1, p_2, p_3` in
  `h M h` with `sigma_t(x_ij(1)) = h + u_ij`, `u_ij` in `p_i M p_j`, `u_ij u_jk = u_ik` and
  `u_ij u_ji = p_i` (`i, j, k` distinct). The corners may have any rank and need not add up to
  `h`.
* **Trivial piece.** `sigma_t(x_ij(1)) = h` for all `i != j`. Then `sigma_t` is trivial,
  because `x_ik(a) = [x_ij(a), x_jk(1)]` and `sigma_t(x_jk(1)) = h`. This is also the
  degenerate matrix-unit piece with `p_i = 0`.
* **Transposed piece.** `sigma_t o theta^-1` is a matrix-unit piece for `EL_3(R^op)`. Here
  `theta : EL_3(R) -> EL_3(R^op)`, `theta(g) = (g^T)^-1`, is the isomorphism with
  `theta(x_ij(a)) = x_ji(-a)`. The dual natural module, with `x_ij(1)` acting as `1 - E_ji`,
  is a transposed piece.

**Theorem 2.** If every graded piece of `sigma` is a matrix-unit, trivial or transposed
piece, then `sigma` is trivial.

*Proof.*
* **Corners are rank ultraproducts.** If `rk(h_t) = 0` then `h_t = 0`. Otherwise lift `h_t`
  to idempotents `h_(t,i)` at finite stages. Then `h_t M h_t` is
  `prod_omega M_(rk h_(t,i))(k)` modulo rank-null sequences, with rank renormalized by
  `rk(h_t)`. It is again a rank ultraproduct over characteristic `p`.
* **Matrix-unit pieces.** By `matrix-unit-root-rank-models-of-simple-el3-are-trivial`
  (Corollary 7, `p = 2`) and `matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial`
  (Corollary 9, `p` odd), applied in the corner, `sigma_t` is trivial.
* **Transposed pieces.** `R^op` is simple, and not directly finite, since `ts = 1 != st` in `R`
  gives `s * t = 1 != t * s` in `R^op`. The same corollaries make `sigma_t o theta^-1`
  trivial, so `sigma_t` is trivial.
* **Gluing.** Every graded piece is trivial, and `EL_3(R)` is perfect, so Lemma 1 makes
  `sigma` trivial.
QED

**Shapes covered.** Below, `p = p_1 + p_2 + p_3`, `f = 1 - p`, and the natural block is a
matrix-unit piece on the corners `p_i`.
* **E1, trivial submodule and natural quotient.** Use the decomposition `(h_1, h_2) = (f, p)`.
  Root images `1 + v_ij + d_ij`, with `v_ij` in `p_i M p_j` and `d_ij` in `f M p_j`, are UT.
  This is `0 -> trivial -> W -> natural -> 0`, non-split when `d != 0`.
* **E2, natural submodule and trivial quotient.** Use `(h_1, h_2) = (p, f)`, with extension
  terms `c_ij` in `p_i M f`. This is `0 -> natural -> W -> trivial -> 0`.
* **E3, finite towers.** Any finite chain of natural, dual natural, multiplicity (`natural (x) W`)
  and trivial layers, glued by arbitrary UT terms.
* **Complements.** A complement carrying extension terms toward or away from the natural
  block, as long as the terms go in one direction along some finite ordering.

**Remark (why the extension class dies, seen directly).** Suppose every root image in E1 is
block triangular: `n_ij(a) = v_ij(a) + d_ij(a)`.
* Put `X = n_ij(a)` and `Y = n_jk(b)`. Then `X^2 = Y^2 = YX = 0`, since `p_k (p_i + f) = 0`.
  So `[1+X, 1+Y] = 1 + XY`.
* Reading off blocks: `v_ik(ab) = v_ij(a) v_jk(b)` and `d_ik(ab) = d_ij(a) v_jk(b)`.
* So every extension term is a product with a block term, and it vanishes once the block
  part does.
* In E2 the same computation gives `c_ik(ab) = v_ij(a) c_jk(b)`.
Theorem 2 needs neither formula; this is the mechanism in coordinates.

## 3. What survives

Theorem 2 kills the named surviving shape in its triangular form. The general claim
`el3-rank-models-factor-through-ring-rank-models` stays open. These shapes are not covered:

* **S1, two-sided mixing.** A natural-type composition factor linked to a complement by
  intertwiner terms in both directions, with no finite UT ordering. This is the case of
  Section 4c with `sigma|_(SL_3(F_p)) = (natural (x) W) (+) M'` and `M'` tied to the block from
  both sides, so that the entrywise comparisons of Propositions 6 and 8 acquire terms in
  `p_i M f` and `f M p_j` at once.
* **S2, other composition factors.** Pieces whose unit root elements are not supported on
  three orthogonal corners: Steinberg-type, projective or regular modules of `SL_3(F_p)`, or
  any piece with no block form. Dual natural pieces are now covered, as transposed pieces.
* **S3, diffuse flags.** At finite stages a model can preserve flags of unbounded length whose
  pieces have normalized rank tending to 0. In `M` there may then be no finite decomposition
  with pieces of the types above. Lemma 1's nilpotency class bound needs finite `m`, and a
  perfect group can sit inside an ultraproduct of unipotent groups of growing class. Such an
  object is not nilpotent, so perfection gives nothing there.
* **S4, restatement trap.** "Every rank model admits a finite UT decomposition with
  matrix-unit, transposed or trivial pieces" is equivalent to "every rank model is trivial",
  given Theorem 2, because a trivial model admits the one-piece decomposition. It is not
  landed as a route into the open claim.
* **An untested angle in odd characteristic.** The torus weight idempotents `q_lambda` of
  artifact Section 4d give a canonical finite decomposition, and positive-root logarithms
  raise the weight height. So `sigma(UT_3(R))` is UT for any height ordering. Negative roots
  lower the height, so all of `EL_3(R)` is not UT, and Lemma 1 does not apply as it stands.
  One could apply Lemma 1 to the Borel part and then use the Weyl symmetry. Not attempted
  here.
