# Finite triangular extensions of matrix-unit rank models of EL_3 collapse

Lane `gk-rk-extensions` (family R), 2026-09-12. Supports the established claims
`perfect-groups-have-no-triangular-models-with-trivial-diagonal`,
`filtered-matrix-unit-rank-models-of-simple-el3-are-trivial` (Sections 1-2),
`unipotent-valued-rank-models-of-el3-are-trivial` and
`flag-preserving-rank-models-of-el3-reduce-to-their-diagonal` (Section 4). It also records what
survives for the open claim `el3-rank-models-factor-through-ring-rank-models`.

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
  object is not nilpotent, so perfection gives nothing there. **Refined in Section 4:** for
  `EL_3` over any ring of characteristic `p` the triangular part carries nothing at any flag
  length. Unitriangular, triangularizable and bounded-block models die. What remains is the
  diffuse block-diagonal model, which is a general rank model on smaller blocks.
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

## 4. Flags of any length: unipotent models and the diagonal model

This section answers the diffuse-flag question S3. A model may preserve flags at finite stages
whose length is unbounded, with pieces of normalized rank tending to 0. Lemma 1's class bound
then fails, and iterating commutator identities along the flag leaks rank at every step. The
argument below uses a different lever: torsion elements of invertible order give an exact
rank identity at every finite stage, with no dependence on nilpotency index or flag length.

Setting: `M = prod_omega M_(n_i)(k) / d_omega` over **any** field `k`. An element `g` of `M^x`
is **unipotent** when it has representatives `g_i` with `g_i - 1` nilpotent for ω-almost
every `i`. The index of nilpotency may be unbounded. Every ultraproduct of unitriangular
groups, for any flags, consists of unipotent elements.

### 4.1 Unipotent models kill torsion of invertible order

**Lemma 3 (exact rank identity).** Let `x` be in `GL_n(k)` with `N = x - 1` nilpotent, and let
`m >= 1` be invertible in `k`. Then `rk(x^m - 1) = rk(x - 1)`.

*Proof.* `x^m - 1 = sum_(l=1..m) binom(m,l) N^l = N c`, where
`c = m + sum_(l=2..m) binom(m,l) N^(l-1)`. `c` is `m` times `1 +` a nilpotent that commutes
with `N`, so it is invertible. QED

*Consequence.* If `g` in `M^x` is unipotent, `g^m = 1` in `M`, and `m` is invertible in `k`,
then `g = 1`. Indeed `g_i^m` represents `g^m = 1`, and `rk(g_i - 1) = rk(g_i^m - 1)`.

**Proposition 4.** Let `Gamma` be a group and `T` the normal subgroup generated by its
elements of finite order invertible in `k`. Every homomorphism `sigma : Gamma -> M^x` with
unipotent values on those elements kills `T`.

**Theorem 5.** Let `R` be a unital ring with `p 1 = 0` for a prime `p`, let `k` be any field,
and let `sigma : EL_3(R) -> M^x` be a homomorphism. Suppose one element `h` has unipotent
image, where `h` is:
* `x_12(1)`, if `char k != p` (including `char k = 0`);
* the image of the permutation matrix of the 3-cycle, if `char k = p = 2`;
* the image of `diag(-1, -1, 1)`, if `char k = p` is odd.

Then `sigma` is trivial. In particular every unipotent-valued model is trivial.

*Proof.*
1. `h` has order `p`, `3` or `2` respectively, which is invertible in `k`. By Lemma 3,
   `sigma(h) = 1`.
2. **`char k != p`.** The Weyl elements `w_ij = x_ij(1) x_ji(-1) x_ij(1)` conjugate `x_12(1)`
   to `x_kl(+-1)` for every `k != l`, so every `sigma(x_kl(1)) = 1`.
3. **`char k = p`.** Let `iota : SL_3(F_p) = EL_3(F_p) -> EL_3(R)` be induced by `F_p -> R`.
   * The kernel `K` of `sigma iota` is normal and contains `h`.
   * `h` is not central: the 3-cycle does not commute with `x_12(1)`, and `diag(-1,-1,1)`
     conjugates `x_13(1)` to `x_13(-1) != x_13(1)` for `p` odd.
   * `PSL_3(F_p)` is simple, so `KZ = SL_3(F_p)`, where `Z` is the center.
   * `SL_3(F_p)/K = KZ/K` is abelian, and `SL_3(F_p)` is perfect, so `K = SL_3(F_p)`.
   * Hence `sigma(x_kl(1)) = 1` for every `k != l`.
4. **All root elements.** For distinct `i, j, k`, `x_ik(a) = [x_ij(a), x_jk(1)]`, so
   `sigma(x_ik(a)) = 1`. Root elements generate `EL_3(R)`.
QED

*What it does not use:* simplicity of `R`, failure of direct finiteness, property (T),
compression, or any bound on flag length or nilpotency index.

*Filter for constructions.* In a nontrivial characteristic-`p` rank model of `EL_3(R)`, the
image of `diag(-1,-1,1)` (`p` odd) or of the 3-cycle (`p = 2`) is not unipotent.

### 4.2 The diagonal model of a flag-preserving model

Let `Gamma` be any group and `sigma : Gamma -> M^x` a homomorphism. A **flag-preserving
presentation** of `sigma` is, for ω-almost every `i`, a decomposition
`k^(n_i) = W_(i,1) (+) ... (+) W_(i,m_i)` with `m_i` arbitrary, such that every `sigma(g)` has
a block upper triangular representative `g_i`, meaning `g_i` maps `W_(i,r)` into
`W_(i,1) (+) ... (+) W_(i,r)`. Put `D_i(x) = sum_t pi_(i,t) x pi_(i,t)`, with `pi_(i,t)` the
projections of the decomposition.

**Remark (invertible representatives; step supplied by `gk-vf-linear`, Section 38).** A
triangular representative need not be an invertible matrix, so it has to be perturbed into one.
* Let `h_i` be a triangular representative of `sigma(g^-1)`. Then `g_i h_i` represents `1`, so
  `rk(g_i h_i - 1) = o(n_i)`.
* By Lemma 6 below, `rk(D_i(g_i h_i) - 1) <= rk(g_i h_i - 1)` and `D_i(g_i h_i) = D_i(g_i) D_i(h_i)`.
  So `rk(D_i(g_i)) >= n_i - o(n_i)`, and the nullities of the diagonal blocks of `g_i` total
  `n_i - rk(D_i(g_i)) = o(n_i)`.
* Add to each singular diagonal block a correction of rank equal to its nullity that makes it
  invertible. The corrections are block diagonal, so triangularity is kept and the total change
  has rank `o(n_i)`.

The perturbed representative is block triangular with invertible diagonal blocks, hence
invertible. From here on triangular representatives are taken invertible, which is what
Proposition 7(b), (c) and Theorem 8.3 use.

**Lemma 6.** For block upper triangular `x, y` in `M_n(k)`:
1. `D(xy) = D(x) D(y)`, and `D(x)` is invertible when `x` is;
2. `rk(D(x)) <= rk(x)`.

*Proof.*
1. Multiplicativity is the computation of Lemma 1, valid for any number of blocks.
   `det x` is the product of the determinants of the diagonal blocks.
2. Choose a basis adapted to the decomposition. In each diagonal block `x_tt` choose an
   invertible square submatrix of size `rk(x_tt)`, with rows `I_t` and columns `J_t` inside
   block `t`. The submatrix of `x` on rows `union I_t` and columns `union J_t` is block upper
   triangular with invertible diagonal blocks, hence invertible. So
   `rk(x) >= sum_t rk(x_tt) = rk(D(x))`.
QED

**Proposition 7 (diagonal model).** `sigma_D(g) = [D_i(g_i)]` is well defined and is a
homomorphism `Gamma -> M^x`. Moreover:
* (a) `rk(sigma_D(g) - 1) <= rk(sigma(g) - 1)`;
* (b) `u(g) = sigma_D(g)^(-1) sigma(g)` is unipotent;
* (c) if `sigma_D` is trivial, `sigma` is unipotent-valued.

*Proof.*
* *Well defined.* Two triangular representatives of `sigma(g)` differ by a triangular
  sequence of vanishing normalized rank, and Lemma 6.2 bounds the difference of their
  diagonals.
* *Homomorphism.* `g_i h_i` is a triangular representative of `sigma(gh)`; apply Lemma 6.1.
* (a) Apply Lemma 6.2 to `g_i - 1`.
* (b) `D_i(g_i)^(-1) g_i` is triangular with identity diagonal blocks, so subtracting `1`
  leaves a strictly block upper triangular, hence nilpotent, matrix.
* (c) `rk(g_i - D_i(g_i)^(-1) g_i) <= rk(D_i(g_i) - 1)`, which vanishes along ω.
QED

**Theorem 8.** Let `R` be a unital ring with `p 1 = 0`, `k` any field, and
`sigma : EL_3(R) -> M^x` a homomorphism with a flag-preserving presentation of any lengths.
Then `sigma` is trivial exactly when `sigma_D` is trivial. In particular:
1. **Unitriangular models are trivial.** If every `sigma(g)` is within rank-null error of a
   unitriangular matrix, then `sigma` is trivial. The flag length may be unbounded and the
   pieces may have normalized rank tending to 0. No common flag is needed: unipotent
   representatives element by element suffice (Theorem 5).
2. **Triangularizable models are trivial.** If every `W_(i,t)` has dimension 1, then
   `sigma_D` takes values in diagonal matrices, which commute. `EL_3(R)` is perfect, so
   `sigma_D` is trivial, and so is `sigma`.
3. **Bounded blocks need a finite-dimensional representation.** Suppose every `W_(i,t)` has
   dimension at most `d` and `sigma` is nontrivial. Then `EL_3(R)` has a nontrivial
   homomorphism into `GL_(d')(K)` for some `d' <= d` and some ultrapower `K` of `k`.

*Proof.* The equivalence is Proposition 7 together with Theorem 5. Parts 1 and 2 follow. For
part 3:
* **Blocks.** By the equivalence `sigma_D` is nontrivial. Write
  `D_i(g_i) = (+)_t rho_(i,t)(g)` with each `rho_(i,t)(g)` invertible. Pick `g_0` and `c > 0`
  with `rk(D_i(g_(0,i)) - 1) >= c n_i` for ω-almost every `i`. Blocks on which
  `rho_(i,t)(g_0) != 1` then carry total dimension at least `c n_i`.
* **Almost all blocks are exact on a finite set.** For a finite `F` in `EL_3(R)` and `g, h` in
  `F`, the relation `sigma_D(gh) = sigma_D(g) sigma_D(h)` gives
  `sum_t rk(rho_(i,t)(gh) - rho_(i,t)(g) rho_(i,t)(h)) = o(n_i)`. A failing block contributes
  rank at least 1 and dimension at most `d`, so failing blocks carry total dimension `o(n_i)`.
* **Choice.** For ω-almost every `i` some block is multiplicative on `F` and nontrivial at
  `g_0`.
* **Ultraproduct.** Take an ultrafilter `U` on the finite subsets of `EL_3(R)` containing
  every set `{F' : F' contains F}`, and fix `d'` on a `U`-large set. The algebraic
  ultraproduct of the chosen blocks is a homomorphism into `GL_(d')(k^U)`, nontrivial at
  `g_0`.
QED

**For the payoff host.** `R = L_(F_2)(1,2)` and `EL_3(R) = R^x`, which is infinite and simple
(`binary-leavitt-unit-group-is-simple`) and finitely generated (host list of
`fg-infinite-simple-groups-are-minimally-almost-periodic`). A nontrivial finite-dimensional
representation over any field would be injective, by simplicity, and its image residually
finite by Malcev (`finitely-generated-linear-groups-are-residually-finite`). An infinite
simple group is not residually finite. So every flag-preserving characteristic-two rank model
of `R^x` with bounded block dimensions is trivial. This is prose here, not a load-bearing part
of any claim.

### 4.3 What survives, refined

* **Diffuse block-diagonal models.** A nontrivial flag-preserving model of `EL_3(R)` has a
  nontrivial diagonal model whose blocks have unbounded dimension and normalized rank tending
  to 0.
  * Each block is an almost homomorphism on `o(n_i)` dimensions. The dimension-weighted
    average of the relative errors tends to 0.
  * If every rank model of `EL_3(R)` over characteristic-`p` ultraproducts is trivial (the
    open claim), then compactness gives uniform smallness on finite sets. Markov's
    inequality over the block weights then kills the diagonal model.
  * So diffuse flags are not an independent obstacle: they reduce to the general claim on
    smaller blocks. They add nothing and remove nothing.
* **General perfect groups at unbounded length.** Proposition 7 holds for any group. Beyond
  Theorem 5, the question is whether a finitely generated perfect group can have a nontrivial
  unipotent-valued rank model.
  * Such a model kills every torsion element of order invertible in `k` (Proposition 4).
  * Iterated commutator identities leak rank `L^r eps` at depth `r`, while the depth needed
    is comparable to the flag length.
  * McLain groups `M(Q, F_p)` are perfect and of unitriangular type, but locally nilpotent, so
    they contain no nontrivial finitely generated perfect subgroup.
  * Candidate shape: scale-invariant strictly triangular operators on a continuous nest,
    where commutators do not accumulate depth additively. Not attempted.
* **Nests in `M` without finite-stage triangular representatives.** A chain of idempotents
  defined only in `M` need not lift to finite-stage flags with triangular representatives.
  The total lower-triangular part over many pieces need not be rank-null, so Proposition 7
  does not apply as stated.
* **Two-sided mixing (S1) and other composition factors (S2)** are unchanged.

### 4.4 The two root identities on the diagonal

Question from lane `gk-l-gate-neg`: does the diagonal reduction commute with the two root
identities of `el3-unit-root-matrix-units-iff-two-root-identities`, `N_12^2 = 0` and
`N_23 N_12 = 0`? It does, in the strongest useful form.

Keep the setting of Section 4.2. Write `D_i(g_i) = (+)_t rho_(i,t)(g)` and
`N^(i,t)_ab = rho_(i,t)(x_ab(1)) - 1`.

**Proposition 9.**
1. **Descent and additivity.** For any noncommutative polynomial `P` in the six displacements
   `N_ab = sigma(x_ab(1)) - 1`, put `P^D = P(N^D)` with `N^D_ab = sigma_D(x_ab(1)) - 1`. Then
   `rk(P^D) <= rk(P)`, and `rk(P^D) = lim_omega sum_t rk(P(N^(i,t))) / n_i`. So an identity
   `P = 0` descends from `sigma` to `sigma_D`. It holds for `sigma_D` exactly when it holds on
   the diagonal blocks in dimension-weighted average.
2. **Localized gate.** Let `R` be a unital algebra of characteristic `p` with no unital ring
   homomorphism into any characteristic-`p` rank ultraproduct, for instance a simple ring that
   is not directly finite, and let `char k = p`. Suppose
   `sum_t rk((N^(i,t)_12)^2) + rk(N^(i,t)_23 N^(i,t)_12) = o(n_i)`; in characteristic two only
   the second term is needed. Then `sigma` is trivial.

*Proof.*
1. The representatives `g_i - 1` of the displacements are block triangular, and so is any
   polynomial in them. `D_i` is additive and multiplicative on block triangular matrices, with
   `D_i(1) = 1`, so `D_i(P(N_i)) = P(D_i(N_i))`. Lemma 6.2 gives the inequality. A block
   diagonal matrix has rank equal to the sum of its block ranks, which gives the additivity.
2. By 1, `sigma_D` satisfies both identities in `M`. By
   `el3-unit-root-matrix-units-iff-two-root-identities`, its unit root elements act by matrix
   units. By `matrix-unit-rank-models-extract-ring-rank-models` and the hypothesis on `R`,
   `sigma_D` is trivial. By `flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`,
   `sigma` is trivial.
QED

*Reading.* For a flag-preserving model the gate identity need not be verified on `sigma`,
where the off-diagonal extension terms enter the products. It suffices to verify it on the
diagonal blocks, each an almost representation on `o(n_i)` dimensions, in weighted average.
The extension part is invisible to the gate.
