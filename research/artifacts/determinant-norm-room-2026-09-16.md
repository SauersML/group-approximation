# Norm room for the determinant conjecture

Lane `hi-fron-determinant-conjecture` (FRONTIER), 2026-09-16. Written proofs,
unreviewed. Numerical sanity checks (finite groups only) are in
`experiments/determinant-norm-room-2026-09-16/norm_room_checks.py`, with
output `output.txt` in the same folder.

The node `determinant-conjecture-counterexample-exists` records that a
violating self-adjoint matrix must have infinite spectrum and norm above two.
This artifact asks how much more room a violation needs, and where the room
stops helping.

- **Theorem A.** Over every group, if the graph of `A` contains no tripod
  `T_(k,k,k)`, then every component stabilizer is finite or virtually cyclic,
  and `A` obeys every Serre inequality. This holds whenever
  `||r_|A|||` is below `3/sqrt 2 = 2.1213...`.
- **Theorem B.** Over every group, a signed matrix of norm below `2.019` obeys
  every Serre inequality. Its norm is either at most `2` or one of the ten
  McKee--Smyth values.
- **Theorem C.** Subdividing a cubic operator over `H` gives operators of norm
  `<= 3/sqrt 2 + 3 * 2^(-(L+1)/2)`, with an exact spectral transfer formula.
  So every Serre violation of a cubic operator of norm below `3` becomes a
  violation just above `3/sqrt 2`, over the same group.

## 0. Conventions and sources

**Operators.**
- `G` is any group and `A in M_n(Z[G])` is self-adjoint.
- `r_A` is right multiplication on `l^2(G)^n = l^2(G x [n])`. Its matrix entry
  between `delta_(x,a)` and `delta_(y,b)` is one integer coefficient of `A_ab`,
  at `x^-1 y` or its inverse depending on convention.
- `|A|` replaces every coefficient by its absolute value. The matrix of
  `r_|A|` is the entrywise absolute value of the matrix of `r_A`.
- `mu_A` is the spectral measure for `Tr = sum_i tau(X_ii)`, of total mass
  `n`. Scaling does not affect Serre inequalities.
- `A` **obeys Serre inequalities** if
  `integral_{Q != 0} log|Q| d mu_A >= 0` for every nonzero `Q in Z[x]`.
  Over a group, this is equivalent to `det_N(G) r_(Q(A)) >= 1` for every such
  `Q`; see `determinant-conjecture-iff-serre-class-spectra`.

**The graph.**
- `Gamma_A` is the graph on `G x [n]` whose edges are the nonzero off-diagonal
  entries of `r_A`.
- `G` acts on it freely by left translation, with at most `n` orbits of
  vertices.
- Every row has finitely many nonzero entries, so the maximum degree `Delta` is
  finite.
- `T_(a,b,c)` is the tree with one center and three legs of `a`, `b` and `c`
  edges.

**Standard facts used.**
- (PF) For finite symmetric matrices `0 <= M <= M'` entrywise,
  `rho(M) <= rho(M')`.
- (Comp) The principal submatrix of a bounded self-adjoint operator on a finite
  set of basis vectors has norm at most the operator norm.
- (Cauchy) Interlacing for principal submatrices.
- (Schur) See Lemma 2.1.
- (SM) Švarc--Milnor.
- (Growth) A finitely generated group of subexponential growth is amenable. A
  finitely generated group of linear growth is finite or virtually infinite
  cyclic.
- (FK) The Fuglede--Kadison determinant is multiplicative on invertible
  elements of `M_N(N(H))`. For normal invertible `T` it equals
  `exp integral log|lambda| d mu_T`.

**Sources read in this session.**

J. McKee and C. Smyth, *Integer symmetric matrices of small spectral radius and
small Mahler measure*, arXiv:0907.0371 (July 2009, by identifier). The TeX
source was fetched from arXiv on 2026-09-16 and Sections 1, 2 and 7 ("Charged
signed graphs of small spectral radius") were read. A journal version (recalled
as IMRN, 2012) is **unverified** and was not checked.

> **Theorem** (label `T:spectral radius`). Up to equivalence, the
> indecomposable integer symmetric matrices having spectral radius less than
> 2.019 are either cyclotomic or have spectral radius equal to one of the ten
> values given in Table 1. The matrices having each such spectral radius are
> also given in this table.

**What Table 1 lists.**
- Radii: 2.00659, 2.00960, 2.01076, 2.01348, 2.01532, 2.01658, 2.01746,
  2.01809, 2.01854, 2.01887.
- Graphs: `10f=T_(1,2,6)`, `10e`, `11c=T_(1,2,7)`, `10d`, `12b=T_(1,2,8)`,
  `9d=T_(1,3,4)`, `10g`, `11a`, `11b`, `13a=T_(1,2,9)`, `10h`,
  `14a=T_(1,2,10)`, `15a`, `16a`, `17a`, `12a`, `18a=T_(1,2,14)`.
- The label is the number of vertices, so every listed matrix has at most 18
  vertices.

**Their conventions.**
- "Integer symmetric matrix" allows every integer entry, diagonal included.
- *Indecomposable* means the graph of nonzero off-diagonal entries is
  connected.
- *Cyclotomic* means spectral radius at most `2`.
- *Equivalence* is `B = +- P^T A P` with `P in O_d(Z)`, which preserves the
  spectral radius.
- In Section 7 the table is produced by growing minimal noncyclotomic graphs.
  The largest graphs found are `T_(1,2,9)`, ..., `T_(1,2,14)` (13 to 18
  vertices). They also remark that above `2.019800887...`, the limit of the
  spectral radius of `T_(1,2,n)`, infinitely many matrices occur.

## 1. Component decomposition

This is steps 3--4 of `norm-two-integral-matrices-virtually-cyclic-proof`,
stated with no norm hypothesis.

**Lemma 1.1.** Let `A in M_n(Z[G])` be self-adjoint, let `C` be a component of
`Gamma_A`, and let `K_C = {g in G : gC = C}`.

1. `K_C` acts freely on `C`, with one orbit on each nonempty
   `C cap (G x {j})`. Write `J_C` for the set of such `j`, and pick
   `(h_j, j) in C`.
2. `r_A` preserves `l^2(C)`, and there is a self-adjoint
   `A_C in M_(J_C)(Z[K_C])` such that `r_A` on `l^2(C)` is unitarily equivalent
   to `r_(A_C)`.
3. Choose one component `C` in each `G`-orbit of components. The sets `J_C`
   partition `[n]`, and
   `mu_A = sum_C mu_(A_C)`.
4. If `C` is finite then `K_C` is finite. If `C` is infinite and
   `|B_r(v)| <= c(1 + r)` for all `r` and some `v in C`, then `K_C` is finitely
   generated of linear growth, hence virtually infinite cyclic.

*Proof.*

(1) If `(h, j)` and `(h', j)` lie in `C`, then `h'h^-1` maps the first to the
second. Components are equal or disjoint, so `h'h^-1 in K_C`. Freeness is
inherited from `G`. Hence `C = disjoint union over j in J_C of (K_C h_j) x {j}`.

(2) The matrix entries of `r_A` join vertices of the same component, so
`l^2(C)` is invariant. Identify `(k h_j, j)` with `(k, j)` for `k in K_C`.
- The entry between `(k h_i, i)` and `(k' h_j, j)` is the coefficient of `A_ij`
  at `h_i^-1 (k^-1 k') h_j` (in the convention of Section 0).
- It depends only on `k^-1 k'`, and only finitely many `x in K_C` give a nonzero
  coefficient `(A_C)_ij(x)` of `A_ij` at `h_i^-1 x h_j`.
- So `A_C in M_(J_C)(Z[K_C])`, and the identification carries `r_A` on
  `l^2(C)` to `r_(A_C)`.

(3) Each `(e, j)` lies in exactly one component, and its orbit has exactly one
representative `C`. If `(h, j) in C` and `(h', j) in C'` for representatives
`C` and `C'`, then `C' = h'h^-1 C`, so `C = C'`. Hence the `J_C` partition
`[n]`. For every bounded Borel `f`, `G`-invariance gives
`<f(r_A) delta_(e,j), delta_(e,j)> = <f(r_A) delta_(h_j,j), delta_(h_j,j)>`.
By (2) this equals `<f(r_(A_C)) delta_(e,j), delta_(e,j)>`. Summing over `j`
gives the formula.

(4) `K_C` acts freely by graph automorphisms, with finitely many orbits, on the
connected locally finite graph `C`.
- By (SM), `K_C` is finitely generated and the orbit map `k -> kv` is a
  quasi-isometry.
- The orbit map is injective and `c'`-Lipschitz for the word metric, so the
  `R`-ball of `K_C` has at most `|B_(c'R)(v)| <= c(1 + c'R)` elements.
- Apply (Growth). QED

**Corollary 1.2.** Suppose every component stabilizer `K_C` is sofic, for
instance amenable. Then:
- `A` obeys every Serre inequality, and `det_N(G) r_(Q(A)) >= 1` for every
  nonzero `Q in Z[x]`;
- every eigenvalue of `r_A` is an algebraic integer, and Galois-conjugate
  eigenvalues have equal `Tr`-multiplicity.

*Proof.* There are finitely many representatives `C`.
- Each `mu_(A_C)` obeys every Serre inequality, by
  `determinant-conjecture-holds-for-sofic-groups` and
  `determinant-conjecture-iff-serre-class-spectra` applied to `K_C`.
- The inequalities are additive in the measure.
- Eigenvalue masses add over `C`, and each `A_C` has balanced eigenvalues by
  `integral-eigenvalues-galois-balanced-for-sofic-groups`.
- `det_N(G) r_(Q(A)) = exp integral_{Q != 0} log|Q| d mu_A` for self-adjoint
  `A`. QED

## 2. Tripods and the Schur test

**Lemma 2.1 (Schur test).** Let `M` be a bounded symmetric operator on
`l^2(V)` with entries `M_uv >= 0`, and suppose `f : V -> (0, infinity)` has
`(Mf)(u) <= lambda f(u)` for all `u`. Then `||M|| <= lambda`.

*Proof.* For finitely supported `x`, by AM--GM,

```text
|<Mx, x>| <= sum_(u,v) M_uv |x_u||x_v|
          <= sum_(u,v) M_uv (x_u^2 f_v/f_u + x_v^2 f_u/f_v)/2
          =  sum_u x_u^2 (Mf)(u)/f(u)
          <= lambda ||x||^2.
```

`M` is self-adjoint, so `||M|| = sup |<Mx,x>|/||x||^2`. QED

**Lemma 2.2 (tripods).** Put `lambda_* = 3/sqrt 2 = 2.12132...`. Then
`rho(T_(k,k,k))` is nondecreasing in `k`, satisfies `rho(T_(k,k,k)) <= lambda_*`,
and

```text
rho(T_(k,k,k))  >=  R_k := 6 * 2^(-1/2) * (2 - 2^(1-k)) / (4 - 3 * 2^(-k))  -->  lambda_*.
```

*Proof.* Monotonicity: `T_(k,k,k)` is a subgraph of `T_(k+1,k+1,k+1)`; use (PF).

Upper bound: apply Lemma 2.1 with `f(center) = 1` and `f = 2^(-j/2)` at distance
`j` on each leg.
- At the center, `Tf = 3 * 2^(-1/2) = lambda_* f`.
- At an interior leg vertex, `Tf = 2^(-(j-1)/2) + 2^(-(j+1)/2) = lambda_* f`.
- At a leaf, `Tf = 2^(-(k-1)/2) = sqrt 2 * f <= lambda_* f`.

Lower bound: take the same vector `x` as a Rayleigh test vector.
- `<x,x> = 1 + 3 sum_(j=1..k) 2^(-j) = 4 - 3 * 2^(-k)`.
- `<Tx,x> = 2(3 * 2^(-1/2) + 3 sum_(j=1..k-1) 2^(-(2j+1)/2))
  = 6 * 2^(-1/2) (2 - 2^(1-k))`.

As `k -> infinity`, the ratio `R_k` tends to `12 * 2^(-1/2) / 4 = lambda_*`. QED

Numerically (`output.txt`):

| `k` | `rho(T_(k,k,k))` |
| --- | --- |
| 1 | 1.7321 |
| 2 | 2 |
| 3 | 2.0743 |
| 4 | 2.1010 |
| 8 | 2.12026 |
| 30 | `lambda_* - 2.5e-10` |

So `rho(T_(3,3,3)) > 2.019` and `rho(T_(4,4,4)) > 2.1`.

**Lemma 2.3 (subgraphs bound the absolute norm).** If `Gamma_A` contains a finite
tree `T` as a subgraph (not necessarily induced), then
`rho(T) <= ||r_|A|||`.

*Proof.* Let `V` be the vertex set of the copy of `T` and `M` the principal
submatrix of `r_|A|` on `V`.
- `M >= 0` entrywise. Every edge of `T` is a nonzero integer entry, so it has
  absolute value at least `1`.
- Hence `M >=` the adjacency matrix of `T` entrywise, and `rho(T) <= rho(M)` by
  (PF).
- `rho(M) = ||M|| <= ||r_|A|||` by (Comp). QED

The same bound holds with `r_A` in place of `r_|A|` when all coefficients of `A`
are nonnegative, or more generally when the copy of `T` is induced and carries no
charges. A tree has no cycles, so its signs can be switched away, and the
principal submatrix is then equivalent to `adj(T)`. Charges and extra chords
break this, which is why Theorem A uses `|A|`.

## 3. Theorem A: tripod-free matrices

**Theorem A.** Let `G` be any group, `A in M_n(Z[G])` self-adjoint, and `Delta`
the maximum degree of `Gamma_A`. Suppose that for some `k >= 1`, `Gamma_A`
contains no subgraph isomorphic to `T_(k,k,k)`. Then:

1. every sphere of radius `r >= 2k` in `Gamma_A` has at most `Delta^(2k)`
   vertices, so `|B_r(v)| <= (2k + r + 1) Delta^(2k)`;
2. every component stabilizer `K_C` is finite or virtually infinite cyclic;
3. `mu_A = sum_C mu_(A_C)` with `A_C` over these stabilizers;
4. `A` obeys every Serre inequality, and `det_N(G) r_(Q(A)) >= 1` for every
   nonzero `Q in Z[x]`;
5. eigenvalues of `r_A` are algebraic integers, and conjugates carry equal
   `Tr`-multiplicity.

The hypothesis holds whenever `||r_|A||| < 3/sqrt 2`. Choose `k` with
`R_k > ||r_|A|||` (Lemma 2.2); Lemma 2.3 then excludes `T_(k,k,k)`.

**Lemma 3.1 (branching forces a tripod).** Let `Gamma` be a connected locally
finite graph, `v` a vertex, and `S_j` the sphere of radius `j` about `v`.
- Choose a BFS tree `T`: every `u in S_j` with `j >= 1` gets one parent in
  `S_(j-1)` adjacent to it.
- Fix `r`, and let `L_j` (`0 <= j <= r`) be the set of `u in S_j` that have a
  `T`-descendant in `S_r`.

If some `x in L_j` with `k <= j <= r - k` has two distinct children in
`L_(j+1)`, then `Gamma` contains `T_(k,k,k)` as a subgraph.

*Proof.* Let `y` and `y'` be the two children. The three legs at `x` are:
- **Leg 1.** The `T`-path from `x` up to its ancestor in `S_(j-k)`, using
  `j >= k`. Its vertices other than `x` lie in levels `j-k, ..., j-1`.
- **Leg 2.** The first `k` edges of the `T`-path from `x` through `y` to a
  descendant of `y` in `S_r`, using `j + k <= r`. Its vertices other than `x`
  lie in levels `j+1, ..., j+k`, inside the subtree of `y`.
- **Leg 3.** The same through `y'`, inside the subtree of `y'`.

The subtrees of the siblings `y` and `y'` are disjoint, and levels separate
leg 1 from legs 2 and 3. So the three legs meet only at `x`. All edges are tree
edges, hence edges of `Gamma`. QED

*Proof of Theorem A.* Fix a vertex `v` and `r >= 2k`, and use the notation of
Lemma 3.1.
- Every `u in L_(j+1)` has its parent in `L_j`, and every `u in L_j` with
  `j < r` has at least one child in `L_(j+1)`. So `|L_j| <= |L_(j+1)|`.
- By Lemma 3.1 no vertex of `L_j` with `k <= j <= r-k` has two children in
  `L_(j+1)`. Hence `|L_(r-k+1)| = |L_k| <= |S_k| <= Delta^k`.
- Each vertex at level at least `1` has at most `Delta - 1` children, so
  `|S_r| = |L_r| <= (Delta-1)^(k-1) |L_(r-k+1)| <= Delta^(2k)`.

Summing over the spheres gives (1). Items (2) and (3) follow from Lemma 1.1(4)
and 1.1(3). Amenable groups are sofic, so Corollary 1.2 gives (4) and (5). QED

**Remarks.**

- *Comparison with the norm-two claim.*
  `norm-two-integral-matrices-reduce-to-virtually-cyclic-groups` assumes
  `||r_A|| <= 2`. Theorem A assumes `||r_|A||| < 3/sqrt 2`. For nonnegative `A`
  it strictly extends the Serre range from norm `<= 2` to norm `< 2.1213...`.
  For signed matrices the two are incomparable. The signed tessellations
  `T_(2k)` have norm `2`, but `|T_(2k)|` is 4-regular with norm `4`.
- *Tripod-freeness is sufficient, not necessary.* The ladder `Z x {0,1}` is
  invariant under `Z`, and it contains `T_(k,k,k)` for every `k`. So the growth
  argument uses only part of the room that virtually cyclic stabilizers allow.
- *Rectangular matrices.* `|B^* B| <= |B|^* |B|` entrywise, so
  `||r_|B^*B||| <= ||r_|B|||^2`. Every `B in M_(m x n)(Z[G])` with
  `||r_|B||| < (3/sqrt 2)^(1/2) = 1.4565...` has `det_N(G) r_B >= 1`.
- *Exactly at `3/sqrt 2`.* The proof needs strict inequality, since every finite
  tripod has `rho < 3/sqrt 2`. Whether `||r_|A||| = 3/sqrt 2` still forces
  amenable stabilizers is open. Section 5 shows that every `3/sqrt 2 + eps` is
  already too much.

## 4. Theorem B: signed matrices below 2.019

**Theorem B.** Let `G` be any group and `A in M_n(Z[G])` self-adjoint with
`||r_A|| < 2.019`. Then:

1. every finite set `S` inside an infinite component of `Gamma_A` gives a
   principal submatrix of `r_A` with spectral radius at most `2`, so `r_A`
   restricted to the infinite components has norm at most `2`;
2. `[n] = J_fin disjoint union J_inf`, according to whether the component of
   `(e, j)` is finite or infinite. After permuting indices,
   `A = A_fin (+) A_inf` with `A_fin in M_(J_fin)(Z[G])`,
   `A_inf in M_(J_inf)(Z[G])` and `mu_A = mu_(A_fin) + mu_(A_inf)`;
3. `r_(A_fin)` has finite spectrum and `||r_(A_inf)|| <= 2`;
4. `A` obeys every Serre inequality, `det_N(G) r_(Q(A)) >= 1` for all nonzero
   `Q in Z[x]`, and eigenvalues are algebraic integers with Galois-equal
   masses;
5. **norm quantization.** `||r_A||` is at most `2` or equals one of the ten
   values of McKee--Smyth Table 1. In the second case the norm is attained on
   a finite component whose matrix is one of the 17 listed charged signed
   graphs.

*Proof.*

(1) Let `C` be an infinite component and `S subset C` finite, and enlarge `S`
to be connected. The principal submatrix `M_S` of `r_A` on `S` is an
indecomposable integer symmetric matrix with `rho(M_S) <= ||r_A|| < 2.019` (Comp).

Suppose `rho(M_S) > 2`. If `|S| >= 19`, put `S' = S`. Otherwise `C` is infinite
and connected, so adding neighbours one at a time gives a connected
`S' supset S` with `|S'| = 19`.
- By (Cauchy), `rho(M_(S')) >= rho(M_S) > 2`.
- By (Comp), `rho(M_(S')) < 2.019`.
- So `M_(S')` is noncyclotomic and indecomposable with radius below `2.019` and
  at least 19 vertices, contradicting McKee--Smyth Table 1, where every matrix
  has at most 18 vertices.

So `rho(M_S) <= 2`. A finitely supported vector lies in some such `S`, so
`|<r_A x, x>| <= 2||x||^2` on `l^2(C)`, and `r_A` on `l^2(C)` has norm at most
`2`. Summing over the orthogonal components gives the second half of (1).

(2) If the coefficient of `A_ij` at `t` is nonzero with `i != j` or `t != e`,
then `(e, i)` and `(t, j)` are adjacent. The component of `(t, j)` is the
`t`-translate of that of `(e, j)`, so both have the same cardinality. Hence
`A_ij = 0` whenever `i` and `j` lie in different classes. The spectral measure
splits along the block decomposition.

(3) For `A_fin`, every component of `Gamma_(A_fin)` is finite. Components form
finitely many `G`-orbits (Lemma 1.1(3)), and translates carry identical
matrices. So `r_(A_fin)` is an orthogonal sum of copies of finitely many finite
integer symmetric matrices, and its spectrum is the finite union of their
spectra. The bound `||r_(A_inf)|| <= 2` is (1).

(4) Apply `finite-spectrum-integral-elements-obey-determinant` to `A_fin`, and
`norm-two-integral-matrices-reduce-to-virtually-cyclic-groups` to `A_inf`. Both
give every Serre inequality and Galois-equal masses. Masses and Serre integrals
add over the two blocks.

(5) `||r_A|| = max(||r_(A_fin)||, ||r_(A_inf)||)`, and `||r_(A_fin)||` is the
maximum spectral radius of the finitely many finite component matrices. If
`||r_A|| > 2`, it is the spectral radius of a noncyclotomic indecomposable
integer symmetric matrix of radius below `2.019`. Apply McKee--Smyth. QED

**Remarks.**

- *Relation to `integral-operator-norm-below-two-is-quantized`.* That claim
  says norms below `2` are `2cos(pi/q)`. Theorem B(5) continues the
  quantization up to `2.019`: between `2` and `2.019` only ten norms occur, and
  only through finite components.
- *Why 2.019.* The spectral radius of `T_(1,2,m)` increases to
  `2.019800887...`, so beyond that finite components of unbounded size occur,
  and no finite table exists. For unsigned graphs, Brouwer--Neumaier and
  Cvetković--Doob--Gutman classify all graphs below `sqrt(2 + sqrt 5)` (cited
  from the McKee--Smyth introduction, not read). For signed matrices, McKee and
  Smyth say the range `(2, sqrt(2+sqrt 5))` is not yet analysed.
- *What B adds to A.* For signed matrices, Theorem B allows `|A|` of large norm,
  for example tessellation-like infinite components with cancellations,
  provided `||r_A|| < 2.019`.

## 5. Theorem C: subdivided cubic operators

**Definitions.**

*Cubic operator.* `B in M_k(Z[H])` is **cubic without inversions** if it is
self-adjoint with nonnegative integer coefficients and:
- every row has coefficient sum `3`;
- no diagonal entry has a nonzero coefficient at `e` (no loops);
- no diagonal entry has a nonzero coefficient at an involution (no inversions).

Then `r_B` is the adjacency operator of a 3-regular multigraph `Gamma_B` on
`H x [k]`, and `H` acts freely on vertices and on edges. Each orbit of vertex
types contributes three half-edge orbits, and every edge orbit contains two of
them, so there are `3k/2` edge orbits and `k` is even.

*Subdivision.* For `L >= 2`, the **`L`-subdivision** `A_L` replaces every edge
by a path of `L` edges.
- Choose an oriented representative `(e, p) -> (t, q)` of each edge orbit `E`.
  Introduce types `(E, m)` for `m = 1..L-1`.
- Join `(h, p) - (h, E, 1) - ... - (h, E, L-1) - (ht, q)`. All coefficients are
  `e`, except `t` on the last edge.
- Then `A_L in M_(k')(Z[H])` with `k' = k + (3k/2)(L-1) = k(3L-1)/2`, and it has
  nonnegative coefficients.
- Ports (old vertices) have degree `3` and internal vertices degree `2`, and
  `Gamma_(A_L)` is a subdivision of `Gamma_B`.
- Components correspond, with the same stabilizers.

*Chebyshev polynomials.*
- `U_m(x/2) in Z[x]` is the monic Chebyshev polynomial: `U_0 = 1`, `U_1 = x`,
  `U_(m+1) = x U_m - U_(m-1)`. Also `U_(L-1)(x/2) = prod_(j=1..L-1) (x - lambda_j)`
  with `lambda_j = 2cos(pi j / L)`.
- `p_L(x) := U_L(x/2) - 2 U_(L-2)(x/2) = x U_(L-1)(x/2) - 3 U_(L-2)(x/2)` is
  monic of degree `L` in `Z[x]`. For example `p_2 = x^2 - 3` and
  `p_3 = x^3 - 4x`.
- `p_L(lambda_j) = 3(-1)^j`: with `phi = pi j/L` we have `U_L = (-1)^j` and
  `U_(L-2) = (-1)^(j+1)`.

**Theorem C.** Let `H` be any group and `B in M_k(Z[H])` cubic without
inversions, and `L >= 2`.

1. **Norm.**
   `rho(T_(L-1,L-1,L-1)) <= ||r_(A_L)|| <= 3/sqrt 2 + 3 * 2^(-(L+1)/2)`.
2. **Spectral transfer.**
   `mu_(A_L) = (k/2) sum_(j=1..L-1) delta_(lambda_j) + p_L^* mu_B`, where
   `p_L^* mu_B (f) := integral sum_(lambda : p_L(lambda) = t) f(lambda) d mu_B(t)`,
   with roots counted with multiplicity.
3. **Violation transfer.** For every nonzero `R in Z[t]` and `Q = R o p_L`,

   ```text
   integral_{Q!=0} log|Q| d mu_(A_L)
     = (k/2) sum_(j : R(3(-1)^j) != 0) log|R(3(-1)^j)|  +  L integral_{R!=0} log|R| d mu_B.
   ```

   If `||r_B|| < 3` and `integral_{R!=0} log|R| d mu_B < 0`, then
   `Q_m := ((t^2 - 9) R^m) o p_L` has `integral_{Q_m != 0} log|Q_m| d mu_(A_L) < 0`
   for all large `m`.
4. **Connected examples.** Every group `H` generated by `s_1, ..., s_d` carries
   a cubic operator without inversions `B_H in M_(2d)(Z[H])` whose graph is
   connected. So `A_(H,L)` has stabilizer `H` and
   `||r_(A_(H,L))|| <= 3/sqrt 2 + 3 * 2^(-(L+1)/2)`.

*Proof of (1).*

Lower bound: a port has three distinct incident paths, so their first `L-1`
vertices form `T_(L-1,L-1,L-1)`. Use Lemma 2.3.

Upper bound: apply Lemma 2.1 to `M = r_(A_L)` with `lambda_* = 3/sqrt 2`,
`theta = log sqrt 2` (so `2cosh theta = lambda_*`), and
- `f = 1` on ports;
- `f(m) = cosh(theta(m - L/2)) / cosh(theta L/2)` at the `m`-th internal vertex
  of a path. This is symmetric in `m <-> L-m`, so orientation does not matter,
  and it equals `1` at `m = 0` and `m = L`.

At internal vertices,
`f(m-1) + f(m+1) = 2cosh theta f(m) = lambda_* f(m)`.
At a port, `(Mf) = 3 f(1)` and

```text
f(1) = cosh theta - tanh(theta L/2) sinh theta
     = e^(-theta) + 2 sinh theta / (e^(theta L) + 1)
    <= 2^(-1/2) + 2^(-1/2) 2^(-L/2),
```

using `sinh theta = 2^(-3/2)` and `e^(theta L) = 2^(L/2)`. So
`Mf <= (lambda_* + 3 * 2^(-(L+1)/2)) f` everywhere. QED

Numerically, over finite groups with `L = 2, 3, 4, 6, 8`, the norm is the
largest root of `p_L(x) = 3`: 2.4495, 2.3028, 2.2361, 2.1753, 2.1490. The Schur
bounds are 3.1820, 2.8713, 2.6517, 2.3865, 2.2539.

*Proof of (2).* Fix a nonreal `z`. Order the basis as ports then internal
vertices, and write

```text
r_(A_L) - z = [[ -z , Y ], [ Y^* , X ]],    X = P - z,
```

where `P` is the orthogonal sum of path adjacency matrices on `L-1` vertices,
one per edge. There are no port--port entries and no charges, since `L >= 2`.
`X` is invertible, and

```text
r_(A_L) - z = [[1, Y X^-1],[0, 1]] . [[S, 0],[0, X]] . [[1, 0],[X^-1 Y^*, 1]],
S = -z - Y X^-1 Y^*.
```

**The Schur complement.**
- `r_(A_L) - z` and `X` are invertible, so `S` is invertible.
- The triangular factors are `exp` of a nilpotent off-diagonal block, so they
  have FK determinant `1`. By (FK),
  `log det(r_(A_L) - z) = log det S + log det X`.
- On a path of `L-1` vertices, `det(z - P_(L-1)) = U_(L-1)(z/2)`. The resolvent
  entries at the ends are `G_11 = G_(L-1,L-1) = -U_(L-2)(z/2)/U_(L-1)(z/2)` and
  `G_(1,L-1) = -1/U_(L-1)(z/2)`.
- Each port lies on three paths, and each path joins its two ports. Hence
  `Y X^-1 Y^* = -(3U_(L-2)(z/2) + r_B) / U_(L-1)(z/2)`. With
  `z U_(L-1) = U_L + U_(L-2)` this gives

  ```text
  S = (r_B - p_L(z)) / U_(L-1)(z/2).
  ```

**The identity.** `X` is an orthogonal sum of `3k/2` orbit-types of finite
blocks. `S` is `r_B - p_L(z)` times a nonzero scalar on `M_k(N(H))`. The
operator `r_B - p_L(z) = U_(L-1)(z/2) S` is normal and invertible. So

```text
integral log|x - z| d mu_(A_L)(x)
  = (3k/2) log|U_(L-1)(z/2)| - k log|U_(L-1)(z/2)| + integral log|t - p_L(z)| d mu_B(t)
  = (k/2) sum_j log|z - lambda_j| + integral log|t - p_L(z)| d mu_B(t).
```

**The Laplacian.** Both sides are locally integrable in `z in C` and agree off
`R`, so they agree as distributions. Apply `(1/2pi) Delta_z`.
- The left side gives `mu_(A_L)`.
- The first term on the right gives `(k/2) sum_j delta_(lambda_j)`.
- `(1/2pi) Delta_z log|p_L(z) - t|` is the sum of the Dirac masses at the roots
  of `p_L - t`, counted with multiplicity.
- Fubini against a test function is justified, because `log|p_L(z) - t|` is
  locally integrable in `z` uniformly for `t` in the compact support of
  `mu_B`.

This gives (2).

**Check.** The total masses agree: `k(3L-1)/2 = (k/2)(L-1) + Lk`. The spectrum
identity was also checked numerically for five finite groups and
`L in {2,3,4,6,8}`, with maximal error `4e-8` (`output.txt`). QED

*Proof of (3).*

**Borel test functions.** Identity (2) is an identity of finite positive Radon
measures, tested on continuous functions. By monotone class it holds for every
nonnegative Borel `f`. Hence it also holds, with values in `[-inf, inf)`, for
every Borel `f` that is bounded above on compact sets. We apply it to
`f = 1_{Q != 0} log|Q|`.

**The identity.**
- At a Dirichlet atom, `Q(lambda_j) = R(p_L(lambda_j)) = R(3(-1)^j)`.
- If `p_L(lambda) = t`, then `Q(lambda) = R(t)`. There are `L` such roots,
  counted with multiplicity, and either all of them satisfy `Q != 0` or none do.
  So the inner sum in `p_L^* mu_B` is `L 1_{R != 0}(t) log|R(t)|`.

This gives the displayed formula.

**The violation.** Put `R_m = (t^2 - 9) R^m`, which is nonzero.
- `R_m(3(-1)^j) = 0` for every `j`, so the Dirichlet term is empty.
- Since `||r_B|| < 3`, `supp mu_B <= [-||r_B||, ||r_B||]`. On this set
  `9 - ||r_B||^2 <= |t^2 - 9| <= 9`, and `R_m(t) != 0` iff `R(t) != 0`.
- Therefore

  ```text
  integral_{Q_m != 0} log|Q_m| d mu_(A_L)
    = L integral_{R != 0} log|t^2 - 9| d mu_B + m L integral_{R != 0} log|R| d mu_B.
  ```

The first term is a finite constant. In absolute value it is at most
`L k max(log 9, -log(9 - ||r_B||^2))`, since `mu_B` has mass `k`. The second
term tends to `-inf` as `m -> inf`, or equals `-inf` already. QED

**Remark (partial converse).** Suppose `A_L` violates Serre with `Q`, and
`mu_B` has no atom on the finite set `p_L(Z(Q))`, where `Z(Q)` is the complex
zero set of `Q`. Then `B` violates Serre.
- *The Dirichlet term is nonnegative.* The `lambda_j` are the distinct roots of
  `U_(L-1)(x/2) in Z[x]`. The subset where `Q != 0` is Galois-stable, so the
  product of those `Q(lambda_j)` is a nonzero rational algebraic integer, hence
  of absolute value at least `1`.
- *The port term is a polynomial.* Put
  `N_Q(t) := Res_lambda(p_L(lambda) - t, Q(lambda))`. It lies in `Z[t]`, and
  since `p_L - t` is monic it equals `prod_(p_L(lambda) = t) Q(lambda)`.
- `N_Q(t) = 0` exactly on `p_L(Z(Q))`, so `N_Q != 0`, and off that set every
  root has `Q(lambda) != 0`. Hence the port term equals
  `integral_{N_Q != 0} log|N_Q| d mu_B`.
- So `integral_{N_Q != 0} log|N_Q| d mu_B < 0`.

Without the no-atom hypothesis the transfer back is not clear; see Section 6.

*Proof of (4).* Let `s_1, ..., s_d` generate `H`, with `d >= 1`, and use types
`P_0, ..., P_(2d-1)`. For every `h in H`, put the edges:
- **hub:** `(h, P_a) - (h, P_(a+1 mod 2d))` for `a = 0..2d-1`. For `d = 1` this
  is a double edge `(h, P_0) = (h, P_1)`.
- **external:** `(h, P_(2i-2)) - (h s_i, P_(2i-1))` for `i = 1..d`.

This multigraph is invariant under left translation by `H`.

**Degrees and entries.**
- Every vertex has two hub edges and one external edge, so degree `3`.
- In matrix form, `B_H` has entry `e` between cyclically adjacent types. For
  `d = 1` the two hub edges together give `2e`. It also has the coefficient
  `s_i` (or `s_i^-1`, by convention) added between `P_(2i-2)` and `P_(2i-1)`.
- All diagonal entries vanish, so there are no loops and no inversions.
  Coefficients are nonnegative integers and every row sums to `3`.

**Connected.** The hub cycle joins all types over `h`. The path
`(h, P_(2i-2)) - (h s_i, P_(2i-1))`, followed by the hub cycle over `h s_i`,
joins `(h, P_0)` to `(h s_i, P_0)`. Since the `s_i` generate `H`, the graph is
connected. Its stabilizer is `H`, acting simply transitively on each type.

The norm bound is (1). QED

This construction was checked numerically for `Z/7`, `Z/12`, `S_3`, `D_5` and
`Z/9` (with `s_3 = e`): connectivity, degrees, norm bounds, the Schur vector
inequality, and the spectrum identity.

**Corollary C.1 (sharpness of Theorem A).** For every finitely generated group
`H` and every `eps > 0`, there is a nonnegative self-adjoint integral matrix
over `H` with `||r_A|| < 3/sqrt 2 + eps` and connected graph with stabilizer
`H`. So Theorem A's structural conclusion fails immediately above `3/sqrt 2`.
Take `H = F_2` for exponential growth and nonamenable stabilizers.

**Corollary C.2 (violations transfer to the tripod threshold).** Let `H` be
finitely generated. Suppose some cubic operator without inversions
`B in M_k(Z[H])` with `||r_B|| < 3` violates a Serre inequality. Then for every
`eps > 0` some nonnegative self-adjoint `A in M_(k')(Z[H])` with
`||r_A|| < 3/sqrt 2 + eps` violates one, so `H` violates the determinant
conjecture. Equivalently, suppose Serre holds over `H` for nonnegative matrices
of norm `< 3/sqrt 2 + eps`, for some `eps > 0`. Then it holds for all cubic
operators without inversions of norm `< 3`. (Take `L` with
`3 * 2^(-(L+1)/2) < eps` and use (1) and (3).)

**Remark (when `||r_B|| < 3`).** For `B_H` of (4) with `H` nonamenable:
- `Gamma_(B_H)` is a connected 3-regular graph with a free cocompact
  `H`-action.
- It is quasi-isometric to a Cayley graph of `H` by (SM), so it has positive
  edge-Cheeger constant `h`. That positivity is a quasi-isometry invariant for
  bounded-degree graphs, a standard fact not reproved here.
- Mohar's bound (`fpbs-mohar-adjacency-norm-cheeger-bound`) gives
  `||r_(B_H)|| <= sqrt(9 - h^2) < 3`.

For amenable `H` the determinant conjecture holds anyway (amenable groups are
sofic). Theorem C does **not** say that cubic operators capture the whole
determinant conjecture. Whether every Serre violation over `H` can be moved to
a cubic operator without inversions over `H` is open; see Section 6.

## 6. What remains open

**6.1 The signed room `(2.019, 3/sqrt 2)`.** Does every self-adjoint
`A in M_n(Z[G])` with `||r_A|| < 3/sqrt 2` obey every Serre inequality, over
every group?
- Theorem B settles this below `2.019`, and Theorem A settles it when
  `||r_|A||| < 3/sqrt 2`.
- Section 5 shows `3/sqrt 2` is the right threshold for unsigned matrices.
- For signed matrices, cancellation lets `|A|` have large norm. The
  McKee--Smyth list becomes infinite beyond `2.0198...`, and signed graphs with
  radius in `(2, sqrt(2 + sqrt 5))` are not classified (McKee--Smyth,
  introduction).

**Lemma 6.1 (local structure in the signed room).** Let `M` be the matrix of
`r_A` with `||r_A|| < 3/sqrt 2`, and let `v` be a vertex.
1. `sum_w M_(vw)^2 <= 4`. Hence either row `v` has a single nonzero entry
   `+-2`, or all its entries lie in `{0, +-1}` and `deg(v) + M_(vv)^2 <= 4`. In
   particular `Delta <= 4`.
2. If `sum_w M_(vw)^2 = 4`, then `M^2 delta_v = 4 delta_v + eps delta_w` with
   `eps in {0, +-1}` and a single `w != v`.
3. If `M^2 delta_v = 4 delta_v`, the spectral measure of `r_A` at `delta_v` is
   supported on `{+-2}`.
4. An induced subgraph that is a tree with zero diagonal has spectral radius at
   most `||r_A||`. Therefore induced `T_(k,k,k)` with zero charges are excluded
   once `R_k > ||r_A||`.

*Proof.*
1. `||M delta_v||^2 <= ||r_A||^2 < 4.5`, and the left side is an integer.
2. `||M^2 delta_v||^2 <= ||r_A||^2 ||M delta_v||^2 < 18`, and
   `(M^2)_(vv) = ||M delta_v||^2 = 4`. So
   `sum_(w != v) (M^2)_(wv)^2 <= 1`, and the entries are integers.
3. `delta_v` is an eigenvector of `r_A^2` for the eigenvalue `4`.
4. Switching signs by a diagonal `+-1` gauge turns a signed tree into the
   unsigned tree. Then use (Comp). QED

**Example (local test is not enough).** Take the Cayley graph of
`Z/4 * Z/2 = <a, b | a^4, b^2>` with generators `a^(+-1), b`. Put sign `-1` on
the edge `x a^3 -> x a^4` of every `a`-coset, so every square is negative.
- Every vertex is cubic. The two 2-paths around its square cancel, and
  `sum_(w != v) (M^2)_(wv)^2 = 4`, so Lemma 6.1 is satisfied.
- The principal submatrix on the word ball of radius `3` (17 vertices) already
  has spectral radius `2.236068 > 3/sqrt 2`.
- The radius-12 ball (1593 vertices) gives `2.397131`, approaching `1 + sqrt 2`
  (`experiments/determinant-norm-room-2026-09-16/signed_square_tree.py`).

By compression these are lower bounds for the norm, up to floating-point error,
and the margin at radius 3 is `0.11`. So this exponential-growth signed graph
is not a candidate for the signed room.
Lemma 6.1 says that in the signed room 4-valent vertices are almost pure, and
that long induced tripods are excluded. It does not decide whether growth can
be exponential. Graphs built from signed 4-regular strips ("tubes") joined at
junctions of lower degree are the natural test family, but no norm computation
for them was done here.

**6.2 The borderline `||r_|A||| = 3/sqrt 2`.** Theorem A needs strict
inequality, and Theorem C gives only `3/sqrt 2 + eps`.
- Is there a nonnegative self-adjoint integral matrix of norm exactly
  `3/sqrt 2` whose graph has a nonamenable stabilizer?
- The Schur vector of Theorem C(1) has port defect `3 * 2^(-(L+1)/2)`, so
  finite `L` never reaches `3/sqrt 2`.

**6.3 Converse transfer with atoms.** In the Remark after Theorem C(3), atoms of
`mu_B` on `p_L(Z(Q))` block the passage from a violation for `A_L` back to one
for `B`. Such atoms are algebraic integers, and their masses carry Galois
information. Controlling them should use
`integral-eigenvalues-galois-balanced-for-sofic-groups`-type input, which is
not available over nonsofic `H`.

**6.4 Do cubic operators capture the conjecture?** Can every Serre violation
over `H` be moved to a cubic operator without inversions over `H` (or over a
group that fails the conjecture exactly when `H` does)? If so, Corollary C.2
gives: `H` satisfies the determinant conjecture iff, for some (equivalently
every) `eps > 0`, nonnegative matrices over `H` of norm `< 3/sqrt 2 + eps` obey
Serre. The known reductions in the graph (support localization, Serre-class
reformulation) keep signed coefficients and do not produce regular graphs.

**6.5 Test operators over nonsofic groups.** For the finitely presented
nonsofic group of `explicit-eighteen-relator-nonsofic-group` (four
generators), Theorem C(4) gives explicit `B_H in M_8(Z[H])` and
`A_(H,L) in M_(4(3L-1))(Z[H])`. `H` is nonsofic, hence nonamenable and not
virtually cyclic.
- By Theorem A, every nonnegative operator over `H` with a component of
  stabilizer `H` has norm at least `3/sqrt 2`.
- The norms of `A_(H,L)` tend to that value.
- By the Remark after Corollary C.2, `||r_(B_H)|| < 3`, so Corollary C.2
  applies to `B_H`.

No method is known to decide Serre for these operators.

**6.6 Random-graph version of Theorem A.** The growth argument is
deterministic. For a unimodular random rooted integer-weighted network whose
support is tripod-free, is the expected root measure Serre? This would feed
`determinant-via-unimodular-integral-networks` only in the tripod-free regime,
where Theorem A already works over groups.
