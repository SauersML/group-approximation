# L²-acyclicity of Leavitt unit groups, 2026-09-12

Lane `ex-lueck-approximation` (EX swarm). This record proves that every L²-Betti number of
the binary Leavitt unit group `R^x`, `R = L_(F_2)(1,2)`, vanishes. The same holds for every
unit group `(B ⊗ R)^x` with `B` a simple unital `F_2`-algebra, in particular for the finitely
presented simple group `(R ⊗ R)^x`.

The proof runs Khanh's stabilizer spectral sequence for ordered frame complexes with
coefficients in the group von Neumann algebra. Every simplex stabilizer below the top
dimension contains an infinite normal abelian subgroup, so all its L²-Betti numbers vanish,
and the whole `E^1` page in low total degree has von Neumann dimension zero. Leavitt
self-similarity `GL_r(R) ≅ R^x` then pushes the acyclic range to every degree.

Status: proved on paper here, unreviewed. The external inputs are listed in Section 1.

## 0. Statements

Write `β_n^(2)(G) = dim_(N(G)) H_n(G; N(G))` for Lück's L²-Betti numbers of an arbitrary
countable group `G`.

**Theorem A (frame criterion).** Let `A` be an infinite unital ring and `r >= 3`. Let
`X_r(A)` be the ordered frame semisimplicial set of Khanh's Definition 2.1. If
`H̃_d(X_r(A); Z) = 0` for `0 <= d <= r-3`, then `β_n^(2)(GL_r(A)) = 0` for `0 <= n <= r-3`.

**Corollary B.** For `R = L_(F_2)(1,2)`, `β_n^(2)(R^x) = 0` for every `n >= 0`.

**Corollary C.** Let `B` be a simple unital `F_2`-algebra and `S = B ⊗_(F_2) R`. Then
`β_n^(2)(S^x) = 0` for every `n >= 0`. This covers `(R ⊗ R)^x`, which is finitely presented,
simple, integrally acyclic and nonsofic.

**Theorem D (general form of the count).** Let a group `G` act on a semisimplicial set `X`
so that every stabilizer fixes its simplex pointwise, and suppose `H̃_d(X; Z) = 0` for
`0 <= d <= m`. If `β_t^(2)(G_σ) = 0` for every `p`-simplex `σ` and every `t` with
`p + t <= m`, then `β_n^(2)(G) = 0` for `0 <= n <= m`.

Theorem A is Theorem D with `G = GL_r(A)`, `X = X_r(A)`, `m = r-3`, once the stabilizers are
identified (Lemma 2.1).

## 1. Inputs

- **(K) Khanh, arXiv:2609.08428v1** (text on MSI, `lit-groups/khanh-clean.txt`).
  - Definition 2.1: "The ordered frame semisimplicial set X_r(A) has as its p-simplices the
    tuples (v_1,...,v_k), where k = p + 1 <= r, admitting a decomposition
    A^r = v_1 A ⊕ ··· ⊕ v_k A ⊕ C, with C ≅ A^(r−k). Each map A → v_i A, a ↦ v_i a, must
    be an isomorphism. [...] Faces delete vectors, and there are no simplices in dimensions
    p >= r."
  - Proof of Theorem 2.2: "The group Γ_r acts transitively on the ordered (k−1)-simplices of
    X_r(A). [...] The stabilizer of the standard k-frame is J_(k,r−k)(A), and the stabilizer
    of a full frame is trivial. [...] Since the frames are ordered, the stabilizers fix their
    simplices pointwise."
  - Corollary 4.3: "For r >= 3, one has H̃_d(X_r(R), Z) = 0 for 0 <= d <= r−3."
    Its proof cones a finite cycle from a common extension vector (Proposition 4.2, from
    Lemma 4.1, Leavitt word reduction).
  - Over `S = B ⊗ R` with `B` simple, the same connectivity is Corollary 2.5 of
    `research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md`, verified PASS in
    `research/artifacts/review-boone-higman-leavitt-tensor-hosts-2026-09-12.md` (Section 1).
    It uses no K-theory hypothesis.
- **(L) Lück's dimension theory** (W. Lück, *L²-Invariants: Theory and Applications to
  Geometry and K-Theory*, Springer 2002). Numbers verified in Section 6.
  - (L1) `dim_(N(G))` is defined on all `N(G)`-modules and is additive on short exact
    sequences and on countable direct sums.
  - (L2) Induction: for `H <= G`, `N(G)` is flat over `N(H)` and
    `dim_(N(G))(N(G) ⊗_(N(H)) M) = dim_(N(H)) M`.
  - (L3) Cheeger–Gromov: if `G` contains an infinite normal amenable subgroup, then
    `β_n^(2)(G) = 0` for every `n >= 0`.
- **(P) Prefix codes.** A complete prefix code with `r` leaves `w_1, ..., w_r` gives a ring
  isomorphism `R -> M_r(R)`, `a ↦ (t_(w_i) a s_(w_j))_(i,j)`, with inverse
  `(a_ij) ↦ Σ s_(w_i) a_ij t_(w_j)`. Here `s_w, t_w` are the words in `s_0, s_1` and in
  `t_0, t_1` with `t_w s_w = 1`, `t_u s_w = 0` for incomparable `u, w`, and
  `Σ_i s_(w_i) t_(w_i) = 1`. So `GL_r(R) ≅ R^x` for every `r >= 1`. The same map with
  coefficients in `B` gives `GL_r(S) ≅ S^x`. (This is the identification used throughout
  `leavitt-gl-equals-el-and-perfect-unit-group`.)

## 2. Stabilizers

Matrices act on columns from the left and `A^r` is a right `A`-module, as in (K).

**Lemma 2.1.** Let `1 <= k <= r-1`. The stabilizer in `GL_r(A)` of the standard `k`-frame
`(e_1, ..., e_k)` is

```text
J = { [[I_k, b], [0, d]] : b in M_(k x (r-k))(A), d in GL_(r-k)(A) }.
```

It contains `U = { [[I_k, b], [0, I_(r-k)]] }` as a normal subgroup, `U ≅ (M_(k x (r-k))(A), +)`
is abelian, and `U` is infinite when `A` is infinite. Hence `β_t^(2)(J) = 0` for all `t >= 0`,
and the same holds for every conjugate of `J`.

*Proof.* `g e_i = e_i` for `i <= k` says the first `k` columns of `g` are `e_1, ..., e_k`, so
`g = [[I_k, b], [0, d]]`. Its inverse also fixes the `e_i`, so it has the same shape
`[[I_k, b'], [0, d']]`, and multiplying out gives `d d' = d' d = I`. Conversely every such
matrix is invertible and fixes the `e_i`. The map `J -> GL_(r-k)(A)`, `g ↦ d`, is a
homomorphism with kernel `U`, and `[[I, b],[0, I]] [[I, b'],[0, I]] = [[I, b + b'],[0, I]]`.
The group `U` is abelian, so amenable, and infinite with `A`. Apply (L3). ∎

**Lemma 2.2.** Every `(k-1)`-simplex of `X_r(A)` with `k <= r-1` has stabilizer conjugate to
`J`, and the stabilizer fixes the simplex pointwise.

*Proof.* Let `A^r = v_1 A ⊕ ··· ⊕ v_k A ⊕ C` with `C ≅ A^(r-k)`. Sending `e_i ↦ v_i` for
`i <= k`, and `e_(k+1), ..., e_r` to the images of the standard basis under an isomorphism
`A^(r-k) -> C`, is an automorphism of the right module `A^r`, that is, a matrix
`g in GL_r(A)` with `g e_i = v_i`. The stabilizer of `(v_1, ..., v_k)` is `g J g^(-1)`. The
action is on ordered tuples, so a group element fixing the simplex fixes each vector. ∎

## 3. The stabilizer spectral sequence with coefficients

**Proposition 3.1.** Let `G` act on a semisimplicial set `X` with stabilizers fixing
simplices pointwise, and let `M` be a right `ZG`-module that is flat as an abelian group.
Suppose `H̃_d(X; Z) = 0` for `0 <= d <= m`. There is a spectral sequence

```text
E^1_(p,t) = ⊕_([σ] in G\X_p) H_t(G_σ; M)   ==>   H_(p+t)(G; M)   in total degrees <= m.
```

*Proof.* Let `P_* -> Z` be a projective resolution by left `ZG`-modules and `C_*(X)` the
semisimplicial chain complex, `∂ = Σ (-1)^i d_i`, a complex of permutation modules (no signs
enter the action, by pointwise fixing). Form the double complex
`D_(t,p) = M ⊗_(ZG) (P_t ⊗_Z C_p(X))`, with `G` acting diagonally on `P_t ⊗ C_p(X)`.

*Filtration by `p`.* `C_p(X)` is free abelian, so `P_* ⊗ C_p(X)` is exact, and each
`P_t ⊗ N` with diagonal action is projective (for `P_t = ZG`, `g ⊗ n ↦ g ⊗ g^(-1) n`
identifies it with `ZG ⊗ N` acted on through the left factor). So column homology is
`Tor_t^(ZG)(M, C_p(X)) = ⊕_[σ] Tor_t^(ZG)(M, Z[G/G_σ]) = ⊕_[σ] H_t(G_σ; M)` by Shapiro's
lemma. This is `E^1_(p,t)`, converging to `H_*(Tot D)`.

*Filtration by `t`.* The same identification, natural in `N`, gives
`M ⊗_(ZG) (P_t ⊗ C_*(X)) ≅ (M ⊗_(ZG) P_t) ⊗_Z C_*(X)` for free `P_t`, and by naturality for
summands of free modules. `M ⊗_(ZG) P_t` is a summand of a direct sum of copies of `M`, so it
is flat over `Z`, and the homology in `p` is `(M ⊗_(ZG) P_t) ⊗ H_p(X)`. It vanishes for
`1 <= p <= m`, and in row `p = 0` it is `M ⊗_(ZG) P_t`, whose homology in `t` is `H_t(G; M)`.
In total degree `n <= m` the only nonzero `E^2` term is `E^2_(n,0) = H_n(G; M)`. A
differential `d^k` out of it lands in row `k-1` in total degree `n-1 < m`, which is zero, and
no differential enters row `0`. So `H_n(Tot D) ≅ H_n(G; M)` for `n <= m`. ∎

This is the construction Khanh uses at (2.6), there with `M = Z` (his citation: Weibel,
§6.1.15), with the coefficient module carried along.

## 4. Proof of Theorem D, hence Theorem A

Take `M = N(G)` with right `ZG`-action through `g ↦ λ(g)`. It is a complex vector space, hence
flat over `Z`, and the left `N(G)`-action commutes with everything in Proposition 3.1, so
every page is a sequence of `N(G)`-modules with `N(G)`-linear differentials.

For a subgroup `H = G_σ`, flatness of `N(G)` over `N(H)` (L2) gives

```text
H_t(H; N(G)) = Tor_t^(ZH)(N(G) ⊗_(N(H)) N(H), Z) ≅ N(G) ⊗_(N(H)) H_t(H; N(H)),
```

so `dim_(N(G)) H_t(H; N(G)) = β_t^(2)(H)` by (L2). By hypothesis every `E^1_(p,t)` with
`p + t <= m` is a countable direct sum of modules of dimension zero, so it has dimension zero
(L1). Every later page term is a subquotient of an `E^1` term, so `E^∞_(p,t)` has dimension
zero for `p + t <= m` (L1). For `n <= m`, `H_n(G; N(G))` has a finite filtration whose graded
pieces are the `E^∞_(p, n-p)`, `0 <= p <= n`, so its dimension is zero (L1). ∎ (Theorem D)

For Theorem A take `G = GL_r(A)`, `X = X_r(A)`, `m = r-3`. A `p`-simplex with `p <= r-3` has
`k = p+1 <= r-2` vectors, so its stabilizer is conjugate to `J` with `r-k >= 2`
(Lemma 2.2), and all its L²-Betti numbers vanish (Lemma 2.1). ∎ (Theorem A)

## 5. Corollaries

*Corollary B.* `R` is infinite (distinct positive words are linearly independent, Khanh
(4.1)). For `n >= 0` put `r = n + 3`. (K) Corollary 4.3 is the hypothesis of Theorem A, so
`β_n^(2)(GL_r(R)) = 0`, and (P) gives `GL_r(R) ≅ R^x`. L²-Betti numbers are invariants of the
abstract group. ∎

*Corollary C.* `S = B ⊗ R` contains `1 ⊗ R`, so it is infinite; connectivity is Corollary 2.5
of the tensor-host artifact; (P) with coefficients in `B` gives `GL_r(S) ≅ S^x`. For
`B = R`: `(R ⊗ R)^x` is finitely presented, simple and integrally acyclic
(`leavitt-square-unit-group-is-fp-simple-and-acyclic`), and `a ↦ 1 ⊗ a` embeds `R^x` in it,
so it is nonsofic by `openai-leavitt-unit-nonsofic`. ∎

## 6. Citation record (read from PDF text on MSI, 2026-09-12)

W. Lück, *L²-Invariants from the Algebraic Point of View*, arXiv:math/0310489 (text extracted
with ghostscript, `/scratch.global/sauer354/ex/ex-lueck-approximation/lit/math_0310489.txt`).

- (L1) **Theorem 1.11 (iii)**: "There exists precisely one dimension function
  dim_N(G): {N(G)-modules} → [0,∞] which satisfies: (a) Extension Property [...]
  (b) Additivity: If 0 → M0 → M1 → M2 → 0 is an exact sequence of N(G)-modules, then
  dim(M1) = dim(M0) + dim(M2) [...] (c) Cofinality: Let {Mi | i ∈ I} be a cofinal system of
  submodules of M [...] Then dim(M) = sup{dim(Mi) | i ∈ I}". A countable direct sum is the
  cofinal union of its finite partial sums, so (b) and (c) give dimension zero for a countable
  sum of dimension-zero modules, and for sub- and quotient modules of dimension-zero modules.
- (L2) **Theorem 1.18 (Induction and dimension)**: "Let i: H → G be an injective group
  homomorphism. Then (i) Induction with N(i): N(H) → N(G) is a faithfully flat functor
  M ↦ i∗M := N(G) ⊗_N(i) M [...] (ii) For any N(H)-module M we have:
  dim_N(H)(M) = dim_N(G)(i∗M)."
- (L3) **Theorem 6.4**, with `B_d := {G | b_p^(2)(G) = 0 for 0 ≤ p ≤ d}` (6.3), `d` a
  non-negative integer or `∞`: "(i) The class B∞ contains all infinite amenable groups;
  (ii) If G contains a normal subgroup H with H ∈ Bd, then G ∈ Bd". The survey proves (ii) by
  its Theorem 3.11 (ii) applied to the fibration `BH → BG → B(G/H)`. Originally Cheeger–Gromov
  (Topology 25, 1986).

The survey's definition of the L²-Betti numbers of a group is `b_p^(2)(G) = b_p^(2)(EG; N(G))`,
the von Neumann dimension of `H_p(N(G) ⊗_ZG C_*(EG))`. Since `C_*(EG)` is a free resolution
of `Z`, this is `dim_N(G) Tor_p^ZG(N(G), Z)`, the quantity used in Sections 3 and 4.

## 7. Calibration, scope and credit

**Model tests of Theorem A's hypotheses.**
- *Infinitude binds.* `A = F_2`: every `GL_r(F_2)` is finite, so `β_0^(2) = 1/|GL_r(F_2)| != 0`.
  The conclusion fails, and the proof breaks exactly at Lemma 2.1: `U` is finite and (L3) does
  not apply.
- *The range `n <= r-3` is where connectivity enters.* `A = Z`, `r = 2`: `β_1^(2)(SL_2(Z)) =
  1/12 != 0`, and the theorem asserts nothing (`r-3 < 0`).
- *Consistency.* For `A = Z`, `r >= 3`, the conclusion agrees with the known L²-acyclicity of
  lattices in `SL_r(R)`, `r >= 3`. For a field `A = Q`, `GL_r(Q)` has infinite central `Q^x`,
  so (L3) already gives all of it.
- *A real object satisfies the hypotheses.* `R = L_(F_2)(1,2)` at every `r >= 3` (Khanh
  Corollary 4.3), and `B ⊗ R` for simple `B` (tensor-host Corollary 2.5).

**What is new and what is not.**
- The ordered frame complex, its connectivity, the transitivity statement and the stabilizer
  spectral sequence are Khanh's. With integral coefficients his proof needs the scalar weight
  argument, because the elementary abelian `U` has large integral homology. With coefficients
  in `N(G)` the stabilizer terms die at `E^1`, and no weight argument and no K-theory input are
  needed.
- The rank-change step `GL_r(R) ≅ R^x` is what turns a vanishing range growing with `r` into
  vanishing in every degree. Over a ring without `M_r(A) ≅ A` for infinitely many `r`,
  Theorem A only gives a low-degree range.
- Novelty check, bounded: arXiv metadata search on 2026-09-12 for "Leavitt Betti" and
  `"Leavitt algebra" l2` returned no results. Khanh's paper does not mention L²-invariants
  (text grep). The analogous result for Thompson's `V` is known and stronger: Sauer–Thumann,
  arXiv:1304.6843, Theorem 1.1, prove that local similarity groups such as `V` are
  l²-invisible (non-reduced homology with `N(Γ)` coefficients vanishes). Our statement is the
  reduced (dimension) form for the unit group, which contains `V` and is not a local
  similarity group.

**What it does not give.**
- Not l²-invisibility of `R^x`. That would need non-reduced vanishing, and `R^x` is not known
  to be of type `F_∞`.
- Nothing about Atiyah-type rationality of kernels of arbitrary matrices over `Q[R^x]`: those
  are not boundary maps of a resolution. See the lane's Atiyah node.
- Nothing about positive characteristic. For the augmentation rank on `F_2[R^x]` the analogous
  Betti numbers are `dim H_n(R^x; F_2)`, which vanish by Khanh's integral acyclicity, not by
  this argument: an infinite elementary abelian `U` has huge mod-2 homology, so the stabilizer
  terms do not die over `F_2`.

**Consequences recorded without new proof.**
- `β_1^(2)(R^x) = 0` was already implied by property (T)
  (`binary-leavitt-unit-group-has-tt-mod-t`). Degrees `n >= 2` are new here.
- `R^x` is an infinite finitely presented simple group that is integrally acyclic,
  L²-acyclic, Kazhdan and nonsofic.
