---
rg: 2
id: c-linear-sofic-iff-bounded-dimension-large-characteristic-proof
kind: route
title: Spread model varieties over Spec Z, lift coprime modules through Witt vectors with averaging idempotents, and restrict the von Neumann rank
target: c-linear-sofic-iff-bounded-dimension-large-characteristic
requires: [root-splits-into-large-and-fixed-characteristic-witnesses]
---

Lemma 3 of `root-splits-into-large-and-fixed-characteristic-witnesses-proof`, over an arbitrary field `F`, says: `G`
is `F`-linear sofic iff every window has a model over `F` with separation `1/4`. Its proof uses only the amplifier,
which works over any field.

## 1. Dimension gate

1. **The model set.** Fix a window `(W, eps)` and a dimension `n`. Let `X` be the subset of affine space
   `A^(|W| n^2)_Z` of tuples `(phi(g))_(g in W)` of `n x n` matrices satisfying:
   - `det phi(g) != 0`;
   - all minors of size `floor(eps n) + 1` of `phi(g)phi(h) - phi(gh)` vanish, for `g, h, gh` in `W`;
   - some minor of size `ceil(n/4)` of `phi(g) - 1` is nonzero, for `g` in `W \ {1}`.

   `X` is a finite Boolean combination of zero sets of integer polynomials, so it is a constructible set defined over
   `Z`. For an algebraically closed field `k`, `X(k)` is the set of `n`-dimensional models over `k`. A model over
   `F_l-bar` has entries in some finite subfield. So `X(F_l-bar)` is nonempty iff `m_(W,eps)(l) <= n`.
2. **Spreading out.**
   - Write `X` as a finite union of locally closed subschemes of finite type over `Z`, and let
     `pi : X -> Spec Z`.
   - By Chevalley's theorem, `pi(X)` is constructible. A constructible subset of `Spec Z` either contains the
     generic point, and then contains a nonempty open set, so all but finitely many primes; or it is a finite set of
     closed points.
   - The generic point lies in `pi(X)` iff `X(Q-bar)` is nonempty, iff `X(C)` is nonempty (Nullstellensatz).
   - A prime `l` lies in `pi(X)` iff `X(F_l-bar)` is nonempty.
3. **(i) implies (iii).**
   - By Lemma 3 over `C`, each window has a complex model of some dimension `n`.
   - So the generic point is in `pi(X_(W,eps,n))`. Hence `m_(W,eps)(l) <= n` for all large `l`.
4. **(iii) implies (ii)** is trivial.
5. **(ii) implies (i).**
   - `pi(X_(W,eps,n))` contains infinitely many closed points, so it contains the generic point.
   - So `X(C)` is nonempty and every window has a complex model. By Lemma 3 over `C`, `G` is `C`-linear sofic.
6. **Consequences.**
   - (iii) supplies models in every large characteristic, so `G` is in `L_inf` by Lemma 3(ii).
   - If `G` is not `C`-linear sofic, (ii) fails for some window. Then for every `n` only finitely many `l` have
     `m(l) <= n`, which means `m(l) -> infinity`. ∎

## 2. Tame lifting

1. **The lift.**
   - Let `O = W(F_q)` be the Witt vectors: a complete discrete valuation ring with residue field `F_q` and fraction
     field `K` of characteristic zero. Put `V = F_q^n` as an `F_q[Q]`-module.
   - Since `p` does not divide `|Q|`, `V` is projective (Maschke). Write it as the image of an idempotent `e` in
     `M_N(F_q[Q])`.
   - `O[Q]` is `pi`-adically complete, so `e` lifts to an idempotent `E` in `M_N(O[Q])`.
   - `L = E O[Q]^N` is a projective `O[Q]`-module with `L / pi L ≅ V`. It is `O`-free of rank `n`.
   - `K` has characteristic zero and cardinality at most the continuum, so it embeds in `C`. Put
     `psi : Q -> GL(L (x)_O C) = GL_n(C)`.
2. **Ranks are preserved.**
   - Fix `x` in `Q` of order `m`, with `p` not dividing `m`, and put `e_x = (1/m) sum_(j<m) x^j` in `O[Q]`. This is
     an idempotent.
   - On any module `M` over a ring where `m` is invertible, `M = e_x M (+) (1 - e_x)M`.
     - `x` is the identity on `e_x M`.
     - `x - 1` is injective on `(1 - e_x)M`: a fixed vector `v` there satisfies `v = e_x v = e_x (1 - e_x) v = 0`.
     - Hence `rank(x - 1) = dim (1 - e_x)M` for finite-dimensional `M`.
   - `(1 - e_x)L` is a direct summand of `L`, `O`-free of some rank `r`. Its reduction is `(1 - e_x)V` and its
     complexification is `(1 - e_x)(L (x) C)`, so both have dimension `r`.
   - So `rank(x - 1)` is the same over `F_q` and over `C`.
3. **Consequences.**
   - Defects are ranks `rank(x - y) = rank(y^(-1)x - 1)` with `x, y` in `Q`, and separations are `rank(x - 1)`. Both
     are transported exactly by `psi`.
   - If `G` is not `C`-linear sofic, some window has no complex model by Lemma 3 over `C`. So every finite-field model
     of that window is wild.
   - Conversely, tame models for every window give complex models for every window. ∎

## 3. Sylvester obstruction

1. **Rank function from models.**
   - Let `phi_j` be `(W_j, 1/j)`-models of `H` over `F_(l_j)` with `l_j -> infinity`. Then
     `R = prod_omega M_(n_j)(F_(l_j))`, modulo the ideal of rank-zero sequences, is a regular ring with a rank
     function over `K = prod_omega F_(l_j)`, a field of characteristic `0` and cardinality at most `2^aleph_0`.
   - `phi` induces a unital homomorphism `K[H] -> R`. Pulling back the rank gives a Sylvester matrix rank function
     with `rk(g - 1) >= 1/4` for `g != 1`.
2. **Every group already has one.**
   - Embed `K` in `C` and `C[H]` in the algebra `U(H)` of operators affiliated to the group von Neumann algebra. The
     von Neumann rank `rk(a)`, the trace of the range projection, is a Sylvester matrix rank function on `U(H)`, and
     restriction along unital ring maps preserves this.
   - For `g != 1`, the kernel of `g - 1` on `l^2 H` consists of the functions constant on cosets of `<g>`. Its
     projection has trace `1/|<g>|`, which is `0` for infinite order. So `rk(g - 1) = 1 - 1/|<g>| >= 1/2`.
3. **What this kills.**
   - Any certificate that `H` is not in `L_inf` must derive a contradiction from properties of the ultralimit rank
     that the von Neumann rank lacks, namely metric approximation by finite-dimensional modular matrices.
   - Every argument that refutes only the existence of such a rank function is void. This includes the
     stable-finiteness passage of `linear-sofic-group-algebra-is-stably-finite`, since the von Neumann rank makes
     `K[H]` stably finite. ∎
