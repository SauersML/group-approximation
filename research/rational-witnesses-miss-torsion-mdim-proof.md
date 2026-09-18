---
rg: 2
id: rational-witnesses-miss-torsion-mdim-proof
kind: route
title: Minimal Pontryagin-alphabet subshifts where rational mcid is at most half the mean dimension
target: rational-witnesses-miss-torsion-mean-dimension
requires: []
---

Self-contained proof. The external inputs are standard theorems. Each is cited
at its point of use:

* **[HP]** I. Hirshberg, N. C. Phillips, *Radius of comparison and mean
  cohomological independence dimension*, arXiv:2009.13045. This gives
  Def. `Def_mcid_Rev` (mcid), Def. `D_0814_CechFromCov`, Thm. `T_0826_Main`
  and Question `Q_0826_Coeffs`.
* **[Ts]** M. Tsukamoto, *Mean dimension of full shifts*, arXiv:1712.03050.
  This gives the basic-type criterion and Lemma "uniform lower bound on widim".
* **[Dr]** A. N. Dranishnikov, *Cohomological dimension theory of compact
  metric spaces*, arXiv:math/0501523. It covers monotonicity on closed subsets,
  the countable sum theorem, the product formula for field coefficients
  (Prop. 3.3), Pontryagin surfaces, the Bockstein inequalities and the
  realization theorem.
* **[Ni]** Z. Niu, arXiv:1906.09171, gives `rc(C(X) ⋊ Z) <= mdim/2` for
  minimal Z-systems. It is used only for context.

Notation. `K` is a compact metric space with `dim K < ∞` and metric `d_K`.
`F` is a commutative field. `dim_F` is cohomological dimension with
coefficients in `F`: `dim_F A >= m` iff `Ȟ^m(A, B; F) != 0` for some closed
`B ⊂ A`. In particular `Ȟ^m(A; F) != 0` implies `dim_F A >= m`. If
`char F = 0` then `dim_F = dim_Q`, and if `char F = p` then
`dim_F = dim_{Z/p}` ([Dr], §1–2).

`dim_F` has the following properties ([Dr]):

* **(M)** It is monotone on closed subsets.
* **(S)** If `A = A_1 ∪ ... ∪ A_s` with the `A_i` closed, then
  `dim_F A = max_i dim_F A_i`.
* **(P)** `dim_F (A × B) <= dim_F A + dim_F B`, with equality for fields.

On `K^Z` we use the metric `d(x,y) = Σ_i 2^{-|i|} d_K(x_i, y_i)` and
`D_I(x,y) = max_{i ∈ I} d(σ^i x, σ^i y)`, with `D_n = D_{[0,n)}`. For a finite
`I ⊂ Z`, `π_I : K^Z -> K^I` is the restriction map.

---

## 1. Theorem B (upper bound for mcid of a subshift)

For a subshift `X ⊂ K^Z` put `a_n := dim_F π_{[0,n)}(X)`. Shift invariance
gives `dim_F π_I(X) = a_{|I|}` for every interval `I` of length `n`. Since
`π_{[0,n+m)}(X) ⊂ π_{[0,n)}(X) × π_{[n,n+m)}(X)`, (M) and (P) give
`a_{n+m} <= a_n + a_m`, and also `a_n <= n dim_F K`. So

    wd_F(X) := lim_n a_n / n = inf_n a_n / n

exists by Fekete's lemma.

**Theorem B.** For every subshift `X ⊂ K^Z` and every field `F`,
`mcid(σ|X ; F) <= wd_F(X)`.

*Proof.* Fix an even `k >= 2` and put `d := mcid_k(σ|X; F)`. The definition holds with this `d`. The case
`k = 0` contributes `0`. Let `D := dim_F K`. Fix `ε > 0`, and choose `n_0`
with `a_n <= n (wd_F + ε)` for all `n >= n_0`.

By [HP, Def. `Def_mcid_Rev`] applied with this `ε`, there are a closed set
`Y ⊂ X`, a finite open cover `U` of `Y` in `X`, and a class
`η ∈ Ȟ^k(Y; U; F)` with the property that for every `(G_0, δ)` there exist
`F_fin ⊂ Z` and `F_0 ⊂ F_fin` satisfying (1) and (2) of the definition.

**Step 1 (η is a finite-window class).** `η` is `φ^* c` for a cocycle `c` on
the nerve `N(U ∩ Y)` and a canonical map `φ : Y -> |N(U ∩ Y)|`
[HP, Def. `D_0814_CechFromCov`]. Let `λ > 0` be a Lebesgue number of `U ∩ Y`
for `Y`. Choose `r` with `Σ_{|i|>r} 2^{-|i|} diam K < λ/3` and `ε' < λ/9`. A ball of sup-radius `ε'` in `K^{[-r,r]}` then pulls back to a set of `d`-diameter at most `3·2ε' + λ/3 < λ`.
Cover `π_r(Y) ⊂ K^{[-r,r]}` (write `π_r := π_{[-r,r]}`) by finitely many
`ε'`-balls `V_1, ..., V_s` in the sup metric. Each `π_r^{-1}(V_j) ∩ Y` has
`d`-diameter `< λ`, so it lies in some member of `U`. Choose one such member
for each `j`. This gives a refinement map
`ν : N(π_r^{-1}V ∩ Y) -> N(U ∩ Y)`.

A subfamily of `{π_r^{-1}(V_j) ∩ Y}` has nonempty intersection iff the
corresponding subfamily of `{V_j ∩ π_r(Y)}` does. So the two nerves coincide.
A canonical map `ψ : π_r(Y) -> |N(V ∩ π_r(Y))|` pulls back along `π_r` to a
canonical map for `Y`. Canonical maps into a nerve are unique up to homotopy,
and `ν ∘ (ψ ∘ π_r) ≃ φ`. Hence

    η = π_r^* η_r,     η_r := ψ^* ν^* c ∈ Ȟ^k(π_r(Y); F).

**Step 2 (the cup product is pulled back from a window).** Let
`Zc := ∩_{g ∈ F_0} σ^{-g}(Y)`. On `σ^{-g}(Y)` we have
`σ_g^* η = (π_r ∘ σ^g)^* η_r`, and `π_r ∘ σ^g` reads the coordinates
`g + [-r, r]`. Put `W := F_0 + [-r, r]` and `F' := F_fin + [-r, r]`. Every
factor of the product in (1) is the pullback along `Zc -> π_W(Zc)` of a class
on `π_W(Zc)`. Hence the product equals `(π_W|Zc)^* ξ` with
`ξ ∈ Ȟ^{k|F_0|}(π_W(Zc); F)`. `π_W` factors as
`Zc -> π_{F'}(Zc) -> π_W(Zc)`. So if the product is nonzero, then the
pullback of `ξ` to `π_{F'}(Zc)` is nonzero, and

    k |F_0| <= dim_F π_{F'}(Zc) <= dim_F π_{F'}(X)            (by (M)).

We pass to the larger window `F'` and do not stay on `W`: `dim_F` is not
monotone under projections, but a nonzero class stays nonzero under pullback.

**Step 3 (counting).** Decompose `F'` into its maximal intervals
`C_1, ..., C_m`. Then `π_{F'}(X) ⊂ Π_j π_{C_j}(X)` is closed, so by (M) and
(P)

    dim_F π_{F'}(X) <= Σ_j a_{|C_j|}
                    <= (wd_F + ε) |F'| + D · n_0 · m.

Now choose `G_0 = {0, 1}` and `δ > 0`. `(G_0, δ)`-invariance gives `|(F_fin + 1) Δ F_fin| < δ |F_fin|`. The pair `(ε, r, n_0, D)` is already
fixed. Let `F_fin, F_0` be as given. Each maximal interval of `F_fin` has a
right endpoint `x` with `x + 1 ∉ F_fin`. So `F_fin` has at most
`|(F_fin + 1) \ F_fin| < δ |F_fin|` components. Hence `m < δ|F_fin|` and
`|F'| <= |F_fin| (1 + 2rδ)`. Combined with (2):

    d - ε < k|F_0| / |F_fin| <= (wd_F + ε)(1 + 2rδ) + D n_0 δ.

Let `δ -> 0` (with `ε` fixed). This gives `d <= wd_F + 2ε` for every `ε`, so
`d <= wd_F`. Taking the sup over `k` finishes the proof. ∎

*Quantifier check.* The order in [HP] is: `ε`, then `(Y, U, η)`, then all
`(G_0, δ)`. So `r` depends only on `ε`, and `δ` may be chosen after `r`.
Step 3 is legitimate.

*Remark.* Only `G = Z` is used here. The same argument should carry over to
`Z^d`, with boundary counting in place of maximal intervals, but that case is
not claimed.

---

## 2. The minimal subshifts `X = X(K, ρ, η)`

Fix `a ∈ K`, `0 < ρ < 1`, and `0 < η` with `ρ + η < 1`. Fix `ε_l ↓ 0`.

**Blocks.** A *level-l block* is a word `B_l ∈ (K ⊔ {□})^{p_l}` with hole set
`H_l = {i : B_l(i) = □}`. Put `ρ_l := |H_l| / p_l`. For
`c ∈ K^{H_l ∪ (H_l + p_l)}`, write `(B_l B_l)[c]` for the word of length
`2p_l` with its holes filled by `c`.

* `p_1 = 1` and `B_1 = □`, so `ρ_1 = 1`.
* Given `B_l`, let `E_l` be a finite `ε_l`-net of
  `K^{H_l ∪ (H_l + p_l)}` in the sup metric, and put `m_l := |E_l|`.
* Choose integers `N_l > c_l + 2` and `c_l >= 2m_l`, as specified below.
* `B_{l+1}` is the concatenation of `N_l` copies of `B_l`:
  * copies `0, ..., 2m_l - 1` are the pairs `(B_l B_l)[e]`, one pair for each
    `e ∈ E_l`;
  * copies `2m_l, ..., c_l - 1` are `B_l` with holes filled by the constant
    `a`;
  * copies `c_l, ..., N_l - 1` are `B_l` with its holes kept.

So `p_{l+1} = N_l p_l`, `ρ_{l+1} = ρ_l (1 - c_l / N_l)`, and every
level-`(l+1)` block is a concatenation of level-`l` blocks whose non-hole
entries agree with `B_l`.

**Parameters.** Choose `N_1, c_1` with `1 - c_1/N_1 ∈ [ρ + η/2, ρ + η]`. For
`l >= 2` put `c_l = 2m_l`, and choose `N_l >= 2^l · 4m_l / η`. Then

    ρ_inf := lim_l ρ_l = (1 - c_1/N_1) · Π_{l>=2} (1 - 2m_l/N_l),

and `Π_{l>=2}(1 - 2m_l/N_l) >= 1 - Σ_l η/2^{l+1} >= 1 - η/2`. So
`ρ_inf ∈ [(ρ + η/2)(1 - η/2), ρ + η] ⊂ [ρ, ρ + η]`.

**Skeleton.** Put `s_1 = 0` and `s_{l+1} := s_l - c_l p_l`. Let
`I_l := [s_l, s_l + p_l)`. Then `I_l` is copy number `c_l` (a kept copy)
inside the level-`(l+1)` block placed on `I_{l+1}`.

* `s_l -> -∞` because `c_l >= 1`.
* `s_{l+1} + p_{l+1} = s_l + p_l + (N_l - c_l - 1) p_l >= s_l + p_l + p_l`.

So `I_1 ⊂ I_2 ⊂ ...` and `∪ I_l = Z`. Place `B_l` on `I_l`. This is
consistent: `B_{l+1}` restricted to `I_l` is `B_l` with holes kept. The
limit is a partial word `x^0 ∈ (K ⊔ {□})^Z` with hole set
`J := ∪_l (s_l + H_l)`. For `ω ∈ K^J`, let `x^ω ∈ K^Z` be `x^0` with its holes
filled by `ω`. Define

    X := closure { σ^n x^ω : n ∈ Z, ω ∈ K^J }.

This set is closed and shift-invariant.

**Property `(P_l)`.** `y ∈ K^Z` has `(P_l)` if there is a phase
`t ∈ Z/p_l` such that for all `j`, `y|[t + j p_l, t + (j+1) p_l)` agrees with
`B_l` at all non-hole positions.

* `(P_l)` is a finite union over `t` of closed conditions, so it is closed.
* Since every `I_{l'}` (`l' >= l`) is tiled by level-`l` blocks along
  `s_l + p_l Z`, every `x^ω` has `(P_l)`.

Hence **every `y ∈ X` has `(P_l)` for every `l`.**

**Lemma 1 (minimality).** `X` is minimal.

*Proof.* Let `y, y' ∈ X`, `L >= 1` and `ε > 0`. Choose `l` with
`p_l >= 2L + 1` and `ε_l < ε`.

* By `(P_l)`, the window `[-L, L]` of `y'` lies inside two consecutive
  level-`l` blocks of `y'`. Their content is `(B_l B_l)[c]` for some `c`.
* Pick `e ∈ E_l` with `sup |c - e| < ε_l`.
* By `(P_{l+1})`, `y` contains a level-`(l+1)` block within distance
  `p_{l+1}` of the origin. That block agrees with `B_{l+1}` at its non-holes,
  and those include the filled pair `(B_l B_l)[e]`.

So some `σ^n y` agrees with `y'` on `[-L, L]` up to `ε_l < ε` in each
coordinate. Hence `y'` lies in the orbit closure of `y`. ∎

A minimal infinite Z-system is free. `X` is infinite once `dim K >= 1` and
`ρ_inf > 0`.

**Lemma 2 (window dimension).** For every field `F` and every `l`,
`wd_F(X) <= ρ_l dim_F K`, hence `wd_F(X) <= ρ_inf dim_F K`. Likewise
`lim_n dim π_{[0,n)}(X)/n <= ρ_inf dim K`.

*Proof.* Let `I` be an interval. By `(P_l)`,

    π_I(X) ⊂ ∪_{t ∈ Z/p_l} {b_t} × K^{I ∩ (t + H_l + p_l Z)},

where `b_t` is the determined non-hole part. This is a finite union of closed
sets. Each is homeomorphic to `K^{m_t}` with
`m_t <= |H_l| (|I|/p_l + 1)`.

* By (S) and (P), `dim_F π_I(X) <= ρ_l dim_F K (|I| + p_l)`.
* For covering dimension, the finite sum theorem and `dim K^m <= m dim K`
  give the same bound.

Divide by `|I|` and let `|I| -> ∞`. ∎

**Lemma 3 (mean dimension).**

    ρ_inf · max_F dim_F K <= mdim(X, σ) <= ρ_inf dim K.

*Upper bound.* Given `ε`, choose `r` with `Σ_{|i|>r} 2^{-|i|} diam K < ε`.
Then `π_{[-r, n+r)} : (X, D_n) -> π_{[-r,n+r)}(X)` has fibers of
`D_n`-diameter `< ε`. So `widim_ε(X, D_n) <= dim π_{[-r,n+r)}(X)`. Divide by
`n` and use Lemma 2.

*Lower bound.* Fix `F` and let `q := dim_F K`. By [Ts, Lemma "uniform lower
bound on widim"], there is `δ > 0` independent of `n` with
`widim_δ(K^n, sup metric) >= nq`. Tsukamoto's proof shows this for every field
with `q = dim_F K`, not only for the one realizing `dim K - 1`.

* Let `Y_l := { x^ω : ω` arbitrary on `s_l + H_l`, `ω = a` elsewhere `}`.
  `Y_l` is a closed subset of `X`, and `ω|_{s_l + H_l} ↦ x^ω` is a
  homeomorphism `K^{H_l} -> Y_l`.
* Since `d(x,y) >= d_K(x_0, y_0)`, we have
  `D_{I_l}(x^ω, x^{ω'}) >= max_{j ∈ s_l + H_l} d_K(ω_j, ω'_j)`.
* A `δ`-embedding of `(Y_l, D_{I_l})` composed with this map is a `δ`-embedding
  of `(K^{H_l}, sup)`. So
  `widim_δ(X, D_{I_l}) >= widim_δ(Y_l, D_{I_l}) >= |H_l| q`.
* `σ^{s_l}` is an isometry from `(X, D_{I_l})` to `(X, D_{p_l})`. So
  `widim_δ(X, D_{p_l}) >= ρ_l p_l q`.

The limit `lim_n widim_δ(X, D_n)/n` exists (subadditivity), so it can be
computed along `n = p_l`. This gives `mdim(X) >= ρ_inf q`. ∎

If `K` has basic type, then some field `F` has `dim_F K = dim K`
([Ts, proof sketch of Thm "basic/exceptional"], from [Dr, Lemma 2.9,
Thm 3.16]). So `mdim(X) = ρ_inf dim K`.

**Theorem A.** If `K` has basic type, then `X` is minimal,
`mdim(X) = ρ_inf dim K`, and `mcid(σ|X; F) <= ρ_inf dim_F K` for every field
`F`.

*Proof.* Combine Lemmas 1–3, Theorem B and Lemma 2. ∎

---

## 3. Corollaries and the exact failing step

**Corollary 1 (Pontryagin alphabet).** Let `K = Π_p`, the Pontryagin surface.
By [Dr, §1] its dimensions are:

* `dim Π_p = dim_{Z/p} Π_p = 2`;
* `dim_Q Π_p = 1`;
* `dim_{Z/q} Π_p = 1` for `q != p`.

So `Π_p` has basic type. For `X = X(Π_p, ρ, η)`,
`mdim(X) = 2ρ_inf` and `mcid(σ|X; Q) <= ρ_inf = mdim(X)/2`.

**Corollary 1' (products of Pontryagin surfaces, large mean dimension).**
Let `K = (Π_p)^s` for `s >= 1`. By (P) and the product formula for field
coefficients, `dim_{Z/p} K = 2s` and `dim_Q K <= s`. Also `dim K <= 2s`, and
`dim K >= dim_{Z/p} K`, so `dim K = 2s`. Lemma 3 with `F = Z/p` gives
`mdim(X) >= 2sρ_inf`, and its upper bound gives `mdim(X) <= 2sρ_inf`. So for
`X = X((Π_p)^s, ρ, η)`:

    mdim(X) = 2sρ_inf,     mcid_k(σ|X; Q) <= mcid(σ|X; Q) <= sρ_inf = mdim(X)/2.

Here the mean dimension is arbitrarily large, so the obstruction below is not
an artifact of `mdim < 2`.

**Corollary 2 (Dranishnikov alphabet).** Fix `n >= 2`. Define the Bockstein
function:

* `D(Q) = 1`;
* `D(Z_(p)) = D(Z/p) = n` and `D(Z/p^∞) = n-1`;
* `D(Z_(q)) = D(Z/q) = D(Z/q^∞) = 1` for all primes `q != p`.

It satisfies the Bockstein inequalities:

* `D(Z/p^∞) <= D(Z/p) <= D(Z/p^∞) + 1`;
* `D(Z/p) <= D(Z_(p))`;
* `D(Q) <= D(Z_(p))`;
* `D(Z_(p)) <= max(D(Q), D(Z/p^∞) + 1)`;
* `D(Z/p^∞) <= max(D(Q), D(Z_(p)) - 1)`.

The analogous inequalities at `q` are trivial. By the realization theorem
([Dr, §2]) there is a compactum `K_n` with this Bockstein function. The
finite-dimensional form is used, with `dim K_n = max D = n`, as produced by
Edwards–Walsh resolutions. Corollary 2 depends on this citation; Corollary 1
does not. For it,
`dim K_n = dim_Z K_n = n = dim_{Z/p} K_n`, so `K_n` has basic type, while
`dim_Q K_n = 1`. So `mdim(X) = nρ_inf` and
`mcid(σ|X; Q) <= ρ_inf = mdim(X)/n`.

**Consequences for the Phillips–Toms `>=` inequality.** Let `X` be as in
Corollary 1' (`s >= 1`, `mdim = 2sρ_inf`) or Corollary 2 (`mdim = nρ_inf`),
and let `k` be even. Write `c := mcid(σ|X; Q)`, so `c <= mdim/2` resp.
`c <= mdim/n`.

* [HP, Thm `T_0826_Main`] gives `rc(C(X) ⋊ Z) >= m - k/2`, where
  `m < mcid_k(σ; Q) <= min(k, c)` ([HP, Rmk `R_0820_AtMostk`]). Hence the
  certified value is at most `max_k (min(k, c) - k/2) <= c/2`. That is at most
  `mdim/4` for Corollary 1' and at most `mdim/(2n)` for Corollary 2.
* [HP, §`Sec_0908_Symm`] has a sharper mechanism, the symmetric variant
  `mcid^{gs}_k`. Its Thm `T_0907_gs` gives `rc >= m` with
  `m < mcid^{gs}_k(σ; Q)/2`. But Lemma `R_0904_Smalller` gives
  `mcid^{gs}_k <= mcid_k <= c`. So this mechanism also certifies at most
  `c/2`, i.e. `mdim/4` resp. `mdim/(2n)`.
* The Phillips–Toms value is `mdim/2`. [Ni] gives `rc <= mdim/2`.
* [HP, Remark `R_0808_OnlyUseQ`]: their lower-bound mechanism needs `R = Q`.
  A rational class is converted, through the Chern character, into
  non-comparison of projections. The Chern character kills torsion.

So on these minimal systems both known general lower-bound mechanisms certify
at most half (Pontryagin products), resp. a `1/n` fraction (Dranishnikov
alphabets), of the conjectured radius of comparison.

**The exact failing step.** It is clause (1) of [HP, Def. `Def_mcid_Rev`].

* A nonzero *rational* cup product of the `F_0`-translates of a degree-`k`
  class forces
  `k|F_0| <= dim_Q π_{F_fin + [-r,r]}(X) <= (ρ_inf dim_Q K + o(1)) |F_fin|`
  (Theorem B, Steps 2–3).
* The coordinate spaces carry only `dim_Q K` rational degrees per free
  coordinate, but `dim K` covering-dimension degrees.
* Mean dimension counts `dim K`, because Tsukamoto's `Z/p`-witnesses
  `(K,A)^n` exist.

**Dichotomy.** Take `X = X(Π_p, ρ, η)`. [Ni] gives
`rc(C(X) ⋊ Z) <= mdim/2 = ρ_inf`. So exactly one of the following holds:

* **(i)** `rc(C(X) ⋊ Z) = ρ_inf`, and the proof must use witnesses invisible
  to rational cohomology; or
* **(ii)** `rc(C(X) ⋊ Z) < ρ_inf`, and Phillips–Toms fails on this explicit
  minimal system.

**Relation to [HP, Question `Q_0826_Coeffs`].** HP ask whether `mcid = mdim`
for subshifts and whether the answer depends on the coefficients. They prove
lower bounds only for finite CW alphabets. Corollaries 1–2 show that for
minimal subshifts over (non-CW) basic-type alphabets, rational mcid can be at
most `mdim/n` for any `n`.

## 4. The open loophole (torsion and relative witnesses)

For `K = Π_p`, let `A ⊂ K` be closed with `Ȟ^2(K, A; Z/p) != 0`. Then:

* `Ȟ^3(K, A; Z) = 0`, since `dim_Z K = dim K = 2` (Alexandroff). So in the Bockstein sequence
  `Ȟ^2(K,A;Z) -> Ȟ^2(K,A;Z/p) -> Ȟ^3(K,A;Z)`, the reduction map
  `Ȟ^2(K,A;Z) -> Ȟ^2(K,A;Z/p)` is onto.
* `Ȟ^2(K,A;Z) ⊗ Q ⊂ Ȟ^2(K,A;Q) = 0`, since `dim_Q K = 1`. So the lifts are
  torsion.

So Tsukamoto's witnesses are relative first Chern classes of line bundles `L`
on `K`, trivialized on `A`, with torsion Chern class. Their exterior products
over `F_0` are nonzero mod `p` on `(K,A)^{F_0}`. These certify the full
`mdim`.

The gate for option (i) is a *mod-p* comparison theorem. Turn the relative
torsion Euler classes of Villadsen-type sums `⊕_{g ∈ F_0} pr_g^* L` into Cuntz
non-comparison in the orbit-breaking subalgebra `C*(C(X), C_0(X \ Y) u)`, with
an `O(1)` loss independent of `dim K`. Rational Chern-character arguments
cannot do this step. The natural candidates are `K`-theory with `Z/p` coefficients and
Dadarlat–Pennig-type generalized Villadsen obstructions. Neither is
established here.
