---
rg: 2
id: torsion-chern-witnesses-within-one-of-phillips-toms-proof
kind: route
title: Split line-bundle sums with torsion first Chern classes replace the rational Chern character in the Hirshberg--Phillips symmetric bound
target: torsion-chern-witnesses-within-one-of-phillips-toms
requires:
  - rational-witnesses-miss-torsion-mean-dimension
---

External inputs, each cited where it is used:

* **[HP]** I. Hirshberg, N. C. Phillips, *Radius of comparison and mean
  cohomological independence dimension*, arXiv:2009.13045: Def.
  `N_0904_ElSymmP` (elementary symmetric polynomials of classes), Def.
  `D_0807_AppInv` (`(G_0, δ)`-invariance), and the proof of Thm `T_0907_gs`.
* **[Ka]** Karoubi, *K-theory*, Ch. V: integral Chern classes of vector bundles
  over compact metrizable spaces, the Whitney formula
  `c(E ⊕ E') = c(E) c(E')`, `c_j(E) = 0` for `j > rank E`, and
  `c(L) = 1 + c_1(L)` for a line bundle.
* **[Line]** For a compact Hausdorff `X`, `c_1 : Pic(X) -> Ȟ^2(X; Z)` is a
  bijection (exponential sheaf sequence).
* **[Sp]** Spanier, *Algebraic Topology*, §6.6 (Künneth theorem): for compact
  `A`, `B` and a field `F`, the cross product
  `Ȟ^*(A; F) ⊗ Ȟ^*(B; F) -> Ȟ^*(A × B; F)` is an isomorphism.
* **[Dr]** Dranishnikov, arXiv:math/0501523: the countable sum theorems for
  `dim` and `dim_G`, and the existence of the Pontryagin surface `Π_p` with
  `dim = dim_{Z/p} = 2` and `dim_Q = 1`.
* **[Ni]** Niu, arXiv:1906.09171: `rc(C(X) ⋊ Z) <= mdim/2` for minimal
  `Z`-systems.
* The node `rational-witnesses-miss-torsion-mean-dimension`, with its proof
  `rational-witnesses-miss-torsion-mdim-proof` (referred to as **[RW]**): the
  construction `X(K, ρ, η)`, Lemmas 1–3, Theorem B and Corollary 1'.

Throughout, `Ȟ` is Čech cohomology. For a compact metrizable `X`, `Ȟ^n(X; Z) = 0`
for `n > dim X`.

---

## 1. Theorem C (split torsion symmetric bound)

**Theorem C.** Let `G` be a countable amenable group acting on a compact
metrizable space `X` by `T`. Let `s >= 1` and let `L_1, ..., L_s` be complex line
bundles on `X`, with `x_j := c_1(L_j) ∈ Ȟ^2(X; Z)`. Assume

* **(sq)** `x_j ⌣ x_j = 0` in `Ȟ^4(X; Z)` for every `j` (automatic if `dim X <= 3`);
* **(ind)** there is `d >= 0` such that for every finite `G_0 ⊂ G` and every
  `δ > 0` there are a `(G_0, δ)`-invariant finite `F ⊂ G` and an integer
  `0 <= r <= |F|` with
  `e_{sr}( (T_g^* x_j)_{g ∈ F, 1 <= j <= s} ) != 0` in `Ȟ^{2sr}(X; Z)` and
  `2sr / |F| > d - δ`.

Here `e_n` is the `n`-th elementary symmetric polynomial in the `s|F|` classes,
and the classes commute because they have even degree. Let `m` be the greatest
integer with `m < d/2`. Then `rc(C(X) ⋊_T G) >= m`.

*Where the Q in [HP] enters.* [HP, Thm `T_0907_gs`] is the case `s = 1` of
this, with `η = x_1` realised rationally. Its proof uses the coefficients `Q` at
exactly one step: after replacing `η` by a multiple, it realises `η` as
`c(E) = 1 + η` for a rank-`k/2` bundle `E` (Lemma `Lemma:zero lower classes`,
via the rational Chern character). The rest of the proof uses only the
following two facts.

* **(a)** `a ∈ M_L(C(X))` is the projection onto a rank-`k/2` subbundle `E` of a
  trivial bundle.
* **(b)** If `Ẽ := ⊕_{g ∈ F} T_g^* E` is isomorphic to a subbundle of a trivial
  bundle of rank `R`, then `R >= (k/2)(|F| + r)`.

We take `k := 2s` and `E := L_1 ⊕ ... ⊕ L_s`, so that (a) holds. We prove (b)
integrally, and then repeat the analytic part of the argument.

*Proof of (b).* By the Whitney formula and `c(L) = 1 + c_1(L)` [Ka],
`c(Ẽ) = Π_{g ∈ F} Π_{j <= s} (1 + T_g^* x_j)`. By (sq) and naturality,
`(T_g^* x_j)^2 = T_g^*(x_j^2) = 0`. So `1 + T_g^* x_j` is a unit with inverse
`1 - T_g^* x_j`. Suppose `Ẽ ⊕ E' ≅ θ^R`, the trivial bundle of rank `R`. Then
`c(E') = c(Ẽ)^{-1}`, which gives

    c(E') = Π_{g, j} (1 - T_g^* x_j) = Σ_n (-1)^n e_n((T_g^* x_j)_{g,j}),

and hence `c_{sr}(E') = (-1)^{sr} e_{sr}(...) != 0` by (ind). Since `c_i` vanishes
above the rank [Ka], `rank E' >= sr`. So
`R = rank Ẽ + rank E' >= s|F| + sr = (k/2)(|F| + r)`. ∎(b)

*Analytic part.* This is [HP, proof of `T_0907_gs`], repeated here so the
estimates can be checked. Let `b ∈ M_L(C(X))` be a constant projection, and
suppose `a ≾ b` in `C(X) ⋊ G`. Fix `ε_0 > 0`.

1. There are an algebraic element `c = Σ_{g ∈ G_0} c_g u_g` with `G_0` finite
   and `‖c^* b c - a‖ < 1/4`. Choose `δ` with
   `δ(‖c‖+1) Σ ‖c_g‖ < 1/16`, and a `(G_0, δ)`-invariant `G_1 ∋ 1`.
2. Choose `ε_1` with `(d + k - ε_0)/(1 + ε_1) > d + k - 2ε_0`, and put
   `ε_2 = min(ε_0, ε_1 / (2|G_1|^2))`. Apply (ind) with `(G_0 ∪ G_1, ε_2)` to
   get `F` and `r`.
3. Put `S = ∪_{h ∈ G_1} h^{-1} F` and `Δ = |G_1|^{-1} χ_{G_1} * χ_S`. Then
   `Δ = 1` on `F`, `|Δ(t^{-1}g) - Δ(g)| < 2δ` for `t ∈ G_0`, and
   `|G_1 S \ F| < ε_1 |F|`.
4. Let `d_0` be multiplication by `Δ` on `ℓ^2(G) ⊗ C(X)`. Then
   `‖c d - d c‖ < 1/(8(‖c‖+1))`. The compression `c' = d^{1/2} c d^{1/2}` lies
   in the matrix algebra `B(ℓ^2(G_1 S) ⊗ M_L ⊗ C(X))`, and
   `‖(c')^* d^{1/2} b d^{1/2} c' - d^{3/2} a d^{3/2}‖ < 1/2`.
5. Cutting down by the diagonal projection `p` onto the coordinates in `F`,
   the projection `p a p`, which is the projection onto `Ẽ`, is Murray--von
   Neumann subequivalent to a constant projection of rank
   `|G_1 S| · rank(b)`. So `Ẽ` embeds in a trivial bundle of that rank.

By (b), `|G_1 S| rank(b) >= s(|F| + r)`. Hence

    rank(b) >= s (|F| + r) / ((1 + ε_1)|F|) = (k + 2sr/|F|) / (2(1+ε_1))
             > (d + k - ε_0) / (2(1 + ε_1)) > (d + k)/2 - ε_0.

Choose `ε_0` with `d/2 - ε_0 > m`, and take `rank(b) = m + s`. Then `a` is not
subequivalent to `b`. Every tracial state `τ` gives `d_τ(a) = s` and
`d_τ(b) = m + s`.

For every real `r' < m` we have `d_τ(a) + r' < d_τ(b)` for all `τ` but `a` is not
subequivalent to `b`. So `r'`-comparison fails for every `r' < m`, and
`rc >= m`. ∎

*Remark.* When the crossed product is simple, [HP] invoke Toms's closedness
(Prop. 6.3 of Toms's rc paper) to upgrade this to `rc > m`. That upgrade is not
needed below and is not claimed here.

---

## 2. The alphabet `K_p`

**Lemma 4.** For every prime `p` there are a compact metric space `K_p` and a
class `x ∈ Ȟ^2(K_p; Z)` such that:

* `dim K_p = 2`;
* `dim_Q K_p <= 1`;
* the reduction `x̄ ∈ Ȟ^2(K_p; Z/p)` is nonzero (so `dim_{Z/p} K_p = 2`);
* `x ⊗ 1 = 0` in `Ȟ^2(K_p; Q)`.

*Proof.* Let `Π_p` be the Pontryagin surface [Dr]. Since `dim_{Z/p} Π_p = 2`,
there is a closed `A ⊂ Π_p` with `Ȟ^2(Π_p, A; Z/p) != 0`. Put
`K_p := Π_p / A`, with basepoint `*`. It is compact metrizable, and Čech
cohomology of compact pairs satisfies `Ȟ^n(Π_p, A) ≅ Ȟ^n(K_p, *)`.

* **Dimensions.** Write `K_p = {*} ∪ ∪_i q(C_i)` with
  `C_i = {y : d(y, A) >= 1/i}`. The quotient map `q` is a homeomorphism from
  `C_i` onto the closed set `q(C_i)`. By the countable sum theorems [Dr],
  `dim K_p <= 2` and `dim_Q K_p <= dim_Q Π_p = 1`.
* **The lift.** `Ȟ^3(K_p; Z) = 0` because `dim K_p <= 2`. So the Bockstein
  sequence `Ȟ^2(K_p;Z) -> Ȟ^2(K_p;Z/p) -> Ȟ^3(K_p;Z)` shows that reduction is
  onto. Lift a nonzero class of `Ȟ^2(K_p;Z/p) ⊃ Ȟ^2(Π_p, A; Z/p)` to `x`.
* **Rational class.** `Ȟ^2(K_p; Q) = 0` because `dim_Q K_p <= 1`.
* **Dimension equality.** `dim K_p >= dim_{Z/p} K_p >= 2`, so `dim K_p = 2`. ∎

For `s >= 1` we have, by (P) of [RW] and the product formula over fields,
`dim_{Z/p} K_p^s = 2s = dim K_p^s` and `dim_Q K_p^s <= s`. So Corollary 1' of
[RW] applies verbatim with `K_p` in place of `Π_p`. (Its proof uses only these
three dimensions.)

---

## 3. Theorem D (the Pontryagin-alphabet minimal subshifts)

Fix `s >= 1`, `ρ > 0` and `η > 0` with `ρ + η < 1`, and let
`X := X(K_p^s, ρ, η) ⊂ (K_p^s)^Z` be the minimal subshift of [RW, §2], with
density `ρ_inf ∈ [ρ, ρ+η]`. Let `J ⊂ Z` be its hole set and `x^a ∈ X` the point
with all holes filled by the constant `a`.

**Theorem D.**

1. `X` is minimal and free, and `mdim(X, σ) = 2sρ_inf`.
2. `mcid(σ|X; Q) <= sρ_inf = mdim/2`. So both Hirshberg--Phillips rational
   lower bounds certify at most `mdim/4`.
3. `mdim/2 - 1 <= ⌈sρ_inf⌉ - 1 <= rc(C(X) ⋊ Z) <= mdim/2`.

*Proof.* (1) and (2) are [RW, Lemmas 1–3, Theorem B, Corollary 1'] with alphabet
`K_p`. The upper bound in (3) is [Ni]. For the lower bound we verify the
hypotheses of Theorem C.

**Line bundles.** By [Line], choose a line bundle `L` on `K_p` with
`c_1(L) = x`. For `j = 1, ..., s`, let `ev_j : X -> K_p` read the `j`-th factor
of coordinate `0`, and put `L_j := ev_j^* L` and `x_j = ev_j^* x`.

* **(sq)** holds because `x^2 ∈ Ȟ^4(K_p; Z) = 0`.
* With the convention `(σ^g y)_0 = y_g`, `T_g^* x_j = ev_{g,j}^* x`, where
  `ev_{g,j}` reads factor `j` of coordinate `g`.

**Unconstrained coordinates.** By construction [RW, §2], for every
`ω ∈ (K_p^s)^J` the point `x^ω` (the skeleton `x^0` with holes filled by `ω`)
lies in `X`. So for a finite `F ⊂ Z`, the map

    t : (K_p^s)^{F ∩ J} -> X,   t(ω)_g = ω_g  (g ∈ F ∩ J),   t(ω)_g = x^a_g  (otherwise)

is continuous with image in `X`.

* For `g ∈ F ∩ J`, `ev_{g,j} ∘ t` is the projection onto factor `(g, j)`.
* For `g ∉ F ∩ J`, `ev_{g,j} ∘ t` is constant, so `t^* T_g^* x_j = 0`, since
  `Ȟ^2` of a point is `0`.

**Nonvanishing.** Put `r := |F ∩ J|`. In `e_{sr}((T_g^* x_j)_{g ∈ F, j})`, every
monomial involves `sr` distinct indices `(g, j)`. After `t^*`, the only monomial
that can survive is the one using all of `(F ∩ J) × {1..s}`. Hence

    t^* e_{sr}(...) = Π_{(g,j) ∈ (F∩J)×[s]} pr_{g,j}^* x = x^{× sr}

is the `sr`-fold cross product. Its reduction mod `p` is `x̄^{× sr}`, which is
nonzero by the Künneth isomorphism over the field `Z/p` [Sp], because
`x̄ != 0`. So `e_{sr}(...) != 0` in `Ȟ^{2sr}(X; Z)`.

**Følner sets.** Take `F := I_l = [s_l, s_l + p_l)`. Then
`|F ∩ J| = |H_l| = ρ_l p_l >= ρ_inf |F|`. Intervals of length `p_l -> ∞` are
eventually `(G_0, δ)`-invariant for any finite `G_0 ⊂ Z` and `δ > 0`. So (ind)
holds with `d = 2sρ_inf`.

**Conclusion.** Theorem C gives `rc >= m`, where `m` is the greatest integer
with `m < sρ_inf`, i.e. `m = ⌈sρ_inf⌉ - 1 >= sρ_inf - 1 = mdim/2 - 1`. ∎

---

## 4. What this settles, and what it does not

* **The dichotomy of [RW] is decided up to an additive constant.** On the
  explicit minimal systems where every rational-cohomology mechanism caps at
  `mdim/4`, the conjectured value `mdim/2` is correct to within `1`. Branch
  (ii) of [RW] ("`rc < ρ_inf`, a counterexample") can hold only with a gap of
  less than `1`. For `s = 1` (`mdim < 2`) the bound in (3) is vacuous, and the
  dichotomy there stays open.
* **The class obstruction is sharp.** [RW] shows that witnesses in rational
  cohomology cannot certify `rc >= mdim/2 - O(1)` on these systems. Theorem D
  shows that integral witnesses can, with torsion first Chern classes whose
  mod-`p` products are nonzero. So the obstruction is exactly the kernel of the
  Chern character, and it is not an obstruction to the conjecture.
* **Mechanism.** The Chern character is avoided entirely. The bundle is split
  into line bundles, so the realisation problem ("which integral classes are
  top Chern classes with vanishing lower classes") disappears. The squares
  `x_j^2` vanish because the alphabet is 2-dimensional, which makes
  `c(⊕ T_g^* E)` invertible by a finite product.
* **Not covered.** Alphabets whose mod-`p` witnesses are not products of
  degree-2 classes. Examples are Dranishnikov compacta with `dim_{Z/p} = n` odd
  or top classes not generated by `H^2`. The integral realisation there needs
  `c(E) = 1 + η` with `η` torsion of order `p`, and the multiple `M` from the
  Chern character may be divisible by `p`. That is the precise remaining gate
  for Corollary 2 of [RW].
