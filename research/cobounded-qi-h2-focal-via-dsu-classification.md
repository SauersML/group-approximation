---
rg: 2
id: cobounded-qi-h2-focal-via-dsu-classification
kind: route
title: The Das–Simmons–Urbański classification, with the parabolic case killed by a Busemann bound, leaves only the focal case
target: cobounded-qi-h2-actions-without-free-groups-are-focal
requires:
  - geodesic-spaces-qi-to-h2-have-circle-gromov-boundary
  - busemann-null-isometries-have-no-boundary-contraction
  - two-boundary-fixed-points-block-cobounded-qi-h2-actions
---

This route proves items 1, 3 and 4, and the second and third properties of item 2, from quoted
statements plus elementary arguments. The first property of item 2 (`∂X ≅ S^1`) is exactly
`geodesic-spaces-qi-to-h2-have-circle-gromov-boundary`. Items 3 and 4 do not use it.

**Imported statements.** DSU is T. Das, D. Simmons, M. Urbański, *Geometry and dynamics in Gromov
hyperbolic metric spaces*, arXiv:1409.2155v7 (28 Jun 2016). The PDF was fetched and its text extracted
on 2026-09-16. Quotes are verbatim up to extraction spacing. Where the extraction lost a relation glyph,
this is marked.
- **(D0) Standing assumptions.** Notation 1.1.5: "X is a Gromov hyperbolic metric space", with a visual
  metric "with respect to a parameter b > 1 and a distinguished point o ∈ X". Properness and
  geodesicity are not assumed. Convention 1 says implied constants depend only on the displayed
  subscripts and on "universal objects such as the metric space X, the group G, and the distinguished
  point o".
- **(D1) Theorem 3.3.10.** "Any geodesic metric space which can be quasi-isometrically embedded into a
  geodesic hyperbolic metric space is also a hyperbolic metric space." It is attributed there to
  Bridson–Haefliger III.H.1.9.
- **(D2) Definition 3.3.2.** Hyperbolic means Gromov's inequality (3.3.4) for all four points:
  `⟨x|z⟩_w ≳_+ min(⟨x|y⟩_w, ⟨y|z⟩_w)`. The glyph was lost in extraction; the text then says every
  R-tree satisfies it "with an implied constant of 0".
- **(D3) Proposition 3.3.4.** "Every CAT(-1) space (in particular every algebraic hyperbolic space) is
  Gromov hyperbolic."
- **(D4) Definitions 3.4.1, 3.4.2, 3.4.9.**
  - Gromov sequences satisfy `⟨x_n|x_m⟩_o → ∞` as `n, m → ∞`.
  - Two are equivalent "if ⟨x_n|y_n⟩_o → ∞, or equivalently if ⟨x_n|y_m⟩_o → ∞".
  - `∂X` is the set of classes.
  - (3.4.6): `⟨ξ|y⟩_z := inf{liminf_n ⟨x_n|y⟩_z : (x_n) ∈ ξ}`.
  - (3.4.7): "B_ξ(y,z) = ⟨z|ξ⟩_y − ⟨y|ξ⟩_z".
- **(D5) Proposition 3.4.18 and Lemma 3.4.25.**
  - "The topological space (bord X, T) is completely metrizable."
  - "If g is an isometry of X, then it extends in a unique way to a continuous map g̃: bord X → bord X."
    Its proof is "left to the reader". It is used only to identify DSU's boundary action with ours.
- **(D6) Proposition 4.2.16.** "Fix g ∈ Isom(X) and ξ ∈ Fix(g). Then for all x ∈ X and n ∈ Z,
  B_ξ(x, g^{-n}(x)) [glyph lost] n log_b g'(ξ)", "with equality if X is strongly hyperbolic". Here
  `g'(ξ) > 0` is the dynamical derivative of Proposition 4.2.12.
- **(D7) Definitions 6.1.1 and 6.1.2.**
  - A fixed point `ξ ∈ ∂X` of `g` is "neutral or indifferent" if `g'(ξ) = 1`, attracting if
    `g'(ξ) < 1`, and repelling if `g'(ξ) > 1`.
  - `g` is "elliptic if the orbit {g^n(o) : n ∈ N} is bounded"; "parabolic if it is not elliptic and has
    a unique fixed point in ∂X, which is neutral"; "loxodromic if it has exactly two fixed points in
    ∂X, one of which is attracting and the other of which is repelling".
- **(D8) Theorem 6.1.4.** "Any isometry is either elliptic, parabolic, or loxodromic."
- **(D9) Definition 6.2.2 and Theorem 6.2.3.**
  - A semigroup `G` is "elliptic if G(o) is a bounded set"; "parabolic if G is not elliptic and has a
    global fixed point ξ ∈ Fix(G) such that g'(ξ) = 1 ∀g ∈ G"; "loxodromic if it contains a loxodromic
    isometry".
  - "Every semigroup of isometries of a hyperbolic metric space is either elliptic, parabolic, or
    loxodromic."
- **(D10) Definition 6.2.13 and Proposition 6.2.14.**
  - A loxodromic semigroup is "lineal if Fix(g) = Fix(h) for all loxodromic g, h ∈ G"; "of general type
    if it has two loxodromic elements g, h ∈ G with Fix(g) ∩ Fix(h) = ∅"; "focal if #(Fix(G)) = 1".
  - "Any loxodromic semigroup is either lineal, focal, or of general type."
- **(D11) Chapter 10.**
  - Definition 10.2.1 concerns "a collection of nontrivial semigroups" in Schottky position, whose
    generated semigroup is their Schottky product.
  - Lemma 10.2.2(i): "(Ping-Pong Lemma) The natural map π: ∗_{a∈E} G_a → G is an injection".
  - Proof of Proposition 10.5.4, "(A) ⇒ (F) for groups": "Fix loxodromic isometries g, h ∈ G with
    Fix(g) ∩ Fix(h) = ∅." For all sufficiently large `n`, "(V_1, V_2) is a global Schottky system for
    ((g^n)^Z, (h^n)^Z)".
  - Only that proof paragraph was read. It relies on DSU Theorem 6.1.10, which was not read.

**Setting.** `X` is geodesic and quasi-isometric to `H^2`. The group `G` has no non-abelian free
subgroup and acts by isometries with an `r_0`-dense orbit `G·x_0`.
- We may replace `G` by its image in `Isom(X)`. Suppose the image contained a free group `⟨a, b⟩`.
  Choose preimages `ã, b̃`. The homomorphism from the free group on two letters sending the letters to
  `ã, b̃` becomes injective after composing with the action map, so it is injective, and `G` would
  contain a free subgroup.
- So assume `G ≤ Isom(X)`, and put `o := x_0` and `r := r_0`.

**Step 1: item 1.**
- `H^2` is geodesic and CAT(−1), hence hyperbolic by (D3).
- A quasi-isometry `X → H^2` is a quasi-isometric embedding, so `X` is hyperbolic by (D1).
- By (D2) and (D0), there is one constant `δ ≥ 0` with
  `(x|z)_w ≥ min{(x|y)_w, (y|z)_w} − δ` for all `x, y, z, w ∈ X`.

**Step 2: boundary conventions and a Busemann estimate.**
- By (D4), DSU's `∂X` is the sequential boundary of `busemann-null-isometries-have-no-boundary-contraction`.
  DSU's boundary product `⟨u|v⟩_o` (an infimum of liminfs) is at most our `(u|v)_o` (a supremum over the
  same nonempty set).
- **(E)** Let `ξ ∈ ∂X`, `z_i → ξ`, and `y, w ∈ X`. Then `⟨y|ξ⟩_w ≤ liminf_i (y|z_i)_w` and
  `⟨y|ξ⟩_w ≥ limsup_i (y|z_i)_w − δ`.
  - The first holds because `(z_i)` is one of the sequences in the infimum.
  - For the second, let `z'_j → ξ`. Choose `i_l, j_l → ∞` with `(y|z_{i_l})_w → limsup_i (y|z_i)_w`
    and `(y|z'_{j_l})_w → liminf_j (y|z'_j)_w`.
  - The four-point inequality at base `w` gives
    `(y|z'_{j_l})_w ≥ min{(y|z_{i_l})_w, (z_{i_l}|z'_{j_l})_w} − δ`.
  - Here `(z_{i_l}|z'_{j_l})_w ≥ (z_{i_l}|z'_{j_l})_o − d(o,w) → ∞`, and the first entry is at most
    `d(y,w)`. So `liminf_j (y|z'_j)_w ≥ limsup_i (y|z_i)_w − δ`. Take the infimum over `(z'_j)`.
- **(E')** Write `B_z(y,w) := d(z,y) − d(z,w)` for `z ∈ X`. One checks directly that
  `B_z(y,w) = (w|z)_y − (y|z)_w`.
  - By (E) at the base points `y` and `w`, for every `ε > 0` and all large `i`,
    `|B_{z_i}(y,w) − B_ξ(y,w)| ≤ δ + 2ε`, with `B_ξ` as in (D4).
  - Since `|B_{z_i}(y,w)| ≤ d(y,w)`, this gives `|B_ξ(y,w)| ≤ d(y,w) + δ`.
- **(E'')** Representatives converge in `T`. If `x_n → ξ`, then by (E),
  `⟨x_n|ξ⟩_o ≥ limsup_i (x_n|x_i)_o − δ`, which tends to `∞` as `n → ∞`. So `x_n → ξ` in `(bord X, T)`.
- **The two boundary actions agree.** Let `g ∈ Isom(X)` and `x_n → ξ`.
  - By (D5), `g̃` is continuous, so `g̃(ξ) = lim_n g(x_n)` in `T`.
  - By (E''), `g(x_n) → [(g x_n)]` in `T`.
  - `T` is metrizable by (D5), so limits are unique, and `g̃(ξ) = [(g x_n)]`.
  - Hence DSU's fixed-point sets in `∂X` are our fixed-point sets.

**Step 3: item 2, second and third properties.** Let `T` be the topology of
`geodesic-spaces-qi-to-h2-have-circle-gromov-boundary`. By that claim, `(∂X, T) ≅ S^1`.
- **Isometries act by homeomorphisms.**
  - Let `k ∈ Isom(X)` and `u, v ∈ ∂X`. The representatives of `ku` are exactly the images under `k` of
    those of `u`. Since `(ky_i|kw_j)_o = (y_i|w_j)_{k^{-1}o} ≥ (y_i|w_j)_o − d(o, k^{-1}o)`, we get
    `⟨kv|ku⟩_o ≥ ⟨v|u⟩_o − d(o, k^{-1}o)`.
  - So `k(N_{t + d(o,k^{-1}o)}(u)) ⊆ N_t(ku)`, and `k` is continuous on `∂X`.
  - The same holds for `k^{-1}`, which is its inverse.
- **Convergence gives large products.** If `u_n → u` in `T`, then for every `t` eventually
  `u_n ∈ N_t(u)`. So `(u_n|u)_o ≥ ⟨u_n|u⟩_o > t`.

**Step 4: loxodromic isometries have unbounded orbits.** Let `g` be loxodromic, with attracting fixed
point `ξ`, and put `L := log_b g'(ξ)`, which is non-zero by (D7) and `b > 1`.
- Suppose (D6) gives only `B_ξ(x, g^{-n}x) ≤ nL + C` for all `x, n`. Then `x = o` with `n ↦ −n` gives
  `B_ξ(o, g^n o) ≤ −nL + C`. Also `x = g^n o` gives `B_ξ(g^n o, o) ≤ nL + C`. By the exact antisymmetry
  of (3.4.7), this is `B_ξ(o, g^n o) ≥ −nL − C`.
- The reverse one-sided reading is symmetric. Either way, `|B_ξ(o, g^n o) + nL| ≤ C` for all `n ∈ Z`.
- By (E'), `d(o, g^n o) ≥ |n| |L| − C − δ → ∞`.
- So `g` is not elliptic, has infinite order, and fixes no point of `X`.

**Step 5: `G` is not elliptic.** Otherwise `G·o` is bounded and `r`-dense, so `X` is bounded. But `X`
is quasi-isometric to `H^2`.

**Step 6: `G` is not parabolic.** Suppose it is, with `ξ` as in (D9).
- `ξ ∉ X`, since otherwise `d(go, o) ≤ 2d(o, ξ)` for all `g`. So `G` fixes `ξ ∈ ∂X`.
- Fix `z_i → ξ`, and let `q, p` be as in `busemann-null-isometries-have-no-boundary-contraction`(i),
  for this group `G`.
- **`p ≡ 0`.**
  - Let `g ∈ G`. Since `g'(ξ) = 1`, (D6) and the argument of Step 4 with `L = 0` give some `C_g` with
    `|B_ξ(o, g^m o)| ≤ C_g` for all `m`.
  - By definition, `q(g^m) = limsup_i (−B_{z_i}(g^m o, o))`.
  - By (E') and (3.4.7), this lies within `δ` of `−B_ξ(g^m o, o) = B_ξ(o, g^m o)`.
  - So `|q(g^m)| ≤ C_g + δ`, and `p(g) = lim_m q(g^m)/m = 0`.
- **A uniform bound.** By the bound `|p − q| ≤ 18δ` in part (i) of that claim, `|q(k)| ≤ 18δ` for all
  `k ∈ G`.
- **The Busemann function is bounded below.** Put `b(y) := limsup_i (d(y,z_i) − d(o,z_i))`.
  - `b(ko) ≥ liminf_i (d(ko,z_i) − d(o,z_i)) = −q(k) ≥ −18δ`.
  - `b` is 1-Lipschitz, since each `d(·, z_i) − d(o, z_i)` is.
  - `G·o` is `r`-dense, so `b ≥ −18δ − r` on `X`.
- **The Busemann function is unbounded below.** Put `t := 20δ + r + 1`.
  - Choose `N` with `(z_i|z_j)_o ≥ t` for all `i, j ≥ N`. In particular `d(o, z_N) ≥ t`.
  - Let `y` lie on a geodesic from `o` to `z_N`, with `d(o,y) = t`. Then `(y|z_N)_o = t`.
  - For `j ≥ N`, `(y|z_j)_o ≥ min{(y|z_N)_o, (z_N|z_j)_o} − δ ≥ t − δ`.
  - Since `d(y,z_j) − d(o,z_j) = d(y,o) − 2(y|z_j)_o`, we get `b(y) ≤ −t + 2δ = −18δ − r − 1`.
    Contradiction.

**Step 7: the loxodromic cases.** By Steps 5 and 6 and (D9), `G` contains a loxodromic `g`. By (D10),
`G` is lineal, focal or of general type.
- **General type is impossible.**
  - Take `g, h` as in (D11). For large `n`, `((g^n)^Z, (h^n)^Z)` is in Schottky position, so the natural
    map `(g^n)^Z ∗ (h^n)^Z → G` is injective.
  - By Step 4, `g^n` and `h^n` have infinite order. So `G` contains `Z ∗ Z`, a non-abelian free group.
    Contradiction.
- **Lineal is impossible.**
  - By (D7) and Step 4, `Fix(g) = {ξ, η}` with `ξ ≠ η` in `∂X`. Let `k ∈ G`.
  - `kgk^{-1}` is not elliptic, because `d(kg^nk^{-1}o, o) ≥ d(g^n o, o) − 2d(k^{-1}o, o)`.
  - Its fixed points in `bord X` are exactly `kξ` and `kη`. So it is not parabolic, and by (D8) it is
    loxodromic.
  - Lineality gives `k{ξ, η} = {ξ, η}`.
  - So `G_0 := {k ∈ G : kξ = ξ}` has index at most 2 and fixes `η` too. Write `G = G_0 ∪ G_0 s`.
  - Then `G·o = G_0·o ∪ G_0·(so)`, and `d(h so, h o) = d(so, o)`. So `G_0·o` is
    `(r + d(so, o))`-dense.
  - This contradicts `two-boundary-fixed-points-block-cobounded-qi-h2-actions`, applied to `G_0`,
    `ξ` and `η`.
- **Focal.**
  - `Fix(G) = {ξ}`, and `ξ ∉ X` by Step 4. So `G` fixes `ξ ∈ ∂X`, which is item 3.
  - `g` fixes exactly two points of `∂X` by (D7) and Step 2, and one of them is `ξ`. This is item 4. ∎

**Weakest points.**
- The imported proofs behind (D8)–(D11) were not checked. Only their statements, and the one proof
  paragraph in (D11), were read.
- The lost glyphs in (D2) and (D6). Step 4 shows that either one-sided reading of (D6) suffices.
- Lemma 3.4.25, whose proof DSU leaves to the reader. It is used only to transport fixed-point sets.
