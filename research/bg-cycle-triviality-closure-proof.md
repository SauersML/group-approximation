---
rg: 2
id: bg-cycle-triviality-closure-proof
kind: route
title: A smallest-prime count kills finite-order BG cycles, translation lengths make cycle elements elliptic, global retractions detect them on vertex groups, coordinate descent handles wreaths and malnormality of M in M * F_m reduces free-product mapping tori to M ⋊ Z
target: bg-cycle-triviality-is-closed-under-the-pbh-calculus
requires:
  - pbh-class-closed-under-relative-holomorphs
---

Notation is that of the target. A BG cycle is `(a_0, …, a_(e-1); s)` with
`a_(i+1) a_i a_(i+1)^-1 = a_i^2` for `0 <= i <= e-1`, where `a_e = s a_0 s^-1`.

## 0. Basic moves

- **(M1) Images and conjugates.** A homomorphism sends BG cycles to BG cycles.
  Conjugating all entries and `s` by one element gives a BG cycle.
- **(M2) Rotation.** `(a_1, …, a_(e-1), a_e; s)` is a BG cycle, since
  `s a_1 s^-1` conjugates `a_e = s a_0 s^-1` to `a_e^2`. So if every cycle of `G`
  has trivial first entry, every entry is trivial.
- **(M3) Unrolling.** Put `a_(ke+i) = s^k a_i s^-k` for `k >= 0` and
  `0 <= i <= e-1`. Then `a_(n+1) a_n a_(n+1)^-1 = a_n^2` for every `n >= 0`, being
  the `s^k`-conjugate of relation `i`. So for every `f >= 1`,
  `(a_0, …, a_(fe-1); s^f)` is a BG cycle.
- **(M4) Descent.** If `a_(n+1) = 1` then `a_n = a_n^2`, so `a_n = 1`. Hence if some
  `a_n = 1`, then `a_0 = 1`.

Items A2, B1 follow from (M1): a nontrivial `a_0` survives in some factor or
quotient, where the image is a BG cycle. Each condition "for all `a_i, s`,
the relations imply `a_0 = 1`" is a quasi-identity. So it passes to subgroups,
products, directed unions (a cycle is finitely many elements) and ultraproducts
(Łoś). Linear groups: a cycle lies in a finitely generated linear group, which is
residually finite (Mal'cev).

## A1. Finite-order lemma

Suppose every element conjugate to its own square has finite order, and let
`(a_i; s)` be a BG cycle. Each `a_i` with `i <= e-1` is conjugate to its square by
`a_(i+1)`, so it has finite order `n_i`. Also `a_e` is conjugate to `a_0`, so
`n_e = n_0`. Since `a_i` and `a_i^2` have the same order, each `n_i` is odd.

Suppose some `n_i > 1`. Let `p` be the smallest prime dividing some `n_i`
(`0 <= i <= e-1`), attained at index `i`, so `p` is odd.
- Conjugation by `a_(i+1)` maps the finite group `<a_i>` into itself, hence onto
  itself.
- It maps `a_i^p` to `a_i^(2p)`, so it preserves `<a_i^p>`.
- On `<a_i>/<a_i^p> ≅ Z/p` it induces multiplication by `2`, an automorphism of
  order `o = ord_p(2) >= 2`.
- `a_(i+1)^(n_(i+1)) = 1` acts trivially, so `o | n_(i+1)`.

Choose a prime `q | o`. Then `q | n_(i+1)`, and `q | n_0` when `i = e-1`. But
`o | p-1`, so `q < p`, contradicting the minimality of `p`. So all `a_i = 1`.

## A3. Hyperbolic groups

An infinite-order element `g` of a hyperbolic group has stable length
`τ(g) = lim |g^n|/n > 0` (Gromov; Coornaert--Delzant--Papadopoulos, Ch. 10). This
is a conjugacy invariant with `τ(g^2) = 2 τ(g)`. So an element conjugate to its
square has `τ = 0` and finite order, and A1 applies.

## A4. Semisimple CAT(0) actions

A semisimple isometry `g` has translation length `|g|` with `|g^2| = 2|g|`, which
is a conjugacy invariant (Bridson--Haefliger II.6.2 and II.6.8). So if `g` is
conjugate to `g^2` then `|g| = 0`, and semisimplicity gives a fixed point. By
hypothesis `g` has finite order, and A1 applies.

For cellular isometries of an `M_κ`-polyhedral complex with finitely many shapes,
every element is semisimple (Bridson, Proc. AMS 127 (1999)). An element fixing a
point stabilizes the open cell containing it, so it lies in a finite cell
stabilizer and has finite order. Lattices in products of locally finite trees
and Kac--Moody lattices act this way, as do groups acting properly on
finite-dimensional CAT(0) cube complexes.

## A5. PL interval groups

Let `g ≠ 1` be an orientation-preserving PL homeomorphism of a compact interval `I = [x_-, x_+]` with
finitely many breakpoints. Its support (the set where `g(x) ≠ x`) has finitely
many components.
- At the left endpoint `x_0` of a component, `g` fixes `x_0` and has right
  derivative `λ(x_0) ≠ 1`. Otherwise `g` would be the identity on some
  `[x_0, x_0 + ε)`.
- `g^2` has the same support components, with right derivatives `λ^2`.
- If `h g h^-1 = g^2` with `h` a PL homeomorphism, `h` maps components of `g` onto
  components of `g^2`. By the chain rule for right derivatives, `λ_(g^2)(h x_0)`
  equals `λ_g(x_0)`.

(Compactness is used: every support component then has a left endpoint in `I`. On `R`
the translation `x ↦ x+1` is conjugate to its square by `x ↦ 2x`, so A5 fails there.)

So the finite multiset `{|log λ(x_0)|}` equals its double as a multiset. Its
maximum `μ > 0` then satisfies `μ = 2μ`, a contradiction. So `g = 1`, every entry
of a BG cycle is trivial, and the group lies in `𝒫`.

## B2. Periodic quotients

Let `N ◁ G` with `N ∈ 𝒫` and `G/N` periodic. By A1, `G/N ∈ 𝒫`. By (M1) and (M2)
every `a_i ∈ N`. Let `f` be the order of `sN`, so `s^f ∈ N`. By (M3),
`(a_0, …, a_(fe-1); s^f)` is a BG cycle in `N`, so `a_0 = 1`. A finite-index
overgroup of `K ∈ 𝒫` contains the normal core `N <= K` of finite index.

## B3. Tree principle

Let `G` act on a tree without inversions, and let `(a_i; s)` be a BG cycle. For a
tree automorphism without inversion, `ℓ(g) = min_v d(v, gv)` is a conjugacy
invariant with `ℓ(g^n) = |n| ℓ(g)`, and `ℓ(g) = 0` iff `g` fixes a vertex (Serre,
*Trees*, I.6.4, Prop. 24--25). Since `a_1` conjugates `a_0` to `a_0^2`,
`ℓ(a_0) = 0`, and `a_0 ∈ G_v` for some vertex `v`. If `a_0 ≠ 1`, pick
`ρ : G → H ∈ 𝒫` with `ρ(a_0) ≠ 1`. Then `ρ` of the cycle is a BG cycle of `H` with
nontrivial first entry, which is impossible. So `a_0 = 1`.

**Detecting homomorphisms.** If `ρ_u : G → G_u` is a retraction onto a vertex
group, then `ρ_u(g x g^-1) = ρ_u(g) x ρ_u(g)^-1 ≠ 1` for `1 ≠ x ∈ G_u`. So `ρ_u`
detects every conjugate of `G_u`.

- **Free products** `*_j A_j` with all `A_j ∈ 𝒫`. Use the Bass--Serre tree and the
  retractions killing the other factors.
- **Finite trees of groups with retract edge groups** (so also `X *_C Y` over a
  common retract `C`), with vertex groups in `𝒫`. For a vertex `u`, define `ρ_u`
  on `G_w` by composing the retractions `G_w → C_(ww') ⊆ G_(w')` along the path from
  `w` to `u`. On an edge group `C_(ww') ⊆ G_w`, with `w'` nearer `u`, both
  definitions agree, because the retraction fixes `C_(ww')`. So `ρ_u` is a
  well-defined retraction `G → G_u`.
- **Graph products** over a finite graph `Γ` with `G_v ∈ 𝒫`. Induct on `|Γ|`:
  `G_Γ = G_(st v) *_(G_(lk v)) G_(Γ∖v)`. Here `G_(lk v)` is a retract of both
  factors (kill the other vertex groups). `G_(st v) = G_v × G_(lk v) ∈ 𝒫` by B1
  and induction, and `G_(Γ∖v) ∈ 𝒫` by induction.
- **Equivariant graph products** `G_Γ ⋊ C` with `C` acting vertexwise and every
  `G_v ⋊ C ∈ 𝒫`. The same splitting holds with each factor `⋊ C`, and the
  retractions are `C`-equivariant, so they extend to the semidirect products. The
  star factor `(G_v × G_(lk v)) ⋊ C` embeds in
  `(G_v ⋊ C) × (G_(lk v) ⋊ C)` by `(g, h, c) ↦ ((g, c), (h, c))`, which is a
  homomorphism because `C` acts factorwise. Induct on `|Γ|`. The base case is
  `G_v ⋊ C`, and for the empty link the edge group is `C`.

## B4. Restricted permutational wreath products

Let `W = (⊕_(x ∈ X) A) ⋊ G`, with `(g·φ)(x) = φ(g^-1 x)`, and `A, G ∈ 𝒫`. Let
`(a_i; s)` be a BG cycle in `W`.
- The quotient `W → G` and (M2) put every `a_i`, hence every unrolled `a_n`, in the
  base `N = ⊕_X A`.
- Coordinate maps `N → A` are homomorphisms, so for each `x`,
  `a_(n+1)(x) a_n(x) a_(n+1)(x)^-1 = a_n(x)^2` for all `n`.
- Write `s^k = φ_k g^k` with `φ_k ∈ N` and `g ∈ G`. Then
  `a_(ke)(x) = φ_k(x) a_0(g^-k x) φ_k(x)^-1`.

- **Infinite orbit.** If `<g> x` is infinite, the points `g^-k x` are distinct, so
  `g^-k x ∉ supp(a_0)` for large `k`. Then `a_(ke)(x) = 1`, and (M4) applied to the
  coordinate sequence gives `a_0(x) = 1`.
- **Finite orbit.** If `<g> x` has size `f`, then `g^f x = x` and
  `c_n = a_n(x)` (`0 <= n <= fe`) satisfy the relations with
  `c_(fe) = φ_f(x) c_0 φ_f(x)^-1`. So `(c_0, …, c_(fe-1); φ_f(x))` is a BG cycle in
  `A`, and `a_0(x) = c_0 = 1`.

Hence `a_0 = 1`. The lamp wreaths of
`bh-type-a-class-closed-under-permutational-lamp-wreaths` are the case of a finite
`A`.

## B5. Free-product mapping tori

Let `Q = M * F_m`, `β ∈ Aut(Q)`, `β(m) = k α(m) k^-1` for `m ∈ M`, and
`G = Q ⋊_β Z = < Q, t | t q t^-1 = β(q) >`.

**Only if.** Put `t' = k^-1 t`. Then `t' m t'^-1 = α(m)`, so `<M, t'>` is a
quotient of `M ⋊_α Z`. An element `m t'^l` of it is trivial only when `l = 0`
(look at the exponent of `t`) and `m = 1`. So `M ⋊_α Z <= G`.

**If.** Assume `M ⋊_α Z ∈ 𝒫`, and let `(a_i; s)` be a BG cycle in `G` with
`a_0 ≠ 1`.

1. **Into `Q`.** The quotient `G → Z` and (M2) give `a_0, …, a_e ∈ Q`. By (M4)
   no `a_i` is trivial.
2. **Into `M`.** `Q` acts on the Bass--Serre tree of the graph of groups with one
   vertex group `M` and `m` trivial loops. Every vertex stabilizer is a conjugate
   of `M`, and edge stabilizers are trivial, so `M` is malnormal:
   `M ∩ qMq^-1 ≠ 1` forces `q ∈ M`. As in B3, `a_0` is elliptic, so after
   conjugating the whole cycle by an element of `Q` we get `a_0 ∈ M`.
   - If `a_i ∈ M ∖ 1`, then `a_i^2 ≠ 1` (else `a_i = a_(i+1)^-1 a_i^2 a_(i+1) = 1`),
     and `a_i^2 ∈ M ∩ a_(i+1) M a_(i+1)^-1`. So `a_(i+1) ∈ M`.
   - By induction `a_0, …, a_e ∈ M`.
3. **Twists of `M` by powers of `β`.** For every `l ∈ Z` there is `k_l ∈ Q` with
   `β^l(m) = k_l α^l(m) k_l^-1` on `M`:
   - `k_0 = 1`;
   - `k_(l+1) = β(k_l) k`;
   - `k_(l-1) = β^-1(k_l k^-1)`, from `β^-1(m) = β^-1(k)^-1 α^-1(m) β^-1(k)`.
4. **Back to `M ⋊_α Z`.** Write `s = r t^l` with `r ∈ Q`. Then
   `a_e = r β^l(a_0) r^-1 = w α^l(a_0) w^-1`, where `w = r k_l`. Here
   `α^l(a_0) ∈ M ∖ 1` and `a_e ∈ M`, so malnormality gives `w ∈ M`. Put
   `s' = w t'^l ∈ <M, t'>`. Then `s' a_0 s'^-1 = w α^l(a_0) w^-1 = a_e`. So
   `(a_0, …, a_(e-1); s')` is a BG cycle in `M ⋊_α Z` with `a_0 ≠ 1`, which is a
   contradiction.

**Partial conjugations.** If `β|_M = c_k`, then `α = id` and `M ⋊_α Z = M × Z`,
which lies in `𝒫` iff `M` does (B1, A2). Every ascending HNN extension `J *_β` with
`β(J) ⊆ J` embeds in `Q ⋊_β Z`: its elements are `t^-p j t^q`, and such an element
maps to `1` only if `p = q` and `j = 1`. This covers (T) of
`pbh-class-closed-under-relative-holomorphs`.

## B6. Relative holomorphs over residually finite M

If `M` is finitely generated and residually finite, then `M * F_n` is finitely
generated and residually finite (Gruenberg). So `Aut(M * F_n)` is residually finite
(Baumslag 1963), and `Aut_M(M * F_n)` lies in `𝒫` by A2 and B1. By (H) of
`pbh-class-closed-under-relative-holomorphs`, `Q ⋊ Aut_M(Q)` embeds in
`Aut_M(M * F_(m+1))`.

## C. Consequence

The listed seeds are in `𝒫`:
- char-zero and char-`p` linear groups (A2);
- `Aut(F_n)`, 3-manifold groups and mapping class groups, which are residually
  finite (Baumslag; Hempel with geometrization; Grossman);
- hyperbolic groups (A3);
- product-of-trees lattices (A4);
- power-map free mapping tori, which are ascending HNN extensions of `F_n` and so
  residually finite by Borisov--Sapir (Invent. Math. 160, 2005);
- PL interval groups (A5).

The listed operations preserve `𝒫` (B1--B6). So the smallest class `𝒢` so
generated lies in `𝒫`. The non-examples `BG` and `H4` are recorded in the target:
`a` is nontrivial in `BG`, and `g_0` is nontrivial in `H4` (Higman).

## Calibration

- `BS(1,2) = < a, b | b a b^-1 = a^2 >` is linear, so it lies in `𝒫`. Adding the
  stable letter `t a t^-1 = b` closes a cycle of length 1. This is exactly the step
  B does not contain, and part (b) of `stable-permutation-hnn-of-type-a-actor-is-type-a`
  does.
- The Druţu--Sapir index-two subgroup `< x, y, t | t x t^-1 = x^2, t y t^-1 = y^2 >`
  lies in `𝒫` by B5 (partial conjugation `c_σ` on `BS(1,2) * <z>`), so it contains
  no BG cycle.
- A1 fails for exponent 3 (`SL(2,3)`, `a = i`, `b = j`), because there
  `ord_p(3)` can be `1` at `p = 2`. So the parity step is where the exponent enters.
