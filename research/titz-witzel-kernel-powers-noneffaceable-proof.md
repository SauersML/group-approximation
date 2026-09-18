---
rg: 2
id: titz-witzel-kernel-powers-noneffaceable-proof
kind: route
title: Local Gauss–Bonnet on a thickness-3 C~_2 quotient gives χ = number of vertices, perfectness and asphericity give H^2, simplicity forbids effacement, and Malcev converts degree two into finite-dimensional projective representations
target: titz-witzel-kernel-powers-have-noneffaceable-mod-p-classes
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

**Imported** from `titz-witzel-simple-kazhdan-cat0-lattices-exist`, verbatim content
of Titz Mite–Witzel, arXiv:2509.05054, Theorem A and Corollary B:
* `Y = Y_1^2` is a finite triangle complex.
* Its universal cover `X` is an exotic building of type `C~_2` of thickness
  `q + 1 = 3`.
* `Γ = π_1(Y)` is a uniform lattice, so it is CAT(0) and Kazhdan.
* Its finite residual `K` has finite index `d` and is simple.
* `Γ` acts freely and cocompactly on the contractible locally finite complex `X`.
  So `Γ` and `K` are torsion-free of type `F`, and `K\X` is a finite aspherical
  2-complex (derived facts on that node).

**Standard facts used.** Each is cited where it is used:
* the Künneth and universal coefficient theorems;
* property (T) passes to lattices, in particular to finite-index subgroups, and
  is closed under extensions, hence under finite products (Bekka–de la
  Harpe–Valette, *Kazhdan's Property (T)*, §1.7; section-level citation, the
  item numbers were not re-checked);
* products of CAT(0) spaces are CAT(0) (Bridson–Haefliger II.1.16);
* Malcev: finitely generated linear groups are residually finite.

## Step 1: χ(Y) equals the number of vertices of Y

Here `Y` is a finite 2-dimensional Δ-complex, and the link `Lk(x)` of a vertex
`x` has one vertex for each edge-end at `x` and one edge for each triangle-corner
at `x`. Each edge has two ends and each triangle three corners, so

`χ(Y) = V - E + T = Σ_x ( 1 - |Lk(x)^(0)|/2 + |Lk(x)^(1)|/3 )`.

The action is free, so each `Lk(x)` is isomorphic to the link of a lift of `x`
in `X`. In a `C~_2` building of thickness `3` (order `q = 2`) there are two kinds
of vertex link.
* **Special vertices.** The link is the incidence graph of a generalized
  quadrangle of order `(2,2)`. That quadrangle has `(s+1)(st+1) = 15` points,
  15 lines and `15·3 = 45` flags, so the link has 30 vertices and 45 edges. Its
  term is `1 - 15 + 15 = 1`.
* **The other type.** The link is a generalized digon of order `(2,2)`, namely
  `K_(3,3)`, with 6 vertices and 9 edges. Its term is `1 - 3 + 3 = 1`.

Hence `χ(Y) = |Y^(0)|`.

Links are invariant under the action, and the two kinds of link are not
isomorphic. Every triangle of `X` is a chamber, with two special corners and
one of the other type. So `Y` has a vertex of each kind, and `|Y^(0)| >= 2`. For the
complex recorded in `titz-witzel-flat-hitting-sparse-branched-covers`, with
vertices `v, w, u_1..u_5`, this gives `χ(Y) = 7`. That value is not needed
below.

## Step 2: H^2(K;F_p)

`B := K\X` is a `d`-sheeted cover of `Y`. It is a finite aspherical 2-complex,
so `χ(K) = χ(B) = d·χ(Y) = d·|Y^(0)|`.
* **`H_1(K;Z) = 0`.** `K` has finite index in the infinite group `Γ`, so it is
  infinite. An infinite simple group is non-abelian, and so it is perfect.
* **`H_2(K;Z)` is free.** `H_2(B) = Z_2(B)` is a subgroup of the free abelian
  group `C_2(B)`. Its rank is `b = χ(K) - 1 + b_1 = d·|Y^(0)| - 1 >= 1`.

By the universal coefficient theorem,
`H^2(K;F_p) ≅ Hom(Z^b, F_p) ⊕ Ext(0, F_p) = F_p^b`. Also `H^1(K;F_p) = 0` and
`H^q(K;F_p) = 0` for `q >= 3`. This proves item 1.

## Step 3: powers

**Finiteness and geometry.** `K^m` acts freely and cocompactly on `X^m`. That
space is CAT(0) (Bridson–Haefliger II.1.16) and contractible, and `K^m\X^m = B^m`.
So `K^m` is torsion-free and of type `F`, and it is finitely presented. It has (T)
by the standard facts above.

**No proper finite-index subgroup.** Let `L <= K^m` have finite index. For each
factor `K_i`, the intersection `L ∩ K_i` has finite index in `K_i`. A simple
infinite group has no proper finite-index subgroup: the normal core of one would
be a proper normal subgroup of finite index, hence nontrivial. So `L ∩ K_i = K_i`
for every `i`. The factors generate `K^m`, so `L = K^m`.

**Cohomology.** By Künneth over the field `F_p`,
`H^*(K^m;F_p) ≅ H^*(K;F_p)^(⊗m)`. The group `H^*(K;F_p)` is concentrated in
degrees `0` and `2`. So `H^q(K^m;F_p)` vanishes for odd `q`, and for `j <= m` it is
`F_p^(C(m,j) b^j) ≠ 0` in degree `2j`.

A nonzero class could only be effaced on `K^m` itself, where it is still nonzero.
So no nonzero class is effaceable. The profinite completion of `K^m` is trivial,
so inflation into degree `2j >= 2` has zero source and nonzero target. Hence
`K^m` is not good. This proves item 2.

## Step 4: the degree-two dictionary (item 3)

**Setting.** `G` is finitely generated. `M = Z/p` is central in
`1 -> M -> E -π-> G -> 1`, which is classified by `x`. Fix a set-theoretic section
`σ` with `σ(1) = 1`. Then `c(g,h) = σ(g)σ(h)σ(gh)^(-1) ∈ M`. A representation of
`C*(G, χ∘c)` is the same thing as a map `g ↦ U_g` into unitaries with
`U_g U_h = χ(c(g,h)) U_(gh)`. Such maps correspond exactly to unitary
representations `ρ` of `E` with `ρ|_M = χ`, via
`ρ(σ(g) m) = χ(m) U_g`. This is a homomorphism because
`σ(g)σ(h) = c(g,h) σ(gh)`.

* **(i) ⇒ (ii).** Suppose `x|_W = 0` with `[G:W] < ∞`. Then `π^(-1)(W) -> W`
  splits by a homomorphism `s`, and `S = s(W)` has index `p[G:W]` in `E`, with
  `S ∩ M = 1`. Its normal core `N` has finite index in `E` and `N ∩ M = 1`. So
  `E/N` is finite and injective on `M`.
* **(ii) ⇒ (iii).** Let `f: E -> F` be finite and injective on `M`. Then `f(M)` is
  central in `F`, and `ℓ²(F)` restricted to `f(M)` is a multiple of the regular
  representation. So the `χ`-isotypic subspace `V ≠ 0` is `F`-invariant. Then
  `E -> F -> U(V)` is a representation with `ρ|_M = χ`, of dimension at most `|F|`.
* **(iii) ⇒ (ii).** A finite-dimensional `ρ` with `ρ|_M = χ` has finitely
  generated linear image `ρ(E) <= U(n)`. By Malcev, `ρ(E)` is residually finite.
  Since `χ` is faithful, `ρ` is injective on `M`. Choose a finite quotient of
  `ρ(E)` that separates the `p - 1` nontrivial elements of `ρ(M)` from 1.
  Composed with `ρ`, it is a finite quotient of `E` that is injective on `M`.
* **(ii) ⇒ (i).** Let `N = ker(E -> F)`, so `N ∩ M = 1`. Then `π|_N` is an
  isomorphism onto `W = π(N)`, which has finite index. Its inverse splits the
  pullback over `W`, so `x|_W = 0` (Brown IV.3).

For `G = K` and `x ≠ 0`, item 2 says (i) fails, hence so does (iii). This proves
item 3.

## Step 5: calibration and the bi-exactness remark (item 4 and scope)

**Item 4** is logic. `K^m` satisfies `P` and has a nonzero, non-effaceable class
in `H^(2m)(K^m;F_p)`. The listed consequences of (T) hold for every Kazhdan group:
* Kazhdan projections (Akemann–Walter);
* Delorme–Guichardet;
* `w`-rigidity of Bernoulli actions (Popa);
* `b_1^(2) = 0` (Bekka–Valette).

These are imported only in the sense that they are consequences of (T). The
calibration needs nothing about them beyond "`P(K^m)` holds".

**Non-hyperbolicity.** Apartments of `X` are Euclidean planes, isometrically
embedded, so `X` is not Gromov hyperbolic. `K` acts on `X` properly and
cocompactly, so by Švarc–Milnor `K` is quasi-isometric to `X`, and `K` is not
hyperbolic.

**Bi-exactness of the powers.** If `G` is bi-exact, then `L(G)` is solid (Ozawa,
Acta Math. 192 (2004); Brown–Ozawa §15). Solidity means that `A' ∩ L(G)` is amenable for every diffuse
`A ⊆ L(G)`. So a solid algebra contains no `A ⊗ B` with `A` diffuse and `B`
non-amenable, since `B ⊆ (A ⊗ 1)'`. For `m >= 2`, `L(K^m)` contains
`L(K) ⊗ L(K)`. Here `L(K)` is diffuse, since `K` is infinite, and non-amenable,
since `K` is Kazhdan and infinite. So `K^m` is not bi-exact.

Whether `K` itself is bi-exact is left open. It is the one gate that `K` could
still decide in degree two.
