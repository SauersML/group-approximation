---
rg: 2
id: houghton-cohomological-dehn-lower-bounds-cap-proof
kind: route
title: Inflation from Z^(n-1) caps every cocycle certificate for H_n at the Euclidean area
target: houghton-cohomological-dehn-lower-bounds-cap-at-quadratic
requires: []
---

Notation is as in the target. `K = FSym(Y_n)` is the kernel of the translation
map `π : H_n -> Q = Z^(n-1)`; this is the exact sequence
`1 -> Sym_fin(Y_n) -> H_n -> Z^(n-1) -> 1` recorded on
`zaremsky-1-24-houghton-dehn-function`. Put
`F_i = Sym({1..n} x {1..i})`. Then `F_1 ⊂ F_2 ⊂ ...` are finite subgroups of
`K` whose union is `K`, since a finitary permutation moves finitely many points.

## Step 1. Cohomology of the finitary kernel (part (B))

Let `V` be any real vector space with a linear `G`-action. We use only its
restriction to `K`.

**1a. Finite groups.** For a finite group `F`, `H^q(F; V) = 0` for `q >= 1`,
because `|F|` annihilates `H^q(F; V)` and is invertible on `V`
(K. S. Brown, *Cohomology of Groups*, GTM 87, Chapter III, Corollary 10.2).
Concretely: a 1-cocycle `c` satisfies `c = δv` with
`v = -(1/|F|) Σ_(f ∈ F) c(f)`. For a 2-cocycle `z`, set
`b(g) = (1/|F|) Σ_(f ∈ F) z(g, f)`; then `z = δb`.

**1b. `H^2(K; V) = 0`.** Let `z` be an inhomogeneous 2-cocycle on `K`.

- By 1a, `z|_(F_i) = δ b_i` for some `b_i : F_i -> V`.
- The difference `b_(i+1)|_(F_i) - b_i` is a 1-cocycle on `F_i`, so by 1a it
  equals `δ v_i` for some `v_i ∈ V`, with `(δ v_i)(f) = f v_i - v_i`.
- The map `δ v_i` is defined on all of `F_(i+1)` and is a cocycle, so
  replacing `b_(i+1)` by `b_(i+1) - δ v_i` keeps `δ b_(i+1) = z` and gives
  `b_(i+1)|_(F_i) = b_i`.
- By induction the `b_i` are compatible. Their union `b` satisfies `δ b = z`
  on `K`, because every pair of elements lies in some `F_i`.

**1c. `H^1(K; V) ≅ lim^1_i V^(F_i)`.** Here `lim^1` of the tower of
inclusions `V^(F_1) ⊇ V^(F_2) ⊇ ...` is the cokernel of the map
`Φ : Π_i V^(F_i) -> Π_i V^(F_i)`, `(a_i) ↦ (a_i - a_(i+1))`.

- Let `c` be a 1-cocycle on `K`. By 1a, `c|_(F_i) = δ v_i`, where `v_i` is
  unique modulo `V^(F_i)`.
- Restricting to `F_i` gives `δ v_i = δ v_(i+1)`, so
  `u_i := v_i - v_(i+1) ∈ V^(F_i)`.
- Replacing `v_i` by `v_i + a_i`, with `a_i ∈ V^(F_i)`, changes `(u_i)` by
  `Φ(a)`. So `c ↦ [(u_i)]` is well defined into `coker Φ`. It is linear, and
  it kills coboundaries: for `c = δ v`, take `v_i = v`.
- Injective: if `(u_i) = Φ(a)`, then the vectors `v_i - a_i` are all equal to
  one `v ∈ V`, and `c = δ v` on every `F_i`, hence on `K`.
- Surjective: given `u_i ∈ V^(F_i)`, set `v_1 = 0` and `v_(i+1) = v_i - u_i`.
  Since `v_(i+1) - v_i ∈ V^(F_i)`, the maps `δ v_i` and `δ v_(i+1)` agree on
  `F_i`. So they glue to a 1-cocycle on `K` with invariant `[(u_i)]`.

**1d. Stabilizing towers.** Suppose `V^(F_i) = W` for all `i >= i_0`. Then
`Φ` is onto, so `lim^1 = 0`. Given `(u_i)`, we need `a_i ∈ V^(F_i)` with
`a_i - a_(i+1) = u_i`.

- Put `a_(i_0) = 0`, and `a_(i+1) = a_i - u_i` for `i >= i_0`. Here
  `u_i ∈ W`, so `a_i ∈ W = V^(F_i)`.
- For `i < i_0`, put `a_i = a_(i+1) + u_i`, going downward. Both terms lie in
  `V^(F_i)`, since `V^(F_(i+1)) ⊆ V^(F_i)`.

- For finite-dimensional `V` the subspaces `V^(F_i)` decrease, so they
  stabilize.
- For `V = R` with trivial action every term is `R`.

In both cases `H^1(K; V) = 0`. This proves (B).

## Step 2. Inflation is onto in degree 2

Assume `H^1(K; V) = 0`. By Step 1b, `H^2(K; V) = 0` as well. Consider the
Lyndon–Hochschild–Serre spectral sequence
`E_2^(p,q) = H^p(Q; H^q(K; V)) => H^(p+q)(G; V)`
(Brown, *Cohomology of Groups*, Chapter VII, Section 6).

- The rows `q = 1, 2` vanish.
- So the only nonzero term of total degree 2 is `E_2^(2,0) = H^2(Q; V^K)`.
- It receives `d_2` from `E_2^(0,1) = 0`, and `d_r` for `r >= 2` leaves it
  into negative rows.

Hence the edge map, which is inflation `H^2(Q; V^K) -> H^2(G; V)`, is an
isomorphism.

## Step 3. Cochain form of a certificate (part (A))

Extend `X` to a `K(G,1)` complex `Y` by attaching cells of dimension `>= 3`.
Its universal cover `Y~` contains `X~` as its 2-skeleton. Write `C^k_G(-; V)`
for the `G`-equivariant `V`-valued cellular cochains.

**The certificate defines a class.**

- Let `(V, ω)` be a cocycle certificate. Every 2-cycle of the 2-dimensional
  simply connected complex `X~` is an integral combination of images of
  spherical diagrams (Hurewicz, `π_2(X) = H_2(X~) = Z_2(X~)`).
- `ω` vanishes on each of them, because two diagrams with the same boundary
  have the same value. So `ω` vanishes on `∂ C_3(Y~) ⊆ Z_2(X~)`.
- Hence `ω` is a 2-cocycle of `C^*_G(Y~; V)`, and it has a class `[ω]` in
  `H^2(G; V)`.

**The inflated comparison.**

- Let `T` be the standard cube torus `K(Q,1)`, with universal cover
  `T~ = R^(n-1)` cubulated by unit cubes. Choose a cellular map `ψ : Y -> T`
  inducing `π` on `π_1`. It exists because `T` is aspherical: each edge `s`
  goes to the lattice path of `π(s)`, relator discs go to fillings in `T`, and
  higher cells extend.
- Its lift `ψ~ : Y~ -> R^(n-1)` is `π`-equivariant. The chain map `ψ~_*`
  lifts the identity of `Z`, so `ψ~^*` induces inflation
  `H^*(Q; V^K) -> H^*(G; V)` (Brown, Chapter III, Section 8).
- By Step 2 there are a `Q`-equivariant `V^K`-valued cubical 2-cocycle `ω''`
  on `R^(n-1)` and `β ∈ C^1_G(X~; V)` with `ω = ψ~^* ω'' + δ β`.
- Put `M'' = max ||ω''(square)||` and `M_β = max ||β(edge)||`. Both are finite,
  because there are finitely many cell orbits and the actions are isometric.
- Let `L` be the longest lattice path `ψ(s)`, for `s ∈ S`.

**The estimate.** Let `w` be null-homotopic with `|w| <= x`, and let `D` be
any van Kampen diagram for it, with 2-chain `[D]` and `∂[D] = [w]`. Then

```text
ω([D]) = ω''(ψ~_*[D]) + β([w]),     ||β([w])|| <= M_β x.
```

- `ψ~_*[D]` is a cubical 2-chain whose boundary is the chain of the closed
  lattice path `ψ(w)`, of length at most `L x`.
- Let `c` be a van Kampen diagram for `ψ(w)` over
  `<e_1, ..., e_(n-1) | [e_i, e_j]>` with at most `(L x)^2` squares
  (sort the letters). Then `ψ~_*[D] - [c]` is a 2-cycle of the contractible
  cube complex `R^(n-1)`, so it is a boundary of a cubical 3-chain.
- `ω''` is a cocycle, so it vanishes there. Hence
  `ω''(ψ~_*[D]) = ω''([c])`, with `||ω''([c])|| <= M'' L^2 x^2`.

Therefore `||ω(D)|| <= M'' L^2 x^2 + M_β x` for every such `D`. Dividing by
`sup ||ω|| > 0` gives `L_ω(x) <= C x^2`. This proves (A).

The whole certificate factors through the Euclidean area of the translation
shadow `ψ(w)`, plus a term linear in `|w|`. That is the single step at which
every member of the class dies.

## Step 4. Central extensions (part (C))

Let `1 -> <z> -> E -> G -> 1` be central, with `E` finitely generated.

**A real certificate from the extension.**

- Lift each `s ∈ S` to `s~ ∈ E`. Then `S~ ∪ {z}` generates `E`, and any finite
  generating set gives a bi-Lipschitz word metric.
- For `r ∈ R`, `r(S~)` lies in `<z>`. Write `r(S~) = z^(e(r))` and extend
  `e` to the 2-cells of `X~` invariantly, with `V = R` and the trivial action.
- If `w = Π_j u_j r_j^(ε_j) u_j^(-1)` freely, then centrality gives
  `w(S~) = z^(Σ_j ε_j e(r_j))`. So `e(D)` is determined by the boundary word,
  and `(R, e)` is a cocycle certificate.
- `H^1(K; R) = Hom(K, R) = 0`, because `K` is a torsion group.
- By Step 3, `|e(D_w)| <= C |w|^2 + C |w|`.

**The distortion bound.** Let `u` be a word of length `ℓ` in
`S~^(±1) ∪ {z^(±1)}` with `u = z^N` in `E`.

- Delete the `z`-letters to get `u'`, with `|u'| <= ℓ`. Centrality gives
  `u'(S~) = z^(N - m)`, where `m` is the `z`-exponent sum, so `|m| <= ℓ`.
- The image of `u'` in `G` is trivial, so `N - m = e(D_(u'))`.
- Hence `|N| <= C ℓ^2 + (C + 1) ℓ`, and `ℓ >= c sqrt(|N|)` for large `|N|`.

This proves (C).

## Step 5. Abelian subgroups (part (D))

Let `A <= G` be finitely generated abelian.

- `A ∩ K` is a finitely generated subgroup of `A`, and it is locally finite,
  so it is finite.
- `π(A) ≅ A / (A ∩ K)` is free abelian of some rank `r`. Pick `a_1, ..., a_r`
  in `A` mapping to a basis of `π(A)`, and put `B = <a_1, ..., a_r> ≅ Z^r`.
  Then `B` has finite index in `A`.
- For `b ∈ B`: `|b|_G >= |π(b)|_(Z^(n-1)) / L'`, where `L'` is the largest
  generator image. Also `|π(b)| >= c' |b|_B`, because
  `π|_B : B -> π(A) <= Z^(n-1)` is an isomorphism onto a subgroup, and
  subgroups of `Z^(n-1)` are undistorted.
- So `B` is undistorted, and hence so is `A`.

In particular every infinite cyclic subgroup is undistorted. This also follows
because finitary elements have finite order, so an infinite-order element has a
nonzero translation vector.

## Scope

- Nothing here constrains non-abelian lower-bound mechanisms. Examples are
  corridor or HNN arguments over non-abelian associated subgroups, counting
  arguments on `FSym`, and asymptotic-cone arguments.
- It also does not constrain certificates over modules with
  `lim^1_i V^(F_i) != 0`, such as `ℓ^∞(G)` and permutation modules on
  `G/F`-type sets.
- Those are the survivors, and a proof that some `H_n` is superquadratic has to
  be one of them.
