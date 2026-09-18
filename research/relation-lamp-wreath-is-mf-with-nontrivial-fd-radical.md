---
rg: 2
id: relation-lamp-wreath-is-mf-with-nontrivial-fd-radical
kind: claim
title: The integer lamp wreath of a free group over a base without finite quotients is MF, its lamp augmentation lies in the finite-dimensional radical, and killing the square of the relator subgroup gives the dummy abelianized cover
distinct_from:
  free-generalized-wreath-over-residually-finite-group-is-mf: that has FREE-product lamps over an arbitrary set of a residually finite group; this has COMMUTING lamps over the coset set F/R of a free group, needs Hall separability of the finite windows H_L of R, and is used to calibrate the abelianized cover.
  infinite-cyclic-compression-lamp-mf: that proves MF for commuting integer lamps over H/L_1 with L_1 finitely generated; here the stabilizer R is normal of infinite index, so infinitely generated, and the models use a growing chain of finitely generated windows of R.
  free-abelianized-cover-fd-radical-is-commutator: that computes the finite-dimensional radical of the abelianized cover with the dummy Fox derivative; this shows the same lamp elements already lie in the finite-dimensional radical of the larger MF group W, so that computation alone cannot reach the MF radical.
  implemented-corona-actions-of-countable-groups-are-unconstrained: that realizes an action with holonomy only in the relative commutant; here the lamp image is a genuine exact module ZG, the relators commute EXACTLY with every lamp, and the only relation of the cover that fails is [R,R]=1.
  full-mf-radical-abelianized-cover-is-not-mf: that is the open non-MF statement for E; this is an MF calibration showing where any proof of it must act.
---

**ESTABLISHED.**

## Statement

Let:
- `F` be free on `x_1,...,x_n`;
- `R` be normal in `F`;
- `G = F/R`, with quotient map `q`, satisfy `G != 1` and have no nontrivial
  finite quotient.  This holds whenever `Rad_MF(G) = G`, because finite
  groups are MF.

Let `F` act on `ZG` through `q` by left translation, and put

```text
W = ZG x| F,        z = (e_1, 1),        so  v z v^-1 = e_(q(v))  (v in F).
```

Then:

1. **(Presentation.)**  `W = < x_1,...,x_n, z | [z, v z v^-1] (v in F), [r, z] (r in R) >`.
2. **(W is MF.)**  `W` embeds in the unitary group of a norm-matrix corona
   `prod_L M_(d_L) / (+)_L M_(d_L)`.
3. **(Lamp augmentation is finite-dimensionally invisible.)**  Let `K` be any
   field.  Every homomorphism `sigma : W -> GL_d(K)` kills the augmentation
   submodule `I_G ZG`, which is nonzero.  In particular, for `w in F \ R`,

   ```text
   [w, z] = e_(q(w)) - e_1  !=  0   in W,
   ```

   while `sigma([w,z]) = 1` for every finite-dimensional representation.
4. **(The cover is a quotient of W.)**  `[R,R]` is normal in `W`, and
   `E' = W/[R,R] = ZG x| E` with `E = F/[R,R]` acting through `G`.
   `E'` is the free abelianized cover `F_(n+1)/[R',R']` of the dummy
   presentation `G = < x_1,...,x_n, z | R, z >`, where `R' = <<R, z>>`.
   `E` embeds in `E'`.

## Consequences for `full-mf-radical-abelianized-cover-is-not-mf`

- **Reduction.**  `E` is a subgroup of `E'`, so "E' not MF" is formally
  weaker than `(DF)` for `E`.  It still serves the route
  `property-t-free-seed-via-leavitt-abelianized-cover`, since:
  - `E'` is the free abelianized cover of a finite presentation of the same
    group;
  - `E'` is torsion free, by `free-abelianized-cover-is-torsion-free`, which
    applies verbatim to the dummy presentation, as
    `free-abelianized-cover-fd-radical-proof` notes.
- **Calibration and no-go.**  `(DF)` for the dummy presentation says that
  imposing the single family of relations `[r,r'] = 1` (`r, r' in R`) on the MF
  group `W` destroys MF.  By items 2 and 3:
  - Consider any argument that places a nonzero lamp element, for example
    `[w,z]`, in `Rad_MF(E')`, and that uses only relations valid in `W`: the
    lamp module relations, the exact commutation of every relator with every
    lamp, the finite-dimensional radical, residual finiteness, or the absence
    of finite quotients of `G`.  Every such argument proves the same statement
    for `W`, and item 2 refutes it.
  - The step where every member of this class dies is the passage from `W` to
    `W/[R,R]`.  A proof must use `rho([r,r']) = 1`, that is, the commutativity
    of the relator images among themselves, and not only their commutation
    with the lamps.
  - The recorded Bernoulli no-go allows relators that do not commute with the
    observable algebra.  This one is sharper.  In the models of item 2 the
    relator unitaries fix the lamp algebra pointwise and exactly, the lamp
    module is exactly `ZG`, and the one relation of the cover that fails is
    `[R,R] = 1`.

## Imported classical theorems

- **(Hall)** M. Hall, "Coset representations in free groups", Trans. AMS 67
  (1949): every finitely generated subgroup `H` of a free group `F` is closed
  in the profinite topology.  That is, for every `t in F \ H` there is a
  finite-index subgroup `K <= F` with `H <= K` and `t notin K`.
- **(Malcev)** A. I. Malcev, 1940: a finitely generated subgroup of `GL_d(K)`,
  over any field `K`, is residually finite.
- **(Free groups are MF.)**  The proof below uses this only as follows.  A
  free group is residually finite, and a fixed-point-free permutation `P`
  satisfies `||P - 1|| >= sqrt 3`.  So regular representations of finite
  quotients that are injective on the balls `S_L` give an injective
  homomorphism into a corona.

## Proof

**Item 1.**  Let `W^` be the group so presented, and let `N` be the normal
closure of `z` in it.
- Conjugation by `z` fixes every `v z v^-1`, so `N` is generated by the
  elements `v z v^-1` with `v` a word in the `x_i`.  These commute pairwise,
  so `N` is abelian.
- For `r in R`, `v r z r^-1 v^-1 = v z v^-1`.  So `v z v^-1` depends only on
  `q(v)`, and `e_g -> v z v^-1` defines a surjective `F`-module map
  `ZG -> N`.
- `W^/N = F` is free, so `W^ = N x| F`.
- `W` satisfies the relations, which gives a surjection `W^ -> W` sending
  `N -> ZG`.  The composite `ZG -> N -> ZG` is the identity, so `N = ZG` and
  `W^ = W`.

**Item 3.**  Let `S = sigma(W)`.  It is finitely generated and linear, so it
is residually finite by Malcev.  Let `S -> P` be a finite quotient, and let
`A` be the image of `ZG`, an abelian normal subgroup.
- `F` acts on `A` by conjugation through a homomorphism `F -> Aut(A)`, and
  `Aut(A)` is finite.
- Each `r in R` commutes with `ZG` in `W`, so `R` lies in the kernel of this
  homomorphism.  It therefore factors through a finite quotient of `G`, and so
  it is trivial.
- Hence the image of `g.a - a` in `P` is trivial.  This holds for every finite
  quotient, so `sigma(g.a - a) = 1`.

`I_G ZG` is spanned by the elements `g.a - a`.  It is nonzero because
`G != 1`: `e_g - e_1 != 0` for `g != 1`.  Finally `[w,z] = e_(q(w)) - e_1`,
and this is nonzero exactly when `w notin R`.

**Item 4.**  `[R,R]` is normal in `F`.  It lies in `R`, so it acts trivially on
`ZG`.  For `a in ZG` and `c in [R,R]`,
`(a,1)(0,c)(-a,1) = (a - c.a, c) = (0,c)`, so `[R,R]` is normal in `W` and
`W/[R,R] = ZG x| E`.

To identify this group with `F_(n+1)/[R',R']`, write `F_(n+1) = F * <z>`.
- **Detection.**  The dummy Fox derivative `D` of
  `free-abelianized-cover-fd-radical-proof` has `D(z) = 1`, `D(x_i) = 0` and
  `D(v z v^-1) = e_(q(v))`.  It restricts to an equivariant homomorphism
  `R' -> ZG` that kills `[R',R']`.  So the normal closure of `z` in
  `E' = F_(n+1)/[R',R']` maps onto `ZG`.
- **Isomorphism.**  That closure is a quotient of `ZG`, because the conjugates
  of `z` commute (they lie in `R'/[R',R']`) and `R` fixes them.  So it is
  isomorphic to `ZG`.
- **Quotient and splitting.**  Modulo `z`, `R'` becomes `R` and `[R',R']`
  becomes `[R,R]`.  So `E'/<<z>> = F/[R,R] = E`.  The inclusion
  `F <= F_(n+1)` induces a splitting, because `[R,R] <= [R',R']`.
- **Action.**  The images of `R` and of the conjugates of `z` both lie in the
  abelian group `R'/[R',R']`.  So `E` acts on `<<z>>` through `G`.

Hence `E' = ZG x| E = W/[R,R]`, and `E` embeds in `E'` as the complement.

**Item 2.**  Fix `L >= 1` and let `S_L` be the ball of radius `L` in `F`.
Define
- `R_L = R cap S_L`;
- `H_L = <R_L>`, which is finitely generated and contained in `R`;
- `T_L = { u^-1 v : u, v in S_L,  u^-1 v notin R }`, a finite set disjoint
  from `H_L`.

For each `t in T_L`, Hall gives a finite-index `K_t` with `H_L <= K_t` and
`t notin K_t`.  Put `K_L = cap_t K_t`.  It has finite index, contains `H_L`,
and misses `T_L`.

*Lamp block.*  Let `Omega_L = F/K_L` with base point `o = K_L`, and let `F`
act by left multiplication, with permutation unitaries `P_v` on
`l^2(Omega_L)`.  Fix `lambda = e^(i)`, which is not a root of unity.  Let
`f_L(o) = lambda` and `f_L(c) = 1` for `c != o`, and send

```text
x_i -> P_(x_i),        z -> Z_L = diag(f_L).
```

Then `P_v Z_L P_v^* = diag(f_L o v^-1)`.  The two families of relators of
item 1 behave as follows.
- `[z, v z v^-1]` maps to a commutator of diagonal matrices, which is `1` at
  every level.
- `[r, z]` with `r in R_L`: `r^-1 c = o` exactly when `c = r o = o`, because
  `r in H_L <= K_L`.  So `f_L o r^-1 = f_L`, and `[P_r, Z_L] = 1` exactly.

Every relator therefore holds exactly at all levels `L >= |r|`.  So the maps
define a homomorphism `rho_1 : W -> U(prod_L B(l^2 Omega_L) / (+)_L)`.

*Detection of lamps.*  Let `a = sum_g a_g e_g != 0`, and fix `g_0` with
`a_(g_0) != 0`.  For large `L`, choose representatives `u_g in S_L` of the
`g in supp(a)`.  Then `rho_1(a)` at level `L` is the diagonal matrix

```text
c -> lambda^( sum_g a_g [ c = u_g o ] ).
```

At `c = u_(g_0) o`, the equality `u_g o = u_(g_0) o` means
`u_g^-1 u_(g_0) in K_L`.  For `g != g_0` this element lies in `T_L`, so it is
not in `K_L`.  So the entry at `c` is `lambda^(a_(g_0))`, and

```text
|| rho_1(a)_L - 1 || >= |lambda^(a_(g_0)) - 1| > 0,
```

a bound independent of `L`.

*Base block.*  Let `rho_2` send `z` to `1` and `x_i` to the regular
representations of finite quotients `F -> P_L` that are injective on `S_L`.
All relators of item 1 hold, since `z = 1`.  A nontrivial `v in F` is then
eventually a fixed-point-free permutation, at distance at least `sqrt 3` from
`1`.

*Injectivity.*  Take `rho = rho_1 (+) rho_2`, with the blocks put level by
level into `M_(d_L)`, `d_L = |Omega_L| + |P_L|`.  Let `(a, v) in W` be
nontrivial.
- If `v != 1`, then `rho_2(a, v) = rho_2(v) != 1`.
- If `v = 1`, then `a != 0` and `rho_1(a) != 1`.

So `rho` is injective and `W` is MF.

*The dummy commutator.*  Take `lambda = -1` instead, with `w notin R`.  At
`c = o`, `rho_1([w,z])_L` has entry `f_L(w^-1 o) f_L(o)^-1`.  Since
`w^-1 in T_L` for `L >= |w|`, this entry is `-1`.  So
`|| rho_1([w,z])_L - 1 || = 2` at every large level, even though `[w,z]` lies
in the finite-dimensional radical by item 3.

*What these models do not satisfy.*  The relator images `P_r`, `r in H_L`,
fix `o` and commute with every lamp.  Among themselves, though, they are
permutations of `Omega_L` with no reason to commute.  This is the relation
`[R,R] = 1` that `E'` adds, and the only one.
