---
rg: 2
id: fpbs-rank-one-homogeneous-bb-certificates-fail-proof
kind: route
title: Unimodularity makes the horospherical kernel of a focal amenable subgroup compact, and equivariant compact midpoint sets in the symmetric space make every crossing part of (G/H)^2 dissipative
target: fpbs-rank-one-homogeneous-bb-certificates-fail
requires: []
---

Full written proof. Imported inputs:
- **(I1) Rank-one geometry.** `G` is a connected simple Lie group of real rank one with finite centre. Then:
  - `G` acts properly and transitively by isometries on `X = G/K`, which after rescaling is a proper CAT(-1)
    space;
  - maximal flats are geodesic lines;
  - every isometry in `G` is elliptic, parabolic or hyperbolic;
  - a hyperbolic isometry `a` has translation length `tau(a) > 0` and a unique axis `Min(a)`, a geodesic line (no
    flat strips in CAT(-1)), and it fixes exactly the two endpoints of that axis in `dX`;
  - `P = Stab(xi) = M A_0 N`, with `M` compact centralizing `A_0`, and `M A_0` normalizing `N`;
  - `M A_0` is the stabilizer of the two ends `xi`, `eta` of the standard line `ell_0` through `o`; `M` fixes
    `ell_0` pointwise, and `a_t` translates it by `t`;
  - `Ad(a_t)` on `Lie(N)` has all eigenvalues of modulus `e^{-t}` or `e^{-2t}` (after fixing the sign of `t`).
- **(I2) Busemann character.** `b(p) = beta_xi(p o, o)` is a continuous homomorphism `P -> R`, surjective, with
  kernel `MN`. Here `MN` is the stabilizer of the horosphere `h_0` through `o` centred at `xi`, and hence of every
  horosphere at `xi`. The identity `b(gh) = b(g) + b(h)` follows from `beta_{g xi} = beta_xi` for `g` in `P` and the
  cocycle identity of Busemann functions.
- **(I3)** Adams--Ballmann, *Amenable isometry groups of Hadamard spaces*, Math. Ann. 312 (1998): an amenable
  locally compact group acting continuously and properly by isometries on a proper Hadamard space fixes a point of
  the visual boundary or preserves a flat.
- **(I4)** Modular functions: if `L` is a closed normal subgroup of a locally compact group `H`, then for `h` in `H`,
  `Delta_H(h) = Delta_{H/L}(hL) * mod_L(c_h)`, where `c_h(l) = h l h^{-1}` and `mod_L` is the factor by which `c_h`
  scales Haar measure of `L` (Bourbaki, *Integration*, Ch. VII, §2).
- **(I5)** Hopf decomposition (Bevilacqua--Bowen `T:Kaim-Hopf` for countable groups, Krengel in general): `Con` is
  the maximal invariant set on which the action is conservative. A.e. point of a positive-measure subset `E` of
  `Con` returns to `E` along an unbounded (for countable `Gamma`: infinite) set of group elements.
- **(I6)** Quasi-centres in CAT(-1): there is `C_X` such that for pairwise distinct `a, b, c` in `dX` the set
  `Q(a,b,c)` of points within `C_X` of all three sides of the ideal triangle is nonempty and compact. It satisfies
  `Q(ga,gb,gc) = g Q(a,b,c)`.
- **(I7)** Borel density: a lattice `Gamma` in `G` fixes no point of `X`, no point of `dX`, and preserves no geodesic
  line.

Measurability of all maps below is routine: they are continuous or Borel functions of the anchors.

## Step 1: classification of closed amenable subgroups

Let `H <= G` be closed and amenable. By (I3), either `H` fixes some `xi` in `dX`, or `H` preserves a flat, which is a
point `p` or a line `ell` by (I1).
- If `H` fixes `p`, it lies in the compact stabilizer `K_p` and is compact: type (C).
- If `H` preserves a line, it is type (L).
- Otherwise `H <= P_xi`. If `b(H) = 0`, then `H <= MN_xi`: type (Hor). If `b(H) != 0`, the subgroup is focal,
  type (F).

## Step 2: unimodular focal subgroups are lineal

**Lemma 2.** Let `H <= P = P_xi` be closed and unimodular, with `b(H) != 0`. Then `H` preserves a geodesic line.

*Proof.*
- **(a) `a` is hyperbolic.** Pick `a` in `H` with `b(a) != 0`. Since `beta_xi(., o)` is 1-Lipschitz,
  `d(a^n o, o) >= |b(a^n)| = n |b(a)|`, so `tau(a) >= |b(a)| > 0` and `a` is hyperbolic. Its axis `ell` has `xi` as
  an endpoint, since `a` fixes `xi`. Conjugating inside `G`, assume `ell = ell_0`. Then `a` fixes `xi` and `eta`
  and translates `ell_0`, so `a = m_a a_t` with `m_a` in `M` and `t != 0` by (I1). Replacing `a` by `a^{-1}` if
  needed, `Ad(a_t)` contracts `Lie(N)`.
- **(b) Contraction modulo `M`.** For `x = m n` in `MN`, `a^j x a^{-j} = (m_a^j m m_a^{-j}) (a^j n a^{-j})`.
  - The first factor lies in `M`.
  - `m_a` acts isometrically on `Lie(N)` for an `M`-invariant norm, and `Ad(a_t)` contracts it, so
    `a^j n a^{-j} -> e` uniformly for `n` in compact subsets of `N`.
  - Hence for every compact `C <= MN` there is `j_0` with `a^j C a^{-j} <= W := M * exp(closed unit ball of
    Lie(N))` for all `j >= j_0`, and `W` is compact.
- **(c) `L = H ∩ MN` is compact.**
  - `L = ker(b|_H)` is a closed normal subgroup of `H`, and `H/L` is isomorphic as a group to `b(H) <= R`. So `H/L`
    is abelian and therefore unimodular.
  - `H` is unimodular, so (I4) gives `mod_L(c_a) = 1`: conjugation by `a` preserves the Haar measure `lambda_L`.
  - For every compact `C <= L`, (b) gives `a^j C a^{-j} <= L ∩ W` for large `j`. So
    `lambda_L(C) = lambda_L(a^j C a^{-j}) <= lambda_L(L ∩ W) < infinity`, and `L ∩ W` is compact because `L` is
    closed.
  - By inner regularity `lambda_L(L) < infinity`, so `L` is compact.
- **(d) The axis lies in the fixed set of `L`.**
  - The compact group `L` fixes a point of the CAT(0) space `X` (Cartan). So `Y = Fix(L)` is a nonempty closed
    convex set, and it is `H`-invariant because `L` is normal in `H`.
  - Let `pi_Y` be the nearest-point projection. It is 1-Lipschitz and commutes with `a`, since `aY = Y`. For `q` on
    `ell`: `d(a pi_Y(q), pi_Y(q)) = d(pi_Y(a q), pi_Y(q)) <= d(aq, q) = tau(a)`. So `pi_Y(q)` lies in
    `Min(a) = ell`.
  - Hence `ell ∩ Y` is nonempty, convex and `a`-invariant. Since `a` translates `ell` nontrivially, `ell ∩ Y = ell`,
    i.e. `ell <= Y`.
- **(e) `H` preserves `ell`.**
  - Let `h` be in `H`. Since `H/L` is abelian, `h a h^{-1} = l a` for some `l` in `L`.
  - `l` fixes `Y` pointwise, so `la` agrees with `a` on `Y`, and in particular translates `ell` by `tau(a)`.
  - `la = h a h^{-1}` is hyperbolic with `tau(la) = tau(a)`. So `ell <= Min(la)`, which is the unique axis of `la`
    by (I1), and that axis is `h ell`.
  - Therefore `h ell = ell`. QED.

**Corollary (Theorem A).** Every closed unimodular amenable subgroup of `G` is of type (C), (L) or (Hor).

## Step 3: equivariant compact sets force dissipation

**Lemma 3.** Let `Gamma <= G` be a closed subgroup and `(Z, mu)` a `Gamma`-space with invariant sigma-finite
measure. Let `E <= Z` be invariant, and let `Mid : E -> {nonempty compact subsets of X}` be measurable with
`Mid(gz) = g Mid(z)`. Then `E ∩ Con(Z)` is null.

*Proof.*
- Put `E_{R,S} = {z in E : Mid(z) meets B(o,R) and Mid(z) <= B(o,S)}`. These sets cover `E` as `R, S` run
  through the integers.
- For `z` in `E_{R,S}` and `g` with `gz` in `E_{R,S}`, some point `q` of `Mid(z)` has `d(gq, o) <= R`. Then
  `d(go, o) <= d(go, gq) + d(gq, o) <= S + R`.
- So the return set of `z` to `E_{R,S}` lies in `{g : d(go,o) <= R+S}`, which is relatively compact (finite if
  `Gamma` is discrete), because `G` acts properly on `X`.
- If `E ∩ Con` were not null, some `E_{R,S} ∩ Con` would have positive measure, and (I5) would give unbounded
  returns to it for a.e. of its points. That is a contradiction. QED.

## Step 4: the crossing parts

Fix a closed unimodular amenable `H`, with invariant Radon measure `m` on `G/H`, a smooth positive density. Let
`c : G/H -> Omega = G/S` be the anchor map, where `S` is the stabilizer of the anchor:
- `c(gH) = g p`, `S = K_p`, for (C);
- `c(gH) = g ell` in the space `Geod` of unoriented lines, `S = Stab(ell)`, for (L);
- `c(gH) = g xi` in `dX`, `S = P_xi`, for (Hor).

**Midpoint maps on `D = {(x,y) : c(x) != c(y)}`.**
- **(C)** `Mid(x,y) = {c(x)}`. Lemma 3 already makes all of `G/H` dissipative.
- **(L)** Let `F = ends(c(x)) ∪ ends(c(y))`, which has 3 or 4 points since the lines differ. Put
  `Mid(x,y) = union of Q(a,b,c) over the triples in F`, which is compact and nonempty by (I6).
- **(Hor)** Here `x = gH` determines the horosphere `h_x = g h_0` centred at `c(x)`, because `H <= MN` stabilizes
  `h_0`. For `c(x) != c(y)`, let `gamma` be the geodesic from `c(x)` to `c(y)`. Along it, `beta_{c(x)}` increases
  strictly (with unit speed), so `gamma` meets `h_x` in exactly one point `p`. Likewise `gamma` meets `h_y` in one
  point `q`. Put `Mid(x,y) = {midpoint of [p,q]}`. This is symmetric in `(x,y)` and equivariant.

In each case `Mid(gx, gy) = g Mid(x,y)`. So by Lemma 3, for every closed subgroup `Gamma <= G`,
`Con_Gamma((G/H)^2) <= {c(x) = c(y)}` modulo null sets.

**Null diagonal.**
- `c` is a `G`-equivariant smooth submersion, and its fibre over `g s_0` is `gS/H`, a closed submanifold of
  codimension `dim Omega`. That dimension is at least `dim dX >= 1` in all three cases.
- Hence each fibre is `m`-null, and by Fubini `m x m({c(x) = c(y)}) = ∫ m(c^{-1}(c(x))) dm(x) = 0`.

## Step 5: consequences

1. **Mellick's hypothesis fails.** Take `Gamma = G`. Then `Con_G((G/H)^2)` is null, so `G` does not act
   conservatively on `(G/H)^2`.
2. **Lattices are not PDR on `G/H`.** For a lattice `Gamma` (or any closed subgroup), the relation generated by
   `Con_Gamma((G/H)^2)` lies inside the equivalence relation `{c(x) = c(y)}`, which is `m x m`-null. So it is not
   conull, and `Gamma` acting on `G/H` is not PDR.
3. **Extensions.** Let `(Z, mu)` be an imp `Gamma`-space with a measurable equivariant `pi : Z -> G/H`. Put
   `kappa = c ∘ pi`.
   - Pulling back `Mid` along `pi x pi` and applying Lemma 3 gives `Con(Z^2) <= {kappa(z) = kappa(z')}`.
   - Suppose `Z` is PDR. Then this equivalence relation is conull. Let `mu'` be a probability measure equivalent to
     `mu` and `nu = kappa_* mu'`. Then `(mu' x mu')({kappa(z) = kappa(z')}) = sum over atoms of nu({omega})^2 = 1`.
     So `nu` is a Dirac mass at some `omega_0`.
   - `mu` is `Gamma`-invariant, so the class of `nu` is `Gamma`-invariant and `omega_0` is `Gamma`-fixed. By (I7),
     no lattice fixes a point of `X`, a point of `dX`, or a line. This is a contradiction.

   This covers finite-measure extensions, products with pmp actions, and every Maharam or Poisson-type
   construction that retains a map to `G/H`.

## Step 6: where rank one was used (calibration)

- In `SL(3,R)` with `H` the diagonal torus, Mellick's hypothesis holds. Step 2(e) fails there, because the minimal
  set of a regular semisimple element is a 2-flat. (I6) also fails: boundary data of two maximal flats in general
  position have no compact equivariant centre.
- Step 4 (Hor) uses that a geodesic from the centre of a horosphere meets it once. In higher rank a horosphere is
  replaced by a horocyclic subvariety that meets flats in positive-dimensional sets.
- Non-unimodular focal subgroups such as `A_0 N` escape Step 2 exactly at 2(c). Their `G/H` has no `G`-invariant
  measure, so the theorem is sharp for Mellick's setting.
- For lattices, Step 5.3 (with `pi = id`) covers every `Gamma`-invariant measure on `G/H` for unimodular `H`.
  - If `H` is cocompact in `P` (for example `A_0 N`), then `G/H` is compact, so a `Gamma`-invariant Radon measure
    on it is finite and pushes forward to a finite `Gamma`-invariant measure on `dX`. No such measure exists.
  - **Uniform lattices: no Radon measure for non-unimodular `H`.** Let `Gamma` be cocompact and `m` a
    `Gamma`-invariant Radon measure on `G/H`.
    - Define `M` on `G` by `M(f) = ∫_{G/H} ∫_H f(gh) d_l h dm(gH)`, with `d_l h` a left Haar measure. The inner
      integral is well defined on `G/H` by left invariance.
    - `M` is a left-`Gamma`-invariant Radon measure, and right translation by `h'` in `H` multiplies it by
      `Delta_H(h')^{±1}`.
    - `M` descends to a Radon measure on the compact space `Gamma\G`, which is finite and nonzero. Right translation
      is a homeomorphism, so it preserves the total mass. Hence `Delta_H = 1`.
    - So for uniform lattices (among them closed hyperbolic 3-manifold groups and cocompact `Sp(n,1)` lattices),
      every homogeneous `G/H` with a `Gamma`-invariant Radon measure has `H` unimodular, and Step 5.3 applies.
  - The remaining homogeneous case is non-uniform lattices, with `Gamma`-invariant Radon measures on `G/H` for
    non-unimodular focal `H` that are not cocompact in `P`, such as `A_0 N'` with `N'` a proper subgroup of `N`
    normalized by `A_0`. Here `Gamma\G` carries infinite `H`-relatively-invariant Radon measures, and this proof
    says nothing.
