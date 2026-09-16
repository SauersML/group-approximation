# Torsion-free router outputs need not be hyperbolic, and the free-group avatar router has no Kazhdan instance

Date: 2026-09-16.  Agent: swarm-internal-torsion-free-single-w.
Hole worked: `internal-torsion-free-single-word-router`.
Nodes supported: `torsion-free-router-forces-nonhyperbolic-output`,
`avatar-router-has-no-nontrivial-kazhdan-instance` and their proof routes.

## 0. Scope

The open claim `internal-torsion-free-single-word-router` asks for an
in-repository construction.  Its input is a finitely presented,
torsion-free, acylindrically hyperbolic group `E`, an element `d != 1`, and
a finite protected set `P` containing `d`.  Its output is a surjection
`q : E ->> Q` with `Q` nontrivial, two-generated, finitely presented,
torsion-free and acylindrically hyperbolic, with `q` injective on `P` and

```text
normalClosure_Q(q(d)) = Q.                                   (TFR3)
```

Call any such `q` a *valid output* for `(E, d, P)`.

This artifact does not construct a router and does not refute the claim.
It proves limits on the architectures that could construct one:

* **Theorem A** (Section 3).  Suppose `E` contains `x` with
  `x d x^-1 = d^m` for some `|m| >= 2`.  Then every valid output contains a
  copy of `BS(1,m)`, so it is not word-hyperbolic.  In particular it has no
  finite classical `C'(1/6)` presentation without proper-power relators, for
  any finite generating set and any choice of `q`.  The test instance
  `E_1 = <a,t,s | a t a^-1 = t^2>`, with `d = t` and `P = {t}`, satisfies
  every input hypothesis (Section 2).  So any architecture that always
  outputs a classical free-group `C'(1/6)` quotient fails on `E_1`, and so
  does any architecture that always outputs a hyperbolic group.  The
  classical free-product regime, in which the factor `E` embeds in `Q` and
  `q` is the factor map, also fails on `E_1`.
* **Theorem A'** (Section 4).  If `d` lies in `Rad_MF(E)`, then no valid
  output is residually finite, so none is a classical `C'(1/6)` group.  A
  word-hyperbolic valid output would be a non-MF hyperbolic group, which
  would settle the open claim `non-mf-hyperbolic-group`.
* **Theorem B** (Section 5).  Every homomorphism from a group with property
  (T) to a group given by a finite classical `C'(1/6)` presentation without
  proper-power relators is trivial.  So the route `free-group-avatar-router`
  has no instance: it asks for a surjection from a Kazhdan partner `B` onto
  exactly such a presentation, together with a surviving protected element
  `s != 1`.

## 1. Baumslag--Solitar groups and the embedding lemma

Fix an integer `m` with `|m| >= 2`.  Let
`BS(1,m) = <a, t | a t a^-1 = t^m>`, and let
`A_m = Z[1/|m|]` be the additive group of rationals whose denominators are
powers of `|m|`.  Let `Z` act on `A_m` by `k . r = m^k r`; this is an
automorphism because `m` is a unit in `Z[1/|m|]`.  Put

```text
G_m = A_m x| Z,        (r, k)(r', k') = (r + m^k r', k + k').
```

The identity is `(0, 0)` and `(r, k)^-1 = (-m^-k r, -k)`.

**Lemma 1.0 (model).**  The assignment `t -> (1, 0)`, `a -> (0, 1)` extends
to an isomorphism `phi : BS(1,m) -> G_m`.

*Proof.*  Compute `(0,1)(1,0)(0,-1) = (m, 1)(0, -1) = (m, 0)`.  This is
`(1,0)^m`, so `phi` is a well-defined homomorphism.

*Surjectivity.*  First, `phi(a^-j t^n a^j) = (0,-j)(n,0)(0,j) = (m^-j n, 0)`.
Every element of `A_m` has the form `m^-j n` with `j >= 0`, so the image
contains `A_m x 0`.  It also contains `(0,1)`, so it is all of `G_m`.

*Injectivity.*  Let `W` be the set of elements of `BS(1,m)` that can be
written `a^-j t^n a^k` with `j >= 0`, `n` in `Z` and `k` in `Z`.  Then
`1` is in `W`, and `W` is closed under right multiplication by `a^+-1`.
It is also closed under right multiplication by `t^+-1`, in two cases:

* if `k >= 0`, then `a^k t^+-1 = t^(+-m^k) a^k`, which gives
  `a^-j t^n a^k t^+-1 = a^-j t^(n +- m^k) a^k`;
* if `k < 0`, then `a^-j t^n a^k = a^-(j-k) (a^-k t^n a^k) = a^-(j-k) t^(n m^-k)`,
  whose exponent of `a` on the right is `0`, so the first case applies.

Hence `W = BS(1,m)`.  Now `phi(a^-j t^n a^k) = (m^-j n, k - j)`.  If this is
the identity, then `k = j` and `n = 0`, so the element is `a^-j a^j = 1`.
Hence `phi` is injective. `[]`

**Lemma 1.1 (embedding lemma).**  Let `H` be any group and let
`f : BS(1,m) -> H` be a homomorphism such that `f(t)` has infinite order.
Then `f` is injective.

*Proof.*  Identify `BS(1,m)` with `G_m`, and let `K = ker f`, a normal
subgroup.

*Step 1: `K` meets `A_m x 0` trivially.*  Suppose `(r, 0)` is in `K` with
`r = n m^-j != 0`, `n` in `Z`, `j >= 0`.  Conjugate by `(0, j)`:

```text
(0,j)(r,0)(0,-j) = (m^j r, 0) = (n, 0) = t^n.
```

So `t^n` is in `K` with `n != 0`.  Then `f(t)^n = 1`, which contradicts
infinite order.

*Step 2: `K` is trivial.*  Let `x = (r, k)` be in `K`.  Since `K` is
normal, `x t x^-1 t^-1` is in `K`.  Compute

```text
(r,k)(1,0) = (r + m^k, k),
(r + m^k, k)(-m^-k r, -k) = (r + m^k - r, 0) = (m^k, 0),
x t x^-1 t^-1 = (m^k - 1, 0).
```

If `k != 0`, then `m^k != 1` because `|m| >= 2`, so `(m^k - 1, 0)` is a
nonzero element of `K`.  This contradicts Step 1.  Hence `k = 0`, so `x`
lies in `A_m x 0`, and Step 1 gives `x = 1`. `[]`

**Corollary 1.2.**  Let `H` be a group, and let `u, g` in `H` satisfy
`u g u^-1 = g^m` with `|m| >= 2`, where `g` has infinite order.  Then
`<u, g>` is isomorphic to `BS(1,m)` through `a -> u`, `t -> g`.
If `H` is torsion-free, `g != 1` is enough.

*Proof.*  The relation holds, so `a -> u`, `t -> g` defines a homomorphism
`f : BS(1,m) -> H` with image `<u,g>`.  Lemma 1.1 shows `f` is injective.
In a torsion-free group every nonidentity element has infinite order. `[]`

**Fact H (imported, not re-derived).**  A word-hyperbolic group contains no
subgroup isomorphic to `BS(1,m)` with `|m| >= 2`.

Here is the standard reason.  In a word-hyperbolic group `Gamma` with a
finite generating set, every infinite-order element `g` is undistorted:
there is `c > 0` with `|g^n| >= c|n|` for all `n`.  If `u g u^-1 = g^m`,
then `g^(m^k) = u^k g u^-k`, so

```text
c |m|^k <= |g^(m^k)| <= 2k|u| + |g|    for all k >= 1,
```

which is impossible as `k -> infinity`.  The undistortedness input is
classical (Gromov; Bridson--Haefliger, Part III.Gamma; Ghys--de la Harpe,
Ch. 8) and was not re-read in this session.

The statement itself was checked on 2026-09-16 on Wikipedia, *Hyperbolic
group*: "The Baumslag–Solitar groups B(m,n) and any group that contains a
subgroup isomorphic to some B(m,n) fail to be hyperbolic (since B(1,1) =
Z², this generalizes the previous example)."  On that page, the neighbouring
sentence about `Z^2` carries citations [4][5], namely Bridson--Haefliger and
Ghys--de la Harpe.  This is the one imported group-geometric fact behind
Theorem A, and it is the step to attack first.  The graph already uses the
`Z^2` case inline, in `lattice-forced-torsion-dies-in-hyperbolic-quotients-proof`.

## 2. The test instance E_1

Let

```text
E_1 = <a, t, s | a t a^-1 = t^2>,       d = t,       P = {t}.
```

**2.1 Finite presentation.**  Three generators and one relator.

**2.2 Torsion-free.**  `E_1` is the HNN extension of the free group
`F(t, s)` with stable letter `a`, associating `<t>` to `<t^2>` by
`t -> t^2`.  The base is free, hence torsion-free.  By the established
claim `hnn-torsion-theorem`, `E_1` is torsion-free.

**2.3 `BS(1,2)` embeds in `E_1`.**  The map `rho : E_1 -> BS(1,2)` with
`a -> a`, `t -> t`, `s -> 1` respects the relator.  So does the map
`iota : BS(1,2) -> E_1` with `a -> a`, `t -> t`.  Since `rho iota = id`,
`iota` is injective.  Also `E_1 = BS(1,2) * <s>` by Tietze moves.  Sections 3
and 4 do not use this embedding; it only illustrates that `E_1` is not
hyperbolic.

**2.4 `d != 1`.**  Here `rho(t) = t != 1` in `BS(1,2)`, by Lemma 1.0.

**2.5 Acylindrical hyperbolicity.**  Write `G = E_1 = A * B` with
`A = BS(1,2)` and `B = <s> = Z`.  Let `T` be the Bass--Serre tree of this
free product:

* the vertices are the cosets `gA` and `gB`;
* the edges are the elements `g` of `G`, where the edge `g` joins `gA` to
  `gB`;
* `G` acts by left multiplication.

This action has no inversions (it preserves the bipartition), the edge
stabilizers are trivial, and the vertex stabilizers are the conjugates of
`A` and `B`.  That `T` is a tree is the normal form theorem for free
products (Serre, *Trees*, Chapter I; not re-read in this session).  We use `T` with its path metric, in which
every edge has length 1.

*(i) Acylindricity.*  Fix `eps > 0`.  Put `R = 2 eps + 6` and
`N = 2 eps + 4`.  Let `x, y` be points of `T` with `d(x, y) >= R`, and let
`g` satisfy `d(x, gx) <= eps` and `d(y, gy) <= eps`.

* Let `mu` be the midpoint of `[x, y]`.  Trees are CAT(0), and in a CAT(0)
  space `d(mu, g mu) <= (d(x,gx) + d(y,gy))/2 <= eps`.
* In a tree, `[gx, gy]` is contained in `[gx, x] u [x, y] u [y, gy]`.  If a
  point `p` of `[gx, gy]` lies on `[gx, x]`, then `d(gx, p) <= d(gx, x) <= eps`.
  The same holds at the `y` end.  Hence every point of `[gx, gy]` at
  distance more than `eps` from both `gx` and `gy` lies on `[x, y]`.
* Choose an edge `e` of `[x, y]` that contains `mu` or has `mu` as an
  endpoint.  Then `ge` is an edge of `[gx, gy]` containing `g mu`.  Every
  point of `ge` is at distance at least `R/2 - 1 > eps` from `gx` and `gy`,
  so `ge` lies on `[x, y]`.  It is also within distance `eps + 1` of `mu`.
* Hence `ge` is one of at most `2 eps + 4` edges of `[x, y]`.
* Since edge stabilizers are trivial, `g` is determined by the edge `ge`.

So at most `N` elements `g` qualify, and the action is acylindrical.

*(ii) A loxodromic element.*  The element `ts` has syllable length 2 and is
cyclically reduced in `A * B`.  By the normal form theorem it is not
conjugate into `A` or `B`, so it fixes no vertex.  An automorphism of a tree
without inversions that fixes no vertex is hyperbolic: it translates along
an axis by a positive integer (Tits; Serre, *Trees*, Chapter I, §6; not
re-read).  So the orbits are
unbounded.

*(iii) Not virtually cyclic.*  The elements `a` (in `A`, infinite order) and
`s` generate `<a> * <s>`, a free group of rank two.  This uses the normal
form theorem for subgroups generated by elements of distinct factors.

*(iv) Conclusion.*  Osin's trichotomy (arXiv:1304.1246, Theorem 1.1, as
quoted in `notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md` §6.8)
says that a group acting acylindrically on a hyperbolic space either has
bounded orbits, or is virtually cyclic with a loxodromic element, or is
acylindrically hyperbolic.  By (i)--(iii), `E_1` is acylindrically
hyperbolic.

So `(E_1, t, {t})` is a legitimate input for the target claim.  More
generally, any finitely presented, torsion-free, acylindrically hyperbolic
group containing `BS(1,m)` with `|m| >= 2` (for example `BS(1,m) * Z`)
gives an input to which Theorem A applies, with `d` the image of `t`.

## 3. Theorem A: every valid output contains BS(1,2)

**Theorem A.**  Let `(E, d, P)` be an input for the target.  Suppose
`x d x^-1 = d^m` for some `x` in `E` and some `|m| >= 2`.  Let
`q : E ->> Q` be a valid output.  Then:

* **(a)** the map `a -> q(x)`, `t -> q(d)` is an isomorphism from
  `BS(1,m)` onto `<q(x), q(d)>`;
* **(b)** `Q` is not word-hyperbolic;
* **(c)** `Q` has no finite classical `C'(1/6)` presentation without a
  proper-power relator, over any finite generating set;
* **(d)** suppose `Q = (E * H)/<<R>>` for some group `H` and some set `R`,
  the composite `E -> E * H -> Q` is injective ("factor embedding"), and `q`
  is this composite.  Then `q` is an isomorphism, so `E` is two-generated and
  `normalClosure_E(d) = E`.

In particular, for `(E_1, t, {t})`:

* every valid output contains `BS(1,2)` and is not word-hyperbolic;
* no valid output is a classical free-group `C'(1/6)` quotient without
  proper powers;
* no valid output comes from a factor-embedding free-product regime with `q`
  the factor map, because `E_1/<<t>> = <a, s | > = F_2 != 1`.

*Proof.*  (a)  First, `q(d) != 1`: otherwise its normal closure is trivial,
and (TFR3) gives `Q = 1`, which contradicts the output requirement that `Q`
be nontrivial.  Since `Q` is torsion-free, `q(d)` has infinite order.
Applying `q` to `x d x^-1 = d^m` gives `q(x) q(d) q(x)^-1 = q(d)^m`.
Corollary 1.2 applies.

(b)  By (a), `Q` contains `BS(1,m)` with `|m| >= 2`.  Apply Fact H.

(c)  By the established claim
`cprime-one-sixth-presentations-hyperbolic-and-torsion-free`, such a
presentation defines a word-hyperbolic group.  Word-hyperbolicity does not
depend on the finite generating set.  This contradicts (b).

(d)  `q` is injective by hypothesis and surjective because it is a valid
output.  So it is an isomorphism.  Pulling back (TFR3) gives
`normalClosure_E(d) = E`, and two-generation of `Q` transfers to `E`.  For
`E_1`, adding the relator `t` turns `a t a^-1 = t^2` into the trivial
relation, so `E_1/<<t>>` is free on `a, s` and is nontrivial.  Hence
`normalClosure_{E_1}(t) != E_1`. `[]`

**Reading for the router program.**  The target explicitly accepts "a direct
formalization of the needed normal-form/Greendlinger argument".  The graph
records two elementary Greendlinger regimes.

1. **Classical free-group `C'(1/6)`**, the regime of `GreendlingerGate` in
   `SmallCancellationRouter.lean`, used by `free-group-avatar-router`.
   There, torsion-freeness comes from the "no proper-power relator" clause.
   By Theorem A(c), no construction that always outputs such a presentation
   can prove the target: it fails on `(E_1, t, {t})`.  The conclusion does
   not depend on how the avatars, tying relators or protected-ball margins
   are chosen.
2. **Classical free-product syllable `C'(1/6)` over `E * H`.**  Here the
   repository's consequence layer derives factor embedding from the
   Greendlinger length bound (see
   `free-product-router-factor-embedding-obstruction`).  With `q` the factor
   map, Theorem A(d) kills it on `(E_1, t, {t})`, and indeed on every input
   with `normalClosure_E(d) != E`.  This is the partner-free analogue of that
   obstruction node's argument.

More broadly, Theorem A(b) rules out every architecture whose outputs are
always word-hyperbolic: graphical small cancellation over free groups,
hyperbolic Dehn filling with hyperbolic output, and so on.  An internal
proof must produce a quotient in which a Baumslag--Solitar subgroup (or, for
other inputs, whatever non-hyperbolic subgroups the protected data force)
survives.  In other words, it must formalize small cancellation *relative
to* a non-hyperbolic ambient structure, as Hull's theory over
acylindrically hyperbolic groups does.

This is consistent with the paper-level router
`two-generated-single-element-hull-router`, whose outputs are only
acylindrically hyperbolic (`hull-quotients-are-not-word-hyperbolic`).
Applied with `A = B = E_1` and `u = t`, it would supply valid outputs for
`(E_1, t, {t})` at paper level.  So Theorem A obstructs architectures; it
does not refute the target.

## 4. MF-radical inputs

Both consumer lanes of the target feed it a word in the MF radical:

* `property-t-free-torsion-free-via-intrinsic-seed`, through
  `torsion-free-fp-ah-mf-radical-seed`;
* `property-t-free-torsion-free-via-bs-radical-tether`, through the tethered
  group `A = <E, t | d t d^-1 = t^2>`.

**Theorem A'.**  Let `(E, d, P)` be an input with `d` in `Rad_MF(E)`, and
let `q : E ->> Q` be a valid output.  Then:

* **(a)** `Rad_MF(Q) = Q`;
* **(b)** `Q` is not MF;
* **(c)** `Q` is not residually finite;
* **(d)** `Q` has no finite classical `C'(1/6)` presentation without a
  proper-power relator;
* **(e)** if `Q` were word-hyperbolic, it would witness the open claim
  `non-mf-hyperbolic-group`.

*Proof.*  (a)  As in Theorem A(a), `q(d) != 1`.  So `q` satisfies (TFR1)
of the established claim `torsion-free-mf-radical-routing-saturation`, and
(TFR2) is the conclusion.

(b)  By `universal-mf-quotient`, a countable group is MF exactly when its MF
radical is trivial.  `Q` is two-generated, hence countable, and
`Rad_MF(Q) = Q != 1`.

(c)  By `central-quotients-of-residually-finite-groups-are-mf` with trivial
central subgroup, every countable residually finite group is MF.  Apply (b).

(d)  By `hyperbolic-cubulated-groups-are-residually-finite` (Wise's
cubulation of finite classical `C'(1/6)` presentations together with Agol
and Haglund--Wise), such a group is residually finite.  Apply (c).

(e)  Combine (b) with the hypothesis. `[]`

Theorem A' needs no Baumslag--Solitar subgroup, and it applies to every
consumer instance.  It does not say whether consumer instances exist; that
is the open seed hole.

In the tether lane the relation `q(d) q(t) q(d)^-1 = q(t)^2` holds in `Q`.
Whenever `q(t) != 1` (for instance when the protected set contains `1` and
`t`), Corollary 1.2 puts `BS(1,2)` inside `Q`, and Theorem A(b) applies as
well.

## 5. Theorem B: Kazhdan groups map trivially to classical C'(1/6) groups

**Theorem B.**  Let `N` be a group with Kazhdan's property (T).  Let `Q` be
given by a finite classical `C'(1/6)` presentation without a proper-power
relator.  Then every homomorphism `psi : N -> Q` is trivial.  In particular,
if `psi` is surjective then `Q = 1`.

*Proof.*

1. By the established claim `hyperbolic-cubulated-groups-are-residually-finite`,
   whose citation route `hyperbolic-cubulated-rf-citation` quotes Wise,
   *Cubulating small cancellation groups*, GAFA 14 (2004), `Q` acts properly
   and cocompactly on a CAT(0) cube complex `X`.  As usual, the action is by
   combinatorial automorphisms, so it is cellular.
2. For a cellular action on a cube complex, cocompactness means that there
   are finitely many `Q`-orbits of cubes, i.e. `X/Q` is a finite complex.  So
   the cube dimensions are bounded and `dim X < infinity`.  This reading of
   "cocompact" is the combinatorial one used for cubulations; it is part of
   the trust surface in §7.
3. Through `psi`, the group `N` acts cellularly on the finite-dimensional
   CAT(0) cube complex `X`.  By
   `niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes` (Niblo--Reeves,
   G&T 1 (1997), Theorem B, verbatim in
   `niblo-reeves-kazhdan-fixed-point-citation`), the action has a global
   fixed point `p`.
4. Let `C` be the unique cube containing `p` in its relative interior.  Then
   `psi(N)` lies in the setwise stabilizer of `C`.  Properness makes
   `{g in Q : gC meets C}` finite, so `psi(N)` is finite.
5. By `cprime-one-sixth-presentations-hyperbolic-and-torsion-free`, `Q` is
   torsion-free.  So its only finite subgroup is trivial, and `psi(N) = 1`.
   `[]`

There is an independent check.  `cubulated-hyperbolic-groups-are-virtually-special`
makes `Q` virtually compact special, and `Q` is torsion-free.  The
established claim `kazhdan-groups-map-trivially-to-torsion-free-special-groups`
then gives the same conclusion.

**Corollary B1 (the avatar router has no instance).**  The route
`free-group-avatar-router` (target `bespoke-routing-lemma`) asks for five
things together:

* `B` a finitely presented, torsion-free Kazhdan partner;
* `Q = F(y_1, y_2)/<<R>>` with `R` finite, satisfying whole-family metric
  `C'(1/6)` after symmetrization, with no proper-power relator (so that
  torsion-freeness follows);
* tying relators `y_j (word in the U_k)^-1`, which make `psi : B -> Q`
  surjective (clause 3 of that node: "so psi is onto and (T) descends");
* `q : E ->> Q`;
* a protected element `s != 1` with `q(s) != 1`.

By Theorem B, surjectivity of `psi` forces `Q = 1`, so `q(s) = 1`.  So no
choice of avatar words, piece ledger or length margins satisfies the route,
and it is invalidated.

This invalidates only the route.  The claim `bespoke-routing-lemma` is
neither refuted nor unestablished by it, because it keeps its other recorded
route, `small-cancellation-router-spec-proof`.  Theorem B also leaves room
for Kazhdan quotients that are not classical `C'(1/6)` groups.  Torsion-free
hyperbolic Kazhdan groups exist (`arzhantseva-steenbock-kazhdan-groups-without-unique-products`),
and Hull-type outputs are acylindrically hyperbolic.

**Remark B2.**  By the same proof, the conclusion holds for any hyperbolic
group that acts properly and cocompactly on a CAT(0) cube complex and is
torsion-free.  The claim `hyperbolic-cubulated-groups-are-residually-finite`
also lists finite `C'(1/4)-T(4)` presentations giving hyperbolic groups.
Theorem B is stated only for the classical `C'(1/6)` case, which is the one
the avatar route uses.

## 6. What this does not do

* **It does not refute `internal-torsion-free-single-word-router`.**  For
  `(E_1, t, {t})`, the paper-level router supplies non-hyperbolic valid
  outputs.
* **It does not exclude every free-product architecture.**  Theorem A(d)
  covers only the case where `q` is the factor map.  Consider a quotient
  `Q = (E * H)/<<R>>` in which the factor `E` embeds and `q : E ->> Q` is a
  *different* surjection, for example an avatar map.  Theorem A does not rule
  this out: `Q` still contains a copy of `E`, so non-hyperbolicity is no
  obstacle.  Such a `q` would have to be a surjection from `E` onto a group
  containing `E`.
* **It does not exclude relative small cancellation.**  This includes Hull's
  theory, and generally any theory over a non-hyperbolic ambient group with
  a hyperbolically embedded family.  Theorem A says that is where an internal
  router has to live.
* **It says nothing about hyperbolic Kazhdan quotients that are not classical
  `C'(1/6)`**, for the Kazhdan lane.
* **It does not decide whether MF-radical inputs exist**, which is the seed
  hole.
* **It does not audit `small-cancellation-router-spec-proof` or any Lean
  file.**

## 7. Literature and trust surface

**Established graph claims consumed** (as nodes; not re-derived here):

* `cprime-one-sixth-presentations-hyperbolic-and-torsion-free`: Gruber,
  arXiv:1210.0178, quoted in its citation route;
* `hyperbolic-cubulated-groups-are-residually-finite`: Wise GAFA 14 (2004),
  Agol Doc. Math. 18 (2013), Haglund--Wise GAFA 17 (2008), quoted in
  `hyperbolic-cubulated-rf-citation`;
* `niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes`: Niblo--Reeves,
  G&T 1 (1997), Theorem B, verbatim;
* `hnn-torsion-theorem`: machine-checked;
* `torsion-free-mf-radical-routing-saturation`, `universal-mf-quotient` and
  `central-quotients-of-residually-finite-groups-are-mf`.

**Inline imports, not re-read this session:**

* **Fact H.**  Hyperbolic groups contain no `BS(1,m)` with `|m| >= 2`.  The
  statement was checked verbatim on Wikipedia, *Hyperbolic group*, fetched
  2026-09-16.  The classical sources are Gromov 1987 and Bridson--Haefliger
  1999, Part III.Gamma, on undistorted infinite cyclic subgroups, and
  Ghys--de la Harpe 1990, Ch. 8.
* **Bass--Serre theory of free products** and the fixed-vertex/axis
  dichotomy for tree automorphisms without inversions (Serre, *Trees*,
  Ch. I).
* **CAT(0) convexity of the metric** (Bridson--Haefliger, Part II.2).
* **Osin's trichotomy**, arXiv:1304.1246 (v1 2013-04-04), Theorem 1.1, as
  quoted through Hull arXiv:1308.4345, Theorem 2.3, in
  `notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md` §6.8.  This is used
  only to certify that `E_1` is acylindrically hyperbolic.  Any other
  certificate would do, and Theorem A(a)--(c) do not use acylindrical
  hyperbolicity at all.

**Weakest steps, in order:**

1. Fact H is imported inline, not through a graph node.
2. Step 1 of Theorem B uses the reading "acts properly and cocompactly on a
   CAT(0) cube complex" by combinatorial automorphisms, which is the
   convention in Wise's theorem.
3. The acylindricity constants in §2.5 matter only for the legitimacy of the
   test instance.

**Computational sanity check.**  The script
`experiments/torsion-free-router-nonhyperbolic-output-2026-09-16/bs_model_check.py`
checks the identities of Section 1 with exact rationals, for
`m in {2, 3, -2, -3}`:

* the relator maps to the identity;
* on 2000 random words per `m`, the rewriting to `a^-j t^n a^k` agrees with
  the model image;
* the commutator and conjugation formulas of Lemma 1.1 hold on random
  elements.

It confirms the algebra; it proves nothing beyond it.

**Recency sweep.**  No 2024--2026 literature sweep was possible in this
session: the WebSearch budget was exhausted and the arXiv export API
returned HTTP 429.  So no claim is made that the obstructions above are new
in the literature.  Theorem B in particular is a direct combination of
standard theorems and is presumably folklore.  Its contribution here is to
invalidate a recorded route.
