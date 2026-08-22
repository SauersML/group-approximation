# The coset wreath algebra has a Cartan masa, so hyperlinearity forces strong 1-boundedness

Date: 2026-08-22.  Companion derivation for the nodes
`coset-bernoulli-action-is-essentially-free`,
`coset-wreath-algebra-has-a-lamp-cartan`,
`cartan-algebras-are-strongly-one-bounded`,
`coset-wreath-hyperlinearity-forces-strong-one-boundedness`,
`coset-wreath-microstates-carry-excess-entropy`,
`nonhyperlinear-from-lamp-torsor-excess`.

Throughout:

```text
Lambda = SL_3(Z),  Gamma = SL_3(Z[1/3]),  I = Gamma/Lambda,
W_3 = ( direct_sum_I C_2 ) rtimes Gamma          (the summit wreath, node CW3),
X = {-1, 1}^I with the Bernoulli(1/2) product measure mu,
L(W_3) = L^infinity(X) rtimes Gamma  with the canonical trace.
```

The identification `L(direct_sum_I C_2) = L^infinity(X)` is the Fourier
transform of the lamp group; it is `Gamma`-equivariant and carries the
counting trace to `mu`, so `L(W_3)` with its canonical group trace is the
crossed product of the generalized Bernoulli action by the coset action.

## Theorem 1 (essential freeness)

Every `g != 1` in `Gamma` moves infinitely many cosets in `I`.
Consequently the generalized Bernoulli action `Gamma acts X` is
essentially free: the stabilizer of `mu`-almost every `omega in X` is
trivial.

**Step 0: the center is trivial.**  `Z(SL_3(Z[1/3])) = mu_3(Z[1/3]) = 1`
(a primitive cube root of unity is not in `Q`), so no nontrivial element
acts trivially on `I` for that trivial reason; the theorem asserts more,
namely that no nontrivial element even fixes a cofinite set of cosets.

**Step 1: `I` is the type-0 vertex set of the building.**  Let `X_3` be
the Bruhat–Tits building of `SL_3(Q_3)`, a two-dimensional CAT(0)
simplicial complex, with base vertex `v_0` the class of the standard
lattice `Z_3^3`.  The stabilizer of `v_0` in `SL_3(Q_3)` is
`SL_3(Z_3)`: if `g Z_3^3 = c Z_3^3` with `det g = 1` then
`3 val(c) = 0`, so `g in GL_3(Z_3) cap SL_3 = SL_3(Z_3)`.  Hence

```text
Stab_Gamma(v_0) = Gamma cap SL_3(Z_3) = SL_3(Z[1/3] cap Z_3) = SL_3(Z) = Lambda.
```

By strong approximation `Gamma` is dense in `SL_3(Q_3)`; since
`SL_3(Z_3)` is open, density gives transitivity of `Gamma` on the
`SL_3(Q_3)`-orbit of `v_0`, which is the set of type-0 vertices.  So
`I = Gamma/Lambda` is `Gamma`-equivariantly the set of type-0 vertices
of `X_3`.

**Step 2: an element fixing cofinitely many type-0 vertices is trivial.**
Suppose `g in Gamma` fixes every type-0 vertex outside a ball `B`.
`Fix(g)` is a closed convex subset of the CAT(0) space `X_3` (fixed sets
of isometries are convex).  Let `A` be any apartment.  The type-0
vertices of `A` form an orbit of the coroot-lattice translations, a
cocompact rank-2 lattice orbit `L_0 subset A ~ R^2`.  Given any point
`x in A`, choose three points of `L_0` at distance `R' >> radius(B) + |x|`
from `x` in directions roughly 120 degrees apart; they lie outside `B`,
so they are fixed, and their Euclidean triangle contains `x`.  Apartments
are convex in `X_3` and geodesics between points of `A` stay in `A`, so
the CAT(0) convex hull of the three vertices is their Euclidean triangle.
Convexity of `Fix(g)` gives `x in Fix(g)`.  Hence `Fix(g) supseteq A`
for every apartment, i.e. `Fix(g) = X_3`.  The kernel of the action of
`SL_3(Q_3)` on its building is the center `mu_3(Q_3)`, and `x^2+x+1`
has no root in `Q_3` (its discriminant `-3` has odd valuation), so the
kernel is trivial and `g = 1`.

(For the `SL_2(Z[1/p])` pair the same argument runs on the
`(p+1)`-regular tree: an isometry fixing all even vertices outside a
ball fixes, for every vertex `x`, two far-apart even vertices on a line
through `x`, hence fixes `x`; the kernel of the tree action is the
center `{+-1}`, so the action is essentially free modulo center.)

**Step 3: measure of the fixed-point set.**  Fix `g != 1` and let
`x_1, x_2, ...` be infinitely many cosets moved by `g` (Step 2).  Choose
inductively infinitely many pairwise disjoint nontrivial
`<g>`-orbits `O_1, ..., O_k, ...` in `I` (each moved point lies in a
nontrivial orbit; discard the finitely many orbits already used).  A
configuration fixed by `g` must be constant on each `O_j`; for an orbit
of size `m >= 2` (infinite orbits: intersect with a finite window) the
constancy event has probability `<= 1/2`, and the events for disjoint
orbits are independent.  So `mu(Fix_X(g)) <= 2^(-k)` for every `k`,
hence `= 0`.  A countable union over `g != 1` finishes: almost every
stabilizer is trivial.  QED.

## Theorem 2 (ergodicity, factoriality, Cartan)

The action `Gamma acts (X, mu)` is ergodic; `L(W_3) = L^infinity(X)
rtimes Gamma` is a II_1 factor and `L^infinity(X)` is a Cartan
subalgebra (maximal abelian, regular, with a faithful normal
conditional expectation given by the trace).

*Ergodicity.*  `L^2(X) = direct_sum_F C w_F` over finite subsets
`F subset I` (Fourier–Walsh basis), and `Gamma` permutes the basis by
`F -> gF`.  Every nonempty finite `F` has an infinite orbit: otherwise a
finite-index subgroup of `Gamma` stabilizes `F` setwise and a further
finite-index subgroup fixes some `x in F`, contradicting
`[Gamma : Stab(x)] = [Gamma : Lambda] = infinity`.  An invariant
`ell^2` vector has coefficients constant on orbits, hence supported on
`F = emptyset`.  So invariant vectors are constants.

*Cartan.*  Essential freeness (Theorem 1) makes `L^infinity(X)` maximal
abelian in the crossed product; it is visibly regular (normalized by the
unitaries `u_gamma` and by its own unitaries, which together generate);
ergodicity plus freeness makes the crossed product a factor, of type
II_1 since the action preserves the probability measure `mu` and the
trace is `tau = integral compose E`.  These are the standard
Murray–von Neumann / Feldman–Moore facts for free ergodic p.m.p.
actions.  QED.

## Theorem 3 (hyperlinearity forces strong 1-boundedness)

Unconditionally `h(L(W_3)) <= 0`, where `h` is Hayes' 1-bounded entropy.
Hence: if `W_3` is hyperlinear (equivalently `L(W_3)` is Connes
embeddable, the trace being canonical), then `L(W_3)` is strongly
1-bounded, `h(L(W_3)) = 0`, and every finite generating tuple of
`L(W_3)` has microstate free entropy dimension `delta_0 <= 1`.

*Proof.*  `A = L^infinity(X)` is a diffuse hyperfinite (abelian)
subalgebra with `h(A) = 0`, and `L(W_3) = W^*(N(A))` by Theorem 2
(regularity).  Hayes' 1-bounded entropy is monotone under
(wq-)normalizing generation: `h(M) <= h(A)` whenever `A <= M` is diffuse
and `M` is generated by the normalizer of `A` (Hayes, *1-bounded entropy
and regularity problems in von Neumann algebras*, IMRN 2018,
arXiv:1505.06682, which abstracts Voiculescu's absence-of-Cartan
argument; the Cartan case is already in Jung, *Strongly 1-bounded von
Neumann algebras*, GAFA 17 (2007) 1180–1200, arXiv:math/0510576, whose
example list explicitly includes II_1 factors with Cartan subalgebras,
and Voiculescu GAFA 1996 for `delta_0 <= 1`).  If `L(W_3)` is Connes
embeddable then microstates exist and `h >= 0`, so `h = 0`, which is
strong 1-boundedness; Jung's theorem then bounds `delta_0` of every
generating tuple by 1.  QED.

**Quantitative reading (the rigidity of the enemy).**  `h(L(W_3)) <= 0`
says: for a fixed generating tuple of `W_3`, the space of its matricial
microstates at precision epsilon in `M_d`, taken modulo unitary
conjugation, admits epsilon-nets of cardinality
`exp(o(d^2) . log(1/epsilon))` — there are NO macroscopic
(`c . d^2`-parameter) families of pairwise non-conjugate models.  Every
hyperlinear model of `W_3` — in particular every enemy configuration
(almost-representation of `Gamma` + equivariant commuting lamp family
`k_x in pi(Stab x)'` with Bernoulli mixed moments) — is, at every scale,
essentially unique modulo conjugation and lower-order corrections.

## Consequences and the new attack surface

1. **The moduli flip.**  The `Lambda`-exact-face campaign
   (`lambda-exact-face-of-the-collapse-closes`,
   `two-power-sector-conjugator-dichotomy`) keeps finding that would-be
   enemy constructions carry torsors: Weyl-cohomological selections,
   in-band automorphisms, congruence-commutant freedom of dimension
   `c_m d^2` at fixed congruence level `m`.  Theorem 3 turns any such
   freedom, IF it survives the constraints and the conjugation quotient
   at scale `c d^2`, into a refutation: excess moduli mean
   `h(L(W_3)) > 0`, contradicting the Cartan bound, so `W_3` would be
   non-hyperlinear.  A successful "hyperlinear-side" construction must
   therefore be RIGID; the constructive probe (the p = 2 flat tower) is
   two-sided in a sharper way than the fork previously recorded.
2. **Scope of Kun–Thom Corollary D, and an incompressibility fence.**
   Cor. D (`coordinate-action-not-sofic`) forbids permutation/Cartan-
   compatible approximations of the coset action FOR THE KUN–THOM PAIR;
   its hypothesis is infranormality (the compression semigroup
   `P_Lambda = {g : g Lambda g^{-1} <= Lambda}` generates).  For the
   arithmetic pair `P_Lambda` is trivial: if `g SL_n(Z) g^{-1}
   subseteq SL_n(Z)` for `g in SL_n(R)`-conjugation coming from
   `GL_n(Q)`, both sides are lattices in `SL_n(R)` of equal covolume
   (conjugation preserves Haar), and `covol(g Lambda g^{-1}) =
   [Lambda : g Lambda g^{-1}] . covol(Lambda)` forces index one, i.e.
   equality.  So `P_Lambda = N(Lambda)`, which is `Lambda` itself
   (a normalizing `g` maps the `SL_3(Z)`-invariant lattice class of
   `Z^3` — unique up to scaling by the elementary-difference argument —
   to a scaling, so `g in GL_3(Z) cap SL_3 = SL_3(Z)`), and `Lambda` is
   as far from infranormal as possible.  Consequently Kun–Thom Thm A /
   Cor. D do NOT apply to `W_3`: the soficity of `W_3` and of the
   arithmetic coset action is genuinely open, and the arithmetic lane's
   mechanism (commensuration/co-density) is provably disjoint from the
   Kun–Thom compression mechanism.  Theorem 3's entropy ceiling is
   unconditional either way.  Recorded as
   `arithmetic-integral-subgroup-is-incompressible`.
3. **Both `L(Gamma)` and `L(W_3)` are strongly 1-bounded (if CE).**
   For `L(Gamma) = L(SL_3(Z[1/3]))` this is property (T) strong
   1-boundedness (Hayes–Jekel–Kunnawalkam Elayavalli, arXiv:2107.03278,
   J. Inst. Math. Jussieu); for `L(W_3)` it is Theorem 3.  So no naive
   entropy gap separates the wreath from its base; the excess-entropy
   hole must be genuinely finer (relative/local entropy of the lamp
   torsor given the base), not a global count.
4. **The exact congruence lamp torsor does not supply that relative count.**
   The joint lamp eigenbases form a macroscopic homogeneous space before
   quotienting, but it is one global-conjugacy orbit.  After the finite actor
   table is imposed, only discrete finite-group multiplicities remain; the
   mixed regular character selects the regular representation.  The exact
   count and the `exp(O(d log d))` ceiling for growing packets are recorded in
   `finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge`.  Thus the
   new route must find genuinely approximate, noncorrectable relative moduli.
5. **Even the relative tangent space is pure gauge.**  For a finite wreath
   packet `H=A rtimes Q`, averaging gives
   `H^1(H,u(d)_Ad rho)=0`.  Cocycles vanishing on the actor `Q` are generated
   by elements of `rho(Q)'`, so actor-fixing conjugacies kill the entire
   fiber tangent.  At a regular packet the raw tangent has dimension
   `d^2(1-|H|^(-1))`, but all of it is orbit tangent.  The exact computation
   and uniform approximate linear contraction are
   `finite-wreath-relative-tangent-moduli-vanish`.
6. **Only moving quotient-kernel cells escape the local contraction.**  True
   radius-`R` multiplication cells cost at most
   `Dehn_G(3R) Def(presentation)`, and every vanishing-defect sequence has a
   diagonal growing radius where that table is accurate.  A congruence
   quotient cell, however, may lift to a nontrivial kernel word in the
   original group and has no van Kampen bound.  The exact theorem and the
   resulting entropy/compiler dichotomy are
   `wreath-ball-area-controls-only-true-group-cells`.
7. **Finite-image moving-kernel tangents vanish.**  For every finite-image
   representation of `W_3`, its kernel has torsion abelianization: the lamp
   part has exponent two and the projected finite-index arithmetic subgroup
   has property `(T)` and finite abelianization.  Inflation--restriction then
   gives `H^1(W_3,u(d)_Ad rho)=0`, including the actor-fixed relative fiber.
   Thus moving kernel cells can matter only nonlinearly; see
   `finite-image-summit-wreath-relative-h1-vanishes`.

## Trust surface

Refereed inputs, used at statement level: Jung GAFA 2007
(arXiv:math/0510576); Hayes IMRN 2018 (arXiv:1505.06682); Voiculescu
GAFA 1996 (absence of Cartan machinery); Hayes–Jekel–Kunnawalkam
Elayavalli JIMJ (arXiv:2107.03278); Serre (trees; the `SL_2` amalgam and
vertex stabilizers), Bruhat–Tits theory as in standard references
(building of `SL_n(Q_p)`, convexity of apartments, kernel = center),
strong approximation for `SL_3` over `S = {infinity, 3}`.  Theorems 1
and 2 are proved in full above; Theorem 3 is a two-line composition of
the cited theorems with Theorem 2.
