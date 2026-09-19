# The exact face of the arithmetic relative-commutant collapse: state on 2026-08-25

Companion to the nodes landed today (`37038f9f0`, `7d556a82e`, `772cffc27`,
`204764f1c`, `7cfec0100`, `8e568c383`).  Pair: `C = SL_n(Z) < A = SL_n(Z[1/p])`,
`h = diag(p,1,...,1/p)`; `L = SL_n(Q_p)`, `K = SL_n(Z_p)`.

## 1. The canonical enemy is a homogeneous quotient, not a wreath

`M = L^infty(L/Lambda') x| A` for a torsion-free cocompact lattice `Lambda'`
with at least two `K`-orbits on `L/Lambda'`.  `A` acts ergodically (dense),
`C` does not (through the compact `K`), the group unitaries have the regular
trace, and a `K`-orbit symmetry `U` is `C`-central with `|tau([U, u_h])| < 1`
(the phase-line stabilizer of `U` is an index-`<= 2` subgroup containing `C`
and `h`, dense, hence ergodic).  So Connes embeddability of `M` refutes
`(RC3)`, `(PTS1)`, `(PRT1)`, `(NSL1)`; it does NOT refute the exact
quasi-regular leak (the leak's profile is the automorphic spherical spectrum
of the finite building quotient) nor the exact-face Iwahori claims.
Structure: `L^infty(L) x| A = (L^infty(K) x| C) (x) B(l^2)`, so `M` is stably a
crossed product of an embeddable II_infty factor by the residually finite
lattice `Lambda'`; for `n = 2`, `M` is an amalgamated free product of two
profinite algebras over a finite-index base.  Nodes:
`homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`,
`dense-s-arithmetic-translation-algebra-is-amplified-profinite`,
`sl3-/sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`.

## 2. Near-genuine microstates of M are deep flat towers (n = 3)

One Kazhdan projection on `C_0 = C cap h^-1 C h` gives an exact intertwiner
`T`; Pythagoras and the contraction-defect identity show that `T^k`
transports isotypic weights along `Ad(h^k)` with overlap deficit
`O(k epsilon^2/kappa_0^2)`; Bass--Milnor--Serre passes from two root subgroups to
`Gamma(p^(a-k)m')`; compressing the equivariant cell family onto the fixed
subspace gives the upper bound.  Result: depth times squared defect bounded
below, top segments of levels carry `O(epsilon^2)` weight per level.  Nodes:
`homogeneous-quotient-near-genuine-microstates-are-deep` and
`orthogonal-kazhdan-powers-have-quadratic-depth-loss`.  The naive
level-by-level descent loses `sqrt(delta)` per level and reaches only
`log log(1/epsilon)` levels; the all-depth orthogonal version is essential.

## 3. Atkin--Lehner: the exact matching condition in rank one

`cap_(i<=k) h^-i SL_2(Z) h^i = Gamma_0(p^(2k))`, normalized by
`g_k = [[0,p^-k],[-p^k,0]]`; the matching condition at depth `k` is
near-invariance of the isotypic weight measure of the restriction under
`Ad(g_k)`.  The vertex-orbit permutation representation on `S(o,2k)` and its
twist are at total-variation distance exactly `2 - 2p^-k` (far sphere:
`2 - 2p^-2k`): the Moebius kernel and the affine twisted kernel generate
`{a = d = +-1 mod p^2k}`, so shared constituents are unit characters.
Verified numerically for `p in {2,3,5,7,11}`, `k <= 3` (fourteen exact
values; `research/artifacts/atkin_lehner_tv.py`).  Node:
`atkin-lehner-twist-of-vertex-orbit-representation-is-disjoint`.  Rank-one
caveat: `SL_2(Z)` has non-congruence finite quotients and infinite-image
finite-dimensional representations, on which isotypic weights are not
perturbation-stable, so this describes only the congruence sub-face there.

## 4. Rank two: the p-divisible Lambda-exact sector is ultra-deep or negligible

For genuine `rho'` of level `p^D m'` and `H` epsilon-intertwining the
`h`-twist on `C_0`: `b_p (1 - nu_0) <= D epsilon^2/kappa_0^2`, with
`c_p = 1 - (p^2+p-2)/(p^3-1) - 1/(p+1)` and
`b_p=min(c_p,1/3)>0` for every prime (coadjoint-orbit count from level two,
and the three-transvection bound at level one).  Together with the graph's
coprime-level closure (`odd-congruence-lambda-exact-sector-collapses`), the
Lambda-exact face of `(RC3)` is confined to towers of depth
`>= b_p kappa_0^2 (1 - nu_0)/epsilon^2`.  Nodes:
`lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible` and
`orthogonal-kazhdan-powers-have-quadratic-depth-loss`.

## 4b. Depth-free: the p-divisible sector is EMPTY at p >= 11

Track each `C_0`-constituent by `(beta, gamma)` = (upper, lower) simple-root
depths.  The twist by `J h` acts as `(beta, gamma) |-> (gamma - 1, beta + 1)`
and moves every diagonal type off the diagonal.  Clifford balancing over
`sl_3(F_p)` puts `>=2c_p-1` of every level `a>=2` on the diagonal and
`<=2(1-c_p)` off it.  Level one is not a Lie layer; three conjugate
transvection subgroups generate `SL_3(F_p)` and put at least `1/3` of its
mass on `(1,1)`.  Hence, for `a_p=min(4c_p-3,1/3)`,
`a_p(1-nu_0) <= epsilon^2/kappa_0^2` with NO depth: for `p >= 11`
the `p`-divisible weight of any near-genuine microstate is `O(epsilon^2)`,
ultra-deep towers included, and the homogeneous-quotient crossed product has
no near-genuine microstates at all.  The coprime closure is robust to an
`o(1)` admixture (a vanishing-weight summand is invisible in the tracial
ultraproduct), so the whole `Lambda`-exact face of `(RC3)` at `p >= 11` is
closed.  Nodes: `p-divisible-lambda-exact-mass-vanishes-at-large-primes`,
`coprime-sector-collapse-is-robust-to-small-p-admixture`,
`sl3-large-prime-pair-relative-commutant-collapse`,
`sl3-large-prime-collapse-from-weak-ucp-stability`,
`non-hyperlinear-from-sl3-large-prime-collapse`.

**Net effect on the goal.**  `cairn impact sl3-z-weakly-ucp-stable`: if weak
ucp-stability of `SL_3(Z)` on regular-type hyperlinear approximations were
established, `non-hyperlinear-group` would flip to ESTABLISHED along two
independent edges (the earlier thin-subgroup edge consuming host stability,
and the large-prime edge consuming subgroup stability through the
established exactification).  Everything else on the large-prime edge is
proved.  Section 5 below is superseded on the exact face at `p >= 11`; it
still describes `p <= 7` and rank one.

## 4c. The involution route: outlier confinement and the weakest leaf

Rounding the stable letter (sector functions of the Haar unitary) shows a
hyperlinear `G_p` would make every `Gamma *_Lambda (Lambda x C_m)`
hyperlinear; the binary case `E_p` is the double-swap group, equivalent to
the arithmetic double.  Running sections 4-4b against the swap involution
gives an unconditional theorem: at `p >= 11` the involution is confined to
uniform lattice outliers (the fold mark `[h, s]` would otherwise have trace
1 against canonical 0).  The route through `E_p` therefore rests on the
single open leaf `sl3-outliers-carry-no-balanced-free-involution`, implied
by weak ucp-stability and not conversely -- the weakest leaf wired to the
goal.  Two fences protect it: free involutions maximally anticommute with
their twists, so abelian-carried leaks (wreath coordinates, K-orbit cells)
can never satisfy the pattern; and the Weyl reverser `x_0 = h w_13`
(an involution of `Gamma` inverting the twist word `z = s hsh^-1`) refutes
the naive enemy descent to depth one by an exact identity, leaving only a
dihedral form.  One rigidity -- `w_13 h w_13^-1 = h^-1` -- thus closes the
coprime face AND blocks enemy regeneration.

## 5. What remains, precisely

- **Ultra-deep towers.**  Orthogonal projection replaces the old linear
  norm telescope by the sharp square function `k epsilon^2/kappa_0^2`, so
  the depth-`k` constraint dies at `k ~ kappa_0^2/epsilon^2`; towers deeper
  than that evade every bound above.  A construction would need a
  level-`p^D` representation of `SL_3(Z)` with `D ~ 1/epsilon^2` and an
  `epsilon`-intertwiner for the
  `h`-twist; the natural candidate (truncating the `A`-action on the level-`D`
  vertex set `L/K_D`) fails because that Schreier graph has exponential
  growth.  The abstract truncated cyclic shift saturates the square-function
  inequality, so one projected intertwiner alone cannot do better.  Nothing
  rules out the arithmetic towers.
- **Outliers.**  Microstates whose `SL_3(Z)`-part is uniformly far from every
  genuine representation.  Their existence for `SL_3(Z)` is
  `sl3-z-weakly-ucp-stable` (open); the graph's earlier remark that infinite
  hyperlinear (T) groups are never flexibly stable is unsourced and should
  not be relied on.
- **Rank one.**  Beyond the congruence sub-face, the exact face of the
  `SL_2` pair is the full local-global problem for the amalgam
  `SL_2(Z) *_B SL_2(Z)` (Dogon--Vigdorovich), where the tangent-space count
  (`dim H^1(B) ~ (p+1)n^2/12` against `2 n^2/12` from the two vertex groups)
  shows the two restriction images are far from transverse, so nothing is
  decided by dimension counting.

Addendum (late 2026-08-25): with 4c, "what remains" for the involution
route is exactly one statement -- no uniform lattice outlier carries a
balanced free central involution.  Everything else on that route is
established and unconditional.
