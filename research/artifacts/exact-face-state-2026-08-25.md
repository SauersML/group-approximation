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
`T`; `T^k` transports isotypic weights along `Ad(h^k)` with additive error
`12 k epsilon/kappa_0`; Bass--Milnor--Serre passes from two root subgroups to
`Gamma(p^(a-k)m')`; compressing the equivariant cell family onto the fixed
subspace gives the upper bound.  Result: depth x defect bounded below, top
segments of levels carry `O(epsilon)` weight per level.  Node:
`homogeneous-quotient-near-genuine-microstates-are-deep`.  The naive
level-by-level descent loses `sqrt(delta)` per level and reaches only
`log log(1/epsilon)` levels; the additive version is essential.

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
`h`-twist on `C_0`: `c_p (1 - nu_0) <= 12 D epsilon/kappa_0`, with
`c_p = 1 - (p^2+p-2)/(p^3-1) - 1/(p+1) > 0` for every prime (uniform
coadjoint-orbit count of `Y_21 = 0`).  Together with the graph's
coprime-level closure (`odd-congruence-lambda-exact-sector-collapses`), the
Lambda-exact face of `(RC3)` is confined to towers of depth
`>= c_p kappa_0 (1 - nu_0)/(12 epsilon)`.  Node:
`lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible`.

## 5. What remains, precisely

- **Ultra-deep towers.**  The chained defect is linear in `k`, so the depth-`k`
  constraint dies at `k ~ kappa_0/epsilon`; towers deeper than that evade every
  bound above.  A construction would need a level-`p^D` representation of
  `SL_3(Z)` with `D ~ 1/epsilon` and an `epsilon`-intertwiner for the
  `h`-twist; the natural candidate (truncating the `A`-action on the level-`D`
  vertex set `L/K_D`) fails because that Schreier graph has exponential
  growth.  Nothing rules them out.
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
