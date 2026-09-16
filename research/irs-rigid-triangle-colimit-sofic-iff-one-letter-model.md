---
rg: 2
id: irs-rigid-triangle-colimit-sofic-iff-one-letter-model
kind: claim
title: An IRS-rigid infinite simple colimit of a triangle of finite groups is sofic iff it has exact free vertex models that disagree on one edge only
artifacts:
  - research/artifacts/km-246-lattice-is-sofic-one-letter-models-2026-09-16.md
distinct_from:
  km-246-lattice-is-sofic: that is the open existence question for S_q; this is an equivalence theorem for a class of triangle colimits that rewrites the question, proving the necessity direction that the target only states as sufficient, and it decides nothing.
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that shows every nontrivial almost action of an IRS-rigid simple group is a sofic approximation; this uses it once, for one direction, and adds finite-group rounding, padding and alignment to make every vertex chart free and two of the three edge identifications exact.
  triangle-edge-matching-reduces-to-one-edge-holonomy: that is a Hilbert--Schmidt statement about flexible HS stability, under cyclic edge groups and split abelianizations, with padding by linear characters; this is about soficity (existence of permutation models), needs no hypothesis on the edge groups, and replaces a stability statement by IRS rigidity.
  triangle-of-finite-groups-hs-stability-is-edge-matching: that characterizes flexible HS stability of any triangle colimit by gluing almost-matching genuine representations; this characterizes soficity, not stability, of IRS-rigid simple colimits, by permutation charts with one inexact edge.
  titz-witzel-soficity-is-one-finite-csp: that reduces soficity of one Titz Mite--Witzel kernel to a three-permutation problem; this is the finite gate for colimits of triangles of finite groups, with the Kac--Moody lattices as instance.
  km-246-lattice-stability-dictionary: that equates nonsoficity of S_q with permutation stability; this equates soficity with the existence of one-letter models, a presentation-level finite search problem.
---

Unreviewed. No novelty is claimed; the ingredients are elementary.

**Setting.** A *triangle of finite groups* here is three finite vertex groups `X_12, X_13, X_23`
and three finite edge groups with injective homomorphisms

```text
X_1 -> X_12, X_13        X_2 -> X_12, X_23        X_3 -> X_13, X_23,
```

each written `iota_ij` (the edge is read off from the argument). Its colimit is

```text
S = (X_12 * X_13 * X_23) / << iota_ij(x) iota_ik(x)^(-1) : x in X_e, e the edge joining ij, ik >>.
```

A face group mapping into all three edges adds no relations and is ignored.

**Hypotheses.**
- (S1) `S` is infinite and simple.
- (S2) Every invariant random subgroup of `S` is a convex combination of `delta_e` and `delta_S`.
- (S3) Each canonical map `X_ij -> S` is injective.

**One-letter models.** Throughout, `d >= 1`: every set acted on is nonempty, since on `[0]` all
conditions below hold vacuously. For `epsilon >= 0` an *`epsilon`-model on `[d]`* is a triple of
homomorphisms `rho_ij : X_ij -> Sym(d)` such that
- (M1) each `rho_ij` is free (every nontrivial element has no fixed point);
- (M2) `rho_12 o iota_12 = rho_13 o iota_13` on `X_1` and `rho_13 o iota_13 = rho_23 o iota_23`
  on `X_3`, exactly;
- (M3) the *defect set* `D = {p : rho_12(iota_12 x) p != rho_23(iota_23 x) p for some x in X_2}`
  has `|D| <= epsilon d`.

Put `K_0 = (X_12 *_{X_1} X_13) *_{X_3} X_23` and let `K` be the HNN extension of `K_0` with
letter `t` and relations `t iota_12(x) t^(-1) = iota_23(x)` for `x in X_2`. Then
`K/<<t>> = S`. An `epsilon`-model is the same thing as an action of `K_0` on `[d]` with free
vertex groups and defect set of size at most `epsilon d`. Write
`n_x = iota_23(x)^(-1) iota_12(x) in K_0`.

**Theorem.** Under (S1)-(S3) the following are equivalent.
- (a) `S` is sofic.
- (b) For every `epsilon > 0` there are `d >= 1` and free homomorphisms `rho_ij : X_ij -> Sym(d)`
  with `d_H(rho_ij(iota_ij x), rho_ik(iota_ik x)) <= epsilon` for every edge and every `x` in it.
- (c) For every `epsilon > 0` there is an `epsilon`-model.
- (d) For every `epsilon > 0` there is a homomorphism `rho : K -> Sym(d)`, `d >= 1`, free on each vertex
  group, with `|supp rho(t)| <= epsilon d`.
- (e) For every `epsilon > 0` there is a finite-index subgroup `M <= K_0` meeting every conjugate
  of every vertex group trivially, such that at most `epsilon [K_0:M]` cosets `kM` have
  `k^(-1) n_x k notin M` for some `x in X_2`.

The quantitative steps are: (b) with `epsilon` gives (c) with
`|X_2| (1 + 2|X_3| (1 + 2|X_1|)) epsilon`; (c) and (d) convert into each other with factor
`1` and `|X_2|`; (c) gives (e) with the same `epsilon`, and (e) is (c) on `K_0/M`. The inexact
edge may be any of the three, by relabelling.

**Necessary shape of every `epsilon`-model** (only (S1) is used).
- (N1) Every `K_0`-orbit meets `D`, and `D` meets each orbit in a union of free `X_2`-orbits.
  So there are at most `epsilon d/|X_2|` orbits, and in (e) `[K_0:M] >= |X_2|/epsilon`.
- (N2) If `M` in (e) is normal in `K_0`, every coset is in the defect set. So for
  `epsilon < 1` there are no Galois certificates, that is, no models given by the regular
  action of a finite quotient of `K_0`.
- (N3) Let `Q = rho(K)` in (d) and `1 != y in X_ij`. Then `Q` is the normal closure of
  `rho(t)`, and every expression of `rho(y)` as a product of conjugates of `rho(t)^(+-1)`
  has at least `1/epsilon` factors. The same bound holds in `rho(K_0)` for products of
  conjugates of the `rho(n_x)^(+-1)`.
- (N4) Negative reading: `S` is not sofic iff there is `epsilon_0 > 0` such that every finite
  action of `K` that is free on the vertex groups moves at least `epsilon_0 d` points by `t`
  (`d >= 1`).

**Instance (conditional on the Levi presentation recorded in `km-246-lattice-is-sofic`).**
Take `X_ij = L_ij/Z`, `X_i = L_i/Z`, with `L_12 = T.(SL_2(q) x SL_2(q))`,
`L_13 = T.Sp_4(q)`, `L_23 = T.G_2(q)`, edges `T.SL_2(q)`, and `Z` the centre of `Lambda_q`.
Suppose that `Lambda_q` is the colimit of the `L`-triangle (Abramenko--Muhlherr 1997,
identified through Caprace--Remy, not read at source), and that `Z` lies in the torus `T`
(standard for split minimal Kac--Moody groups, not read at source). Then `S_q` is the colimit
of the `X`-triangle, because `Z` is central and contained in every edge and vertex group.
(S1) and (S2) hold for `q >= 4` by `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`.
(S3) holds because the `L_ij` are subgroups of `Lambda_q` containing `Z`. So
`km-246-lattice-is-sofic` is equivalent to finding, for some `q >= 4` and every
`epsilon > 0`, free actions of these three finite groups glued exactly along two `T.SL_2(q)/Z`
edges and along the third off `epsilon d` points. By (M1), `d` is a multiple of
`lcm |X_ij|`, which is `12831436800/|Z|` at `q = 4` (see the artifact).

Proof: `irs-rigid-triangle-colimit-one-letter-model-proof`.
