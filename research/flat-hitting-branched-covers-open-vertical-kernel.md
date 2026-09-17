---
rg: 2
id: flat-hitting-branched-covers-open-vertical-kernel
kind: claim
title: In a flat-hitting branched cover of a product-of-trees complex, short vertical-kernel loops close B-freely only at a branching-mass fraction of vertices
distinct_from:
  radu-square-complex-flat-hitting-sparse-branched-covers: that asks for sparse flat-hitting covers of Radu's complex; this proves a quantitative necessary condition on any such cover and kills every construction that is locally a finite cover on a positive fraction of balls.
  flat-hitting-branched-covers-have-hyperbolic-pi1: that derives hyperbolicity from flat hitting; this derives a lower bound on branching mass from flat hitting plus B-free closure of vertical-kernel loops, without using branch girth.
  sparse-branched-covers-with-sofic-pi1-give-sofic-lattice: that transfers soficity from covers to the base and notes that unbranched covers are sparse; this shows that flat hitting forces the local structure of a sparse cover to separate the vertical kernel, unlike any unbranched cover.
  titz-witzel-sparse-defect-needs-dense-generator-surgery: that forbids sparse edits of exact finite sheets of a marked model; this is about branched covers under flat hitting, and the count is a forest exit count over vertical slabs rather than a defect propagation.
---

**ESTABLISHED** (proof: `flat-hitting-branched-covers-open-vertical-kernel-proof`).

**Setting.**
* `Y` is a finite nonpositively curved VH square complex with universal cover
  `Delta = T1 x T2`, and `H = pi_1(Y)` preserves the two factors.
* Every vertex of `T1` has degree at least `m >= 3`.  `D` is the maximal
  horizontal degree of a vertex of `Y`.  `P_L` is the number of based closed
  edge paths of length at most `L` in `Y`.
* `N = ker(H -> Aut T1)`.  Its nontrivial elements are hyperbolic on `T2`.
* `S` is a subset of `N \ {1}` closed under conjugation by `H`, for instance
  `N \ {1}` itself or one conjugacy class.
* `p: X -> Y` is a finite branched cover of degree `n_X`, with branch set `B`
  and branching mass `beta(X)`, as in
  `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`.

For a vertex `o` of `Delta`, let `S_L(o) = {s in S : d(o, s o) <= L}`.

**Definition (closed vertical slabs).**  `W^S_L(X)` is the set of unbranched
vertices `y` of `X` such that, for some (equivalently every) vertex `o` of
`Delta` over `p(y)`, both of the following hold.
* **(A)** Some `s in S_L(o)` has `o` on its axis, i.e. `d(o, s o)` is its
  translation length.
* **(C)** For every `s in S_L(o)`, the lift from `y` of the loop
  `p[o, s o]` meets no vertex of `B` and ends at `y`.

**Theorem.**  If `X` satisfies (H) of `flat-hitting-branched-covers-have-hyperbolic-pi1`
(for some `R`, no locally isometric immersion of a Euclidean `R`-disk into
`X \ B`), then

```text
(m - 2) |W^S_L(X)|  <=  D (L+1) P_L  beta(X) n_X .                     (VS)
```

Branch girth (G) is not used.

**Corollary 1 (finite residual).**  Suppose `g in S` lies in the finite
residual of `H`, and `S` is the `H`-conjugacy class of `g`.  Let `L` be the
translation length of `g` on `T2`, and `v = p(o)` for a vertex `o` on the
axis of `g`.  Call a vertex `y` of `X` over `v` *locally finite* if its rooted
`L`-ball in the 1-skeleton, all of whose vertices are unbranched, is
isomorphic over `Y` to the rooted `L`-ball of a vertex of some finite
unbranched cover of `Y`.  Then every locally finite vertex lies in
`W^S_L(X)`.  So under (H) there are at most `D (L+1) P_L beta(X) n_X / (m-2)`
locally finite vertices over `v`.

**Corollary 2 (Radu's complex: a class of constructions dies).**  Let
`Y = S_R`, so `m = D = 3`.  Some power `g = (xz)^(4j)`, `1 <= j <= 4`, lies in
`pi_1(S_R)`.  It lies in `Lambda_v` and in the finite residual
(`radu-horizontal-projection-kills-delta-squared`, `radu-bmw-lattice-embeds-in-titz-witzel-kernel`).
Hence there is a constant `c_R > 0` with the following property.  Every
branched cover `X` of `S_R` satisfying (H), in which a fraction `f` of the
vertices over `v` are locally finite, has

```text
beta(X)  >=  c_R f .
```

So `radu-square-complex-flat-hitting-sparse-branched-covers` cannot be
witnessed by the following constructions, all with `f` bounded below:
* a finite (congruence, random or other) cover of `S_R` modified at a set of
  vertices whose `L`-neighbourhood has at most `(1 - f) n_X` vertices;
* any branching planted on a finite cover of `S_R` at a vertex set, however
  `R`-dense, of density at most `1/(2 |ball_L|)`, where `|ball_L|` bounds the
  size of an `L`-ball (then `f >= 1/2`).

For such constructions the naive bound from (H) is only `beta >~ 1/R^2`,
which tends to zero.  (VS) is a bound independent of `R`.

**Reading.**  Any sparse flat-hitting cover of `S_R` must, at all but an
`O(beta)` fraction of its points, lift a short conjugate of the mark to an
open path.  Its local structure must separate the finite residual, which no
finite quotient of `pi_1(S_R)` does.  So the branched-hyperbolization route to
soficity of `Gamma_R`, and through it to `K`, does not bypass the
non-residual-finiteness gate; it relocates it into the local combinatorics of
the cover.

DERIVATION
flat-hitting-branched-covers-open-vertical-kernel-proof
