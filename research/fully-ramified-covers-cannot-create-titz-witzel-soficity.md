---
rg: 2
id: fully-ramified-covers-cannot-create-titz-witzel-soficity
kind: claim
title: A flat-hitting cover that is fully ramified over a base branched cover costs a whole fibre per unbranched base component, so the base already certifies soficity and hyperbolic-group inputs (VTF, residual finiteness, goodness) are idle for the Titz--Witzel kernel
distinct_from:
  sofic-lattice-plus-hyperbolic-vtf-gives-flat-hitting-covers: that builds flat-hitting covers from a sofic base plus (V2); this proves that every construction of that shape (any base, any fully ramified top cover, in particular any torsion-free or normal finite-index subgroup of any complex of groups over the base) needs a base that already satisfies item 3 of the connected-links equivalence, so the hyperbolic input can never be the source of soficity.
  sparse-fully-branched-covers-iff-sofic-with-connected-links: that is the equivalence of soficity with sparse (fully) branched covers; this is a mass identity for towers X' -> X_0 -> Y, which uses that equivalence only to name what the base already proves.
  branched-cover-branching-mass-is-quantized-by-deck-group: that quantizes the mass of a connected cover of Y by its own deck group over Y; here the symmetry is relative to an intermediate base X_0, not over Y, and the mass is not quantized but bounded below by the unbranched part of the base.
  titz-witzel-flat-hitting-sparse-branched-covers: that asks for flat-hitting sparse covers of Y_1^2; this kills every fully ramified construction of them that does not already start from a soficity certificate, and says what a construction must do to avoid it (partial ramification).
  every-hyperbolic-group-is-good: that is a famous open problem in the cone of the flat-hitting route; this shows its resolution cannot move titz-witzel-kernel-sofic through any fully ramified construction.
---

**ESTABLISHED** (proof: `fully-ramified-covers-cannot-create-titz-witzel-soficity-proof`).

**Setting.** `Y`, `G = pi_1(Y)`, `Delta = Y~`, finite branched covers, local
degrees `d_x`, sheet numbers and the branching mass `beta` are as in
`sparse-fully-branched-covers-iff-sofic-with-connected-links` (covers need not
be connected). Assume every vertex link of `Y` is nonempty and `G` has an
infinite simple subgroup `K` of finite index `m = [G : K]`.

For a finite branched cover `X_0 -> Y`, write `N_0` for its sheet number,
`B_0` for its branch set and `phi(X_0)` for the fraction of the `N_0` sheets
lying in branched components.

**Definition (fully ramified tower).** A *fully ramified tower* is a pair of
finite branched covers `q: X' -> X_0` and `p_0: X_0 -> Y` such that for every
vertex `y` of `X_0`, the local degrees `d^q_x` at the points `x` of `q^(-1)(y)`
are either all `1` or all `>= 2`. Its *ramification set* is the set `S` of
vertices of the second kind.

The main examples are the following.
* `X' = Lambda \ D`, where `D` is the development of a complex of groups over
  `X_0` with trivial edge and face groups and finite vertex groups
  `Q_y = pi_1(Lk(y)) / N_y`, and `Lambda` is a finite-index subgroup of
  `Gamma = pi_1` of that complex of groups which is *torsion-free* or
  *normal*.
* In particular, Step 6 of `sofic-plus-vtf-flat-hitting-covers-proof` (normal
  core `Lambda_0` of a torsion-free subgroup).
* Any finite regular (Galois) branched cover of `X_0`.

**Theorem.** Let `X' -> X_0 -> Y` be a fully ramified tower with ramification
set `S`, and let `X' -> Y` be the composite.
1. **(Mass identity.)** `X' -> Y` is a finite branched cover, and
   `beta(X') = beta(X_0) + |S \ B_0| / N_0`.
2. **(Hitting descends.)** Suppose `X'` satisfies (H) with radius `R`, that is,
   no locally isometric map from the closed Euclidean `R`-disk misses `B'`.
   Then no locally isometric map from that disk to `X_0` misses `S cup B_0`.
3. **(Fibre cost.)** Suppose `Delta` contains an isometrically embedded
   Euclidean plane (for example `Delta` a Euclidean building) and `X'`
   satisfies (H) for some `R`. Then every unbranched component of `X_0` meets
   `S`, and
   `beta(X') >= beta(X_0) + (1 - phi(X_0)) / m`.

**Corollary (the base already certifies).** Suppose every vertex link of `Y`
is connected, `Delta` contains a flat, and there are fully ramified towers
`X'_n -> X_{0,n} -> Y` with `X'_n` satisfying (H) and `beta(X'_n) -> 0`. Then
`beta(X_{0,n}) -> 0` and `phi(X_{0,n}) -> 1`. So the bases alone satisfy
item 3 of `sparse-fully-branched-covers-iff-sofic-with-connected-links`, and
`K` is sofic by its 3 => 1. For `Y = Y_1^2` this applies verbatim: `m` is
finite and `Delta` is a `C~_2` building (`titz-witzel-simple-kazhdan-cat0-lattices-exist`),
whose apartments are flats, and the links are connected (Corollary of
`sparse-fully-branched-covers-iff-sofic-with-connected-links`).

**Obstruction (what dies, and where).** Class: every construction of
flat-hitting sparse covers of `Y_1^2` that ends with a fully ramified step
over some base. This includes all complex-of-groups hyperbolizations
finished by a torsion-free or a normal finite-index subgroup, which is
exactly where (V2), residual finiteness, goodness, cubulation or soficity
of hyperbolic groups can enter.
* *Invariant:* `phi(X_0)`, the fraction of base sheets in branched
  components, through the identity `beta(X') = beta(X_0) + |S \ B_0|/N_0`.
* *Step where every member dies:* the hitting step. Hitting an unbranched
  base component costs a whole fibre, so mass `>= 1/m` per sheet of that
  component. Sparsity then forces the base to satisfy item 3, which is
  equivalent to `titz-witzel-kernel-sofic`.
* *Consequence:* no theorem about hyperbolic groups can move
  `titz-witzel-kernel-sofic` (hence the goal
  `torsion-free-sofic-exact-mf-radical-over-z` via
  `torsion-free-sofic-exact-mf-radical-via-titz-witzel`) through such a
  construction. The sub-cone under `titz-witzel-flat-hitting-via-soficity-and-2d-vtf`,
  including `two-dimensional-cat0-hyperbolic-groups-virtually-torsion-free`
  and `every-hyperbolic-group-is-good`, is goal-inert.

**What escapes.** A top step that is *partially ramified*: some base vertex
has both branched and unbranched points in its fibre. For `Lambda \ D` this
means `Lambda` has torsion and contains a vertex group `Q_y` but not all of
its conjugates. The Remark in the proof gives the version for components of
different degrees.
