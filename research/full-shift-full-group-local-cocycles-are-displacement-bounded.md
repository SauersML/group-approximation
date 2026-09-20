---
rg: 2
id: full-shift-full-group-local-cocycles-are-displacement-bounded
kind: claim
title: "Class-kill for [[X]]: every 1-cocycle of the full-shift topological full group that is local for a covariant spectral measure on X (measured walls over any Z-extension of X with any invariant data, Maharam and quasi-invariant walls, l2 of orbits, orbit walls weighted by patterns, their sums, integrals and limits) satisfies psi(g) <= psi(sigma) * sum_{k in k_g(X)} k^2, so it is bounded on the infinite set {|k_g| <= 1} and never proper; the same bound holds in V, so a proper witness must be non-local like Farley's"
distinct_from:
  full-shift-topological-full-group-is-a-t-menable: that is the open existence claim for [[X]]; this proves that one large class of candidates, the germ-local cocycles, contains no proper member
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that bounds extractable cocycles of T-bar on its centre, using relations among three elements; this bounds local cocycles of [[X]] on a displacement ball, using only the clopen decomposition of each element into shift powers
  nv-extractable-cocycles-bounded-on-centralizers: that bounds extractable cocycles of nV on a centralizer, using paradoxical gaps; this uses no relation at all, only subadditivity of a local cocycle over the germ pieces of an element
  nv-local-density-walls-bounded-on-callard-salo-element: that bounds integrated local walls of nV along one element f^N, using a belt-length tail of Lebesgue measure; this bounds every local cocycle of [[X]], for every covariant measure class, including atomic and infinite ones, on the whole displacement ball
---

**ESTABLISHED** by `full-shift-local-cocycles-displacement-bound-proof` (`requires: []`). Nothing
is imported except, for the calibration in item 5, Farley's theorem that `V` is Haagerup.

## Setting

- `X = {0,1}^Z`, `σ` the shift, and `[[X]]` the group of homeomorphisms `g(x) = σ^{k_g(x)} x`
  with `k_g : X → Z` continuous. `k_g` is uniquely determined by `g` (aperiodic points are dense),
  and `k_{gh}(x) = k_h(x) + k_g(hx)`. Write `|g| = max |k_g|`.
- **Covariant pair.** A unitary representation `π` of `[[X]]` on a Hilbert space `H`, together
  with a projection-valued measure `P` on the Borel sets of `X` such that `P(X) = I` and
  `π(g) P(A) π(g)^* = P(gA)` for all `g` and all Borel `A`.
- **Local cocycle.** A 1-cocycle `b : [[X]] → H` for `π` (so `b(gh) = b(g) + π(g) b(h)`) is
  *local* for `P` if, for all `g, h ∈ [[X]]` and every clopen `B ⊆ {x : k_g(x) = k_h(x)}`,

    `P(gB) b(g) = P(hB) b(h)`.

  Note that `gB = hB` here. In words, the part of `b(g)` sitting over a region depends only on the
  germs of `g` there. A cnd function `ψ` is *local* if `ψ(g) = ‖b(g)‖²` for a local cocycle of some
  covariant pair.
- `B_r = {g ∈ [[X]] : |g| ≤ r}`.

## Statement

1. **(Germ subadditivity.)** Let `b` be local and `g ∈ [[X]]`. Let `U_1, …, U_N` be a clopen
   partition of `X` and `t_1, …, t_N ∈ [[X]]` with `k_g = k_{t_i}` on `U_i`. Then

     `b(g) = Σ_i P(t_i U_i) b(t_i)`, an orthogonal sum, so
     `ψ(g) = Σ_i ‖P(t_i U_i) b(t_i)‖² ≤ Σ_i ψ(t_i)`.

2. **(Displacement bound.)** Every local `ψ` satisfies
   `ψ(g) ≤ ψ(σ) · Σ_{k ∈ k_g(X)} k² ≤ ψ(σ) · (2|g| + 1) |g|²`.
   In particular `ψ ≤ 2ψ(σ)` on `B_1`, and `ψ` is bounded on every `B_r`.
3. **(Not proper.)** `B_1` is infinite. It contains the pairwise distinct involutions `g_m` of the
   w16 attempt, every swap `s_U` (equal to `σ` on a clopen `U` with `U ∩ σU = ∅`, to `σ^{-1}` on
   `σU`, and to the identity elsewhere). For a fixed clopen `E` with `E ∩ σE = ∅`, the swaps
   `s_U` with `U ⊆ E` clopen form an infinite elementary abelian 2-group inside `B_1`, because
   `s_U s_{U'} = s_{U Δ U'}`. The `g_m` (`m ≥ 1`) are the swaps `s_{E_m}`, and all of them lie in the group for `E = E_1`. So no
   local `ψ` is proper.
4. **(Closure.)** Let `𝓛` be the set of functions `ψ ≥ 0` on `[[X]]` with
   `ψ(g) ≤ ψ(σ) · Σ_{k ∈ k_g(X)} k²` for all `g`. It contains every local `ψ`, and it is closed
   under sums `Σ_j w_j ψ_j` with `w_j ≥ 0` (whenever the sum is finite at `σ`), under direct
   integrals, and under pointwise limits. No member of `𝓛` is proper, because every member is
   bounded by `2ψ(σ)` on the infinite set `B_1`.
5. **(Calibration: `V`.)** The same lemma holds for Thompson's `V` acting on `C = {0,1}^N`, with
   locality defined through germs: `B ⊆ int{x : gx = hx}`. It gives an infinite family `g_W ∈ V`,
   one for each clopen `W ⊆ C`, with `ψ(g_W) ≤ ψ(t)` for a single fixed involution `t`. So no local
   cnd function on `V` is proper. Since `V` is Haagerup (Farley), the proper cocycles of `V` are
   non-local for every covariant spectral measure on `C`. The kill therefore does not count as
   evidence against the claim for `[[X]]`. What it does is fix the form a positive witness must
   take.

## Members of the class (all verified local in the proof, Step 4)

**Master example (Z-extensions).** Let `(Ω, τ)` be a standard Borel space with a Borel
`Z`-action (it need not be free), let `p : Ω → X` be Borel with `p∘τ = σ∘p`, and let `m` be a
σ-finite `τ`-invariant measure. Let `[[X]]` act by `g·ω = τ^{k_g(pω)} ω`. This action preserves
`m`. Let `π(g)f = f∘g^{-1}` on `L²(Ω, m; K)`, for a Hilbert space `K`, and let `P(A)` be
multiplication by `1_{p^{-1}A}`. Then for every measurable `ξ : Ω → K` with
`ξ∘g^{-1} − ξ ∈ L²` for all `g`, the cocycle `b(g) = ξ∘g^{-1} − ξ` is local. Special cases:

- (a) **Invariant-measure walls (w16).** `Ω = X × Z`, `τ(x,t) = (σx, t−1)`, `m = ν ⊗ count`
  with `ν` invariant, `ξ = 1_{t ≥ 0}`. This gives `ψ = ∫|k_g| dν`, including the Maharam wall of
  `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal` 6(c) and the periodic-point sums.
- (b) **Walls over arbitrary, quasi-invariant or non-quasi-invariant data.** The same `Ω` with
  `m = Σ_t ν_t ⊗ δ_t`, where `ν_t(A) = ν(σ^t A)` for an *arbitrary* σ-finite Borel measure `ν`.
  This `m` is `τ`-invariant. Any half-space `H ⊆ Ω` with `m(gH Δ H) < ∞` for all `g` gives a
  local wall function. So do skew products `X × R` over a Radon–Nikodym cocycle (the Maharam
  extension, with `m = ν ⊗ e^s ds`), and any wall family inside them. These are exactly the
  survivors named by the w16 attempt ("measured walls over non-invariant but quasi-invariant
  data").
- (c) **`ℓ²` of orbits.** `Ω = O ⊆ X`, any `σ`-invariant set, with `τ = σ`, `p` the inclusion and
  `m` constant on each orbit. Every function `η` on `O` with `gη − η ∈ ℓ²` gives a local cocycle.
  This covers:
  - half-line walls on one or several dense orbits;
  - walls at cuts weighted by the local pattern at the cut, i.e.
    `ψ(g) = Σ_{y ∈ O} c(y) |g H_y Δ H_y|` with `H_y = {σ^n y : n ≥ 1}` (this is the second w16
    survivor);
  - orbit-wise sums `Σ_i ψ_i` over countably many orbits, whose separate bounds `C_i(r)` may
    diverge, provided each `ψ_i` is of this `ℓ²`-type. Such sums need not come from `W(Y)`, so
    they are outside the reach of the parallel w20 kill for restrictions from orbit wobbling
    groups. Here they die anyway, because `C_i(1) ≤ 2ψ_i(σ)` and `Σ_i ψ_i(σ) = ψ(σ) < ∞`.
- (d) **Direct sums and integrals** of all of the above, over any parameter space, including sums
  of `ℓ²`-orbit cocycles and non-atomic cocycles together.

**Groupoid representations (remark, not proved here and not used).** More abstractly, one expects
every cocycle of the transformation groupoid `X ⋊ Z` into a measurable Hilbert bundle, for any
quasi-invariant measure class, to be local once it is induced to `[[X]]` through
`g ↦ {(k_g(x), x)}`. The theorem applies to any such cocycle once its locality has been checked
directly. The Master example covers every case used in this graph. For the Maharam skew product
in (b), the proof needs only that `m` is `τ`-invariant, and that is standard.

## Invariant and where every member dies

- **Invariant.** Locality turns the cocycle identity into *germ subadditivity*: `ψ(g)` is at most
  the sum of `ψ` over the finitely many germ types of `g`. For `[[X]]` there are only three germ
  types of displacement at most one (`σ^{-1}, id, σ`), but there are infinitely many elements
  built from them.
- **Where every member dies.** On `B_1`, for instance on the w16 involutions `g_m`. The bound is
  explicit: `ψ(g_m) = ‖P(σE_m) b(σ)‖² + ‖P(E_m) b(σ^{-1})‖² ≤ 2ψ(σ)`. As `m → ∞` this tends to
  `‖P({σx*}) b(σ)‖² + ‖P({x*}) b(σ^{-1})‖²`.
- **This covers every Hilbert-space model in which the cocycle is read off fibrewise over `X`,** atomic
  or not, with finite or infinite mass, invariant or not. It is not limited to invariant probability
  measures, as w16 was.

## Survivors

A proper cnd function on `[[X]]`, if one exists, is realized by a cocycle `b` that fails locality
for *every* covariant pair. By the calibration (item 5) that is how Farley's cocycle for `V`
behaves. It has two possible shapes:
- (S1) **No covariant spectral measure on `X`.** For example `ℓ²` of configuration spaces (finite
  subsets of orbits, partitions, the clopen algebra), or Farley-type cube complexes. For `[[X]] ≤ 2V`
  the direct Farley analogue is the brick-chart complex, and that route is dead
  (`brin-thompson-brick-charts-are-not-commensurated`). A configuration model that is not a brick
  model is untested.
- (S2) **A covariant pair with a non-local cocycle.** Locality forces `P(B) b(s) = 0` whenever `s`
  is the identity on a clopen `B`. In particular `P({x*}) b(s) = 0` for every `s` fixing an
  aperiodic `x*`, since such an `s` is the identity near `x*`. A survivor must therefore put
  cocycle mass over points that `s` fixes, for instance through characters of rigid stabilizers.

**Necessary condition, recorded for both sides.** Any proper `ψ` on `[[X]]` has `ψ(s_U) → ∞`
along the swaps, and in particular along any enumeration of `{s_U : U ⊆ E}` for a fixed `E` with
`E ∩ σE = ∅`. This is a proper function on an infinite, locally finite, elementary abelian
2-group, which is always possible. So the condition is not an obstruction. It only says where
the growth must come from.

## What this does not do

- It neither proves nor refutes `full-shift-topological-full-group-is-a-t-menable`.
- It does not cover the class of the parallel w20 node on wobbling groups: cnd functions on the
  whole orbit wobbling group `W(Y)`, which need not be local. That class is killed there by
  strong boundedness of block groups. Together, the two nodes leave only survivors that are
  non-local and do not extend to `W(Y)`.
