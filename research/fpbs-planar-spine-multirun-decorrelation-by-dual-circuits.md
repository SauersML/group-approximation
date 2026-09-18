---
rg: 2
id: fpbs-planar-spine-multirun-decorrelation-by-dual-circuits
kind: claim
title: For the supercritical Z^2 percolation spine the multi-run coverage decorrelation K_n is bounded uniformly in n and in the pattern on every geodesic path, by a product over path vertices of 1/max(theta, 1-psi(delta/2)) with psi the dual circuit tail; hence Br/TJT <= C(p') for all r and n on geodesic paths, and the constant depends on the fold profile at the dual correlation scale, not on theta alone
distinct_from:
  fpbs-path-bridge-ratio-untilted-coverage-decorrelation: that proves K <= 2/theta only for patterns with one run on each side, by a last-exit union bound, and leaves the multi-run K open; this bounds K over all patterns on geodesic paths by splitting dual circuits at the bisector of the cut and using Harris twice
  fpbs-hairpin-paths-break-uniform-bridge-ratio: that bounds K on paths by the fold width for finite-range environments (Theorem 3) and conjectures a weak fold effect for the percolation spine (Conjecture 5); this proves the percolation-spine analogue of Theorem 3, with exponential decay of the dual connection in place of finite range, and gives the matching exponential-in-fold upper bound on hairpins
---

**ESTABLISHED (strict reduction; the fixed-density part of the path Br
route).** Proof in
`fpbs-planar-spine-multirun-decorrelation-by-dual-circuits-proof`.
**The `theta -> 0` scaling `K <= C/theta`: still OPEN**; the constant proved
here is of order `theta^{-c xi}`, with `xi` the dual correlation length.

**Setting.** As in `fpbs-path-bridge-ratio-untilted-coverage-decorrelation`.
`omega` is Bernoulli(`p'`) bond percolation on `Z^2`, `p' > 1/2`. The
spine `Z` is the set of open edges with an endpoint in the infinite cluster,
and `theta = theta(p')`. The volume is a chordless path `x_0 ... x_n` with
edges `e_i = x_{i-1} x_i`. For a split edge `e_k` and a pattern
`S ⊆ Lambda \ {e_k}`, `S^-` is the part before `e_k` and `S^+` the part
after, and

```text
K_n(Z) = max_k max_S  P(S ⊆ Z) / ( P(S^- ⊆ Z) P(S^+ ⊆ Z) ).
```

Put `U^-_k = {x_0,...,x_{k-1}}` and `U^+_k = {x_k,...,x_n}`. For a vertex
`x` of the path let `delta_k(x)` be the Euclidean distance from `x` to the
other side (to `U^+_k` if `x in U^-_k`, to `U^-_k` otherwise). The dual
lattice is open where the primal is closed, so it is Bernoulli(`1-p'`),
which is subcritical. Let

```text
psi(rho) = P_{1-p'}( some dual-open circuit surrounds 0 and has a point at distance >= rho from 0 ).
```

By sharpness of the phase transition on `Z^2` (Kesten; Menshikov;
Aizenman--Barsky), `psi(rho) <= C_1 e^{-c_1 rho}` with `c_1 = c_1(p') > 0`.

**Theorem 1 (multi-run decorrelation by dual circuits).** For every
`p' > 1/2`, every chordless path, every split `k` and every pattern `S`,

```text
P(S ⊆ Z) <= P(S^- ⊆ Z) P(S^+ ⊆ Z) / ( Theta^-_k(S) Theta^+_k(S) ),
Theta^±_k(S) >= prod_{x in V(S^±)} max( theta, 1 - psi(delta_k(x)/2) ).
```

So

```text
log K_n(Z) <= max_k sum_{x in path} ell(delta_k(x)),     ell(rho) = -log max(theta, 1 - psi(rho/2)).
```

*Mechanism.* In the plane, a run of `S` declared open misses the infinite
cluster exactly when a dual-open circuit surrounds it, and dual circuits
cannot cross declared-open edges. Split the dual edges by the Euclidean
bisector of `U^-_k` and `U^+_k`, into `L` (closer to `U^-_k`) and `R`
(closer to `U^+_k`). The event "no circuit inside `L` surrounds an `S^-`
vertex" contains the event for the whole pattern, depends only on `L`, and
does not see the `S^+` edges at all. The two sides are then independent.
Returning from the half-plane event to the true one-sided event costs only
the circuits that leave `L`. By Harris, this costs at most the product of
the probabilities that no such circuit exists, and a circuit around `x`
that leaves `L` reaches distance `delta_k(x)/2`.

**Corollary 2 (geodesic paths; the multi-run kernel at fixed density).** On
every monotone (geodesic) lattice path in `Z^2`,
`delta_k(x_{k-j}) >= j/sqrt 2` and `delta_k(x_{k-1+j}) >= j/sqrt 2`. Hence

```text
K_n(Z) <= C(p') := prod_{j >= 1} max( theta, 1 - psi(j/(2 sqrt 2)) )^{-2} < infinity,
```

uniformly in `n`, in the split and in the pattern. With Theorem 1 of
`fpbs-path-bridge-ratio-untilted-coverage-decorrelation`, for every
`r in (0,1)`:

```text
Br/TJT <= C(p'),        D_n >= (1 - 2/n)/C(p').
```

This proves `inf_n D_n > 0` on geodesic paths for every supercritical spine,
which is the path form of the Br route in
`fpbs-percolation-spine-path-bridge-ratio-criterion` (Corollary 2 there). The
earlier support for it was numerical.

**Corollary 3 (fold profile).** Let `rho_0 = rho_0(p')` be the least radius
with `psi(rho/2) <= 1/2` for all `rho >= rho_0`. Put
`N_k(rho) = #{x : delta_k(x) <= rho}`. Then

```text
log K_n(Z) <= max_k [ N_k(rho_0) log(1/theta) + 2 sum_{delta_k(x) > rho_0} psi(delta_k(x)/2) ].
```

This is the percolation analogue of Theorem 3 of
`fpbs-hairpin-paths-break-uniform-bridge-ratio`. The finite range `R` is
replaced by the dual decay scale `rho_0 ≍ xi(p')`, and the fold width by the
number of path vertices within `rho_0` of the other side of the cut. On the
hairpin `H_m`, split at the first turn, `N(rho_0) ≈ 2m`, so the bound is
`log K <= O(m) log(1/theta)`. That is the same order as the linear growth
measured in Conjecture 5 there, so the bound is attained in order, although
the measured slope is much smaller. In particular, Theorem 1 rules out
super-exponential fold effects for the spine.

**Scope.**

* *Box proxies.* The proof is unchanged when the target is the boundary of a
  box `B` containing the path (the proxies of `kdecor.c` and `brratio.c`):
  there, "not joined to `∂B`" means "surrounded by a dual circuit inside
  `B`", and `psi` is replaced by its restriction to circuits inside `B`,
  which is smaller. At the critical proxies (`p' = 1/2`, target at distance
  `M`), circuits have diameter at most `2M`. So the bound is finite for each
  `M`, but it is not uniform as `M -> infinity`.
* *Other planar lattices.* The proof uses only planar duality and the
  summability of the dual circuit tail. It applies verbatim to a
  quasi-transitive planar lattice with its planar dual, at any `p'` for
  which dual-open clusters are a.s. finite with exponentially decaying
  radius, with `delta` measured in the graph metric of the lattice together
  with its dual. For a nonamenable planar lattice this is the regime
  `p' > p_u = 1 - p_c(G*)` (Benjamini--Schramm), by sharpness on the dual.
* *Not claimed.* `K <= C/theta` as `p' -> 1/2`. Theorem 1 has `C(p')` of
  order `theta^{-c rho_0}`, since every vertex within `rho_0` of the cut is
  charged `1/theta`. The measurements give `K theta <= 0.93`. The loss is the
  Harris step: it treats the circuits that leave `L` around different
  vertices near the cut as independent obstacles, while in fact they
  are nested. Non-planar graphs are also not covered: there, "joined to
  infinity or of small radius" is not a monotone event, and the Harris step
  has no analogue.

**What this moves.** The path-volume Br route is now proved at every fixed
supercritical density on geodesic paths, for all `r`, with a constant that
depends on the fold profile at the dual correlation scale. The open inputs
of the route are exactly two:

* the scaling of `C(p')` as the spine is born (`theta -> 0`, where `rho_0`
  diverges), which the gate integral `∫ C(r) dr` needs;
* passing from paths to the volumes the gate uses.

A sharper nested-circuit decomposition near the cut is the natural way to
attack the first.
