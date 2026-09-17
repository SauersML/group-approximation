---
rg: 2
id: fpbs-benjamini-schramm-counterexample-exists
kind: claim
title: Some nonamenable Cayley graph has coinciding percolation thresholds
root: true
distinct_from:
  fpbs-fixed-price-one-percolation-kernel: that is the positive statement for nonamenable fixed-price-one groups, the last case of the cost route; this is the negation of the universal goal, and by Lyons any witness for it must lie inside that same class.
  fpbs-product-fibre-collision-loss-vanishes: that is an asymptotic inequality on high-degree products whose truth would refute this claim for that class; this is the existence of a counterexample anywhere.
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/spectral-spike.md
  - research/artifacts/fpbs/exploration.md
---

**OPEN; the negation of `fpbs-benjamini-schramm-universal`.** There exist a
nonamenable finitely generated group `Gamma` and a finite symmetric generating
set `S` with

```text
p_c(Cay(Gamma,S)) = p_u(Cay(Gamma,S)).
```

This node exists because of the graph's refutation convention. A
counterexample is not a route into the universal goal; it is an ESTABLISHED
negation claim, and only when this claim is established does
`fpbs-benjamini-schramm-universal` acquire
`refuted_by: [fpbs-benjamini-schramm-counterexample-exists]`.

**The witness class is pinned down.** By Lyons, arXiv:1109.5418, a finitely
generated group without fixed price one has a nonuniqueness phase on every one
of its Cayley graphs. So any witness here is a nonamenable group **of fixed
price one**: it satisfies the Fixed Price assertion for its own group rather
than contradicting it, and it lies inside
`fpbs-fixed-price-one-percolation-kernel`. Section 5 of the forwarded
2026-09-09 priority assessment draws the operational consequence: proving
fixed price one for one more nonamenable group does not advance the
percolation problem, it only moves the group into the class where the cost
obstruction is silent.

It must also avoid every established positive case:
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness` (nonamenable Gromov
hyperbolic quasi-transitive graphs, and graphs with a nonunimodular
quasi-transitive automorphism subgroup) and `fpbs-sc-choi-seo` (every Cayley
graph of an acylindrically hyperbolic group). It must fail Hutchcroft's L2
boundedness conjecture `fpbs-nonamenability-bounds-critical-connectivity-operator`,
so establishing this claim would refute that conjecture too.

## Attempts

* **Show the collapse scenario is internally consistent** (response 9,
  `spectral-spike.md` Sections 4--7). Assuming `p_c=p_u=c`, the note derives
  what collapse forces: a spectral atom of mass `theta(p)^2` at `1` appearing
  immediately above `c`, and conditional pivotal counts of order
  `n exp(alpha n)` for every `alpha<lambda_0/2`. Section 7 then exhibits a
  monotone FIID partition model on the same nonamenable graph that realizes
  exactly this spectral jump, with explicit finite-`n` formulas and a
  logarithmic-derivative peak of rate precisely `lambda_0/2`. **Why this is
  not a counterexample:** Section 7 says so in its own terms. The partition
  classes are not clusters of the ambient Cayley graph. For every `t` in
  `(0,1)` a selected vertex has all `d` neighbours unselected with probability
  `t(1-t)^d>0`, and ergodicity produces such isolated vertices almost surely;
  they belong to the unique infinite class but are not connected to it through
  edges of the graph. The toy parameter also has threshold zero rather than
  `c>0`, so identifying its logarithmic derivative with a Bernoulli pivotal
  count is an error the note names explicitly.
* **Build a nonamenable graph with no indispensable edges** (response 4,
  `creative-branches.md` Section 1.3; response 8, `exploration.md` Section 1).
  The model `H_epsilon` on `T_{2r} x Z` keeps all vertical edges and each
  horizontal edge with probability `epsilon`; it is connected, bridgeless, and
  has divergent mean replacement-route length. **Where it dies:** it is a
  dependent anisotropic law, not Bernoulli percolation on a Cayley graph, and
  Proposition 1 of `exploration.md` shows it is collectively fragile,
  `p_c(H_epsilon) -> 1` as `epsilon` decreases. It separates route length from
  pivotality; it does not produce coinciding thresholds anywhere.
* **Use a cost-one group directly.** Every group in the archive's
  fixed-price-one families (`fpbs-amen2-fixed-price-one`,
  `fpbs-bounded-exponent-two-groups-fixed-price`, `fpbs-sc-fixed-price-family`,
  `fpbs-tfl-fixed-price`) is admissible as a candidate by the Lyons
  constraint. **Where it dies:** admissibility is not a threshold
  computation. For the explicit small-cancellation family the opposite is
  proved, `fpbs-sc-percolation-family` and `fpbs-ew-window` give an actual
  nonuniqueness interval; and the quantitative cost bound of response 1
  degenerates to `0 <= 0` under threshold equality, so it neither forbids nor
  produces a collapse. No candidate has a proved upper bound on `p_u` matching
  a lower bound on `p_c`.
* **Reasoning from the two endpoint facts.** Absence of an infinite cluster at
  `p_c` and absence of a unique cluster at `p_u` are both known and both
  remain true when `p_c=p_u`. Section 8 of `spectral-spike.md` records this
  after a literature check: no implication about strictness may be inferred by
  combining them.
* **Kazhdan projection applied to the two-point function** (sw-029,
  2026-09-17, inverter lane). Assume a witness `Gamma` has property (T), with
  Kazhdan constant `kappa` for `S`. Then `phi_p(x)=tau_p(o,x)` is a normalized
  positive definite function on `Gamma`: its GNS vector is `e_{C(o)}` in
  `L^2(P; l^2(clusters))`. Its invariant mean is
  `W(p)=M(phi_p)=||P_inv xi||^2`. By ergodicity, indistinguishability of
  infinite clusters and the Alaoglu--Birkhoff mean ergodic theorem,
  `W(p)=theta(p)^2 1{uniqueness at p}`. Under (T), `W(p)=s_p(p_0)`, where `p_0`
  is the Kazhdan projection in `C*(Gamma)` and `s_p` is the state defined by
  `phi_p`. Since `phi_p` is pointwise left-continuous in `p`, `W` is
  left-continuous. This yields two things. (a) Either `p_c=p_u`, or there is
  no uniqueness at `p_u`. (b) The quantitative bound
  `1-W(p) <= 2(1-p)/kappa^2`, so `p_u <= 1-kappa^2/2`. Calibration: planar
  hyperbolic surface groups have uniqueness at `p_u`, and they lack (T), as
  they must. **Where it dies:** (a) is the Lyons--Schramm conclusion for
  Kazhdan groups, and `fpbs-pu-nonuniqueness-cannot-separate` already shows
  that no endpoint statement of the form "no unique cluster at `p_u`" can force
  strictness. The exact failing step is the continuity of `W` at `p_c` under
  collapse. For a unimodular nonamenable transitive graph `theta(p_c)=0`
  (BLPS), and `theta` is right-continuous, so `W(p)=theta(p)^2 -> 0 = W(p_c)`
  as `p` decreases to `p_c`. Thus `W` is continuous at `p_c`, and the
  one-sided continuity supplied by the Kazhdan projection has nothing to
  contradict. The same computation gives `M=theta^2 1{U}` for the invariant
  mean of any positive definite function `P(o ~ x)` built from an ergodic
  invariant random partition with indistinguishable infinite classes, sprinkled
  couplings `C_q(o)` included. So the whole class "invariant means,
  equivalently Kazhdan projections, of cluster two-point functions" is silent
  on collapse. A contradiction would have to come from a non-mean
  functional, one that sees `tau_p` outside the trivial isotypic component,
  such as the spectral mass of `phi_p` near but not at the trivial
  representation.
* **Large amenable factor closes the gap (heretic lane, swarm-0917).**
  **Candidate class.** Nonamenable `H` times an amenable `B` with a large
  generating set. Here `p_u/p_c -> 1` as `d_B -> infinity`: for `B = Z^k`, use
  `p_u <= p_c(Z^k)`, which follows from Lyons–Schramm and Harris, together with
  `p_c >= 1/(d-1)`. So the gap plausibly closes in the limit.

  **Obstruction** (`fpbs-nb-spectral-deficit-obstruction`, ESTABLISHED). Every
  counterexample has percolation deficit `D(G) = d-1-1/p_c` at least the
  nonbacktracking spectral deficit `d-1-sigma(max(||A||,2 sqrt(d-1)))`. On
  `H □ B` this is at least `d_H - ||A_H||`, whatever `B` and `S_B` are. So the
  gap closes only if `p_c` leaves mean-field by an order-one amount in the
  reciprocal, fixed by `H`. The spectral side never closes it.

  **Where the kill stops.** The missing `p_c` asymptotic is
  `fpbs-product-amenable-factor-mean-field-deficit` (OPEN). The same criterion
  gives new unconditional windows on groups with a free quotient and a few
  kernel generators, for example `Z^2 ⋊ F_5`.

  **Surviving class for a counterexample.** Graphs with order-one deficit
  `D >= d(1-rho)(d-1)/(d-2)`, meaning dense short cycles relative to degree.
  This is where "amenable-like local structure" must live.
* **Fibre-renormalized certificate: the factor's own cycles are harmless
  (heretic lane, swarm-0917 w5, 2026-09-17).**

  **What was wrong with the wave-4 route.** The deficit kill needs
  `D(G_k) -> 0`, and the factor's own short cycles spoil it. For
  `F_2 × Cay(Z,{±1..±k})`, an exact Collatz–Wielandt bound on
  no-backtrack, no-triangle walks
  (`experiments/fibre-renormalized-certificate-2026-09-17/saw_triangle_deficit.py`)
  gives `D(G_k) >= 0.563, 0.619, 0.649, 0.681` for `k = 16, 24, 32, 48`. These
  exceed both `delta_H = 0.536` and `Delta(G_k)`. So spread-out factors have
  order-one deficit, and the unrenormalized criterion cannot certify them,
  whatever `p_u` is.

  **New invariant** (`fpbs-fibre-renormalized-nonbacktracking-certificate`,
  ESTABLISHED). Contract the fibre clusters of an infinite normal `N` into
  their susceptibility `chi_N` and weight quotient backtracks by
  `(chi-1)/chi`. A Woodbury reduction on directed quotient edges, together
  with Pringsheim, gives
  `E|C(o) ∩ qN| < infinity` whenever `1 + gamma(d'-gamma)u^2 > u||A_X||` on
  `[0, p chi]`, and hence `p <= p_u`. On `H □ B` the only data from `B` is
  `chi_B`. A counterexample must then have **collision loss**
  `L_p = d_H - 1/chi - 1/(p chi) >= delta_H - 1/chi + p(d_H - 1/chi)`, or
  `p(d_H - gamma) > 1/(p chi)` with `||A_H||^2 >= 4 gamma(d_H - gamma)`, at
  every `p ∈ (p_c(G), p_c(B))`.

  **Surviving class.** Products in which fibre clusters, displaced by
  `H`-steps, re-collide at a rate of at least `delta_H`. For high-degree
  factors this means a near-critical fibre bubble (`p nabla_B` of order one),
  whether or not `B` has triangles.

  **Last missing prerequisite:** `fpbs-product-fibre-collision-loss-vanishes`
  (OPEN). Its failure modes are a vanishing margin `p_c(B) - p_c(G)` and the
  absence of a lace expansion on `G_k`.
