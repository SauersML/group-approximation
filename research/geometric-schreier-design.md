---
rg: 2
id: geometric-schreier-design
kind: claim
title: Spherical almost actions quantize to a labelled Schreier graph
distinct_from:
  hyperlinear-implies-sofic: that is the group statement; this is a quantization theorem about isometries of a sphere and finite point clouds, whose hypothesis is a mean-square almost action and whose conclusion is a labelled matching. It never mentions groups beyond a finite window, and it would also apply to almost actions that come from no group at all.
  spherical-candidate-hypergraph-quasirandom: that is the probabilistic half — degree and codegree control for the candidate graphs — and says nothing about selecting a matching; this is the whole quantization statement, of which that is one input.
  hypergraph-absorption-schreier-matching: that is the deterministic combinatorial half, taking a quasirandomness package as a hypothesis; this is the analytic statement about unitary tables and spheres that produces such a package in the first place.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Target (Target B of the source dossier).**  For every finite table `T` and
`eps > 0` there are parameters `r > 0`, `N_0`, `delta > 0` such that: if a
unitary table `{U_s}` has normalized-HS multiplicative defect `< delta` and
regular-trace separation `< delta`, then some sufficiently uniform point cloud
`X = {x_1,…,x_N} ⊂ S^{2d-1}`, `N ≥ N_0`, carries labelled perfect matchings
`sigma_s` — each an edge set of the geometric candidate graph
`B_s = { (i,j) : ‖U_s x_i - x_j‖ ≤ r }` — whose word maps satisfy `T` in
Hamming error `< eps`.  The parameters must not depend on `d`.

The hypothesis is exactly what a hyperlinear microstate supplies, by
`hs-defect-is-mean-square-sphere-displacement`: multiplicative defect is
mean-square transport cost, `E_x‖U_gU_hx - U_{gh}x‖^2 ≪ 1`, and regular-trace
separation is macroscopic geometric separation, `E_x‖U_wx - x‖^2 ≈ 2` for
nontrivial tested `w`.  The conclusion is exactly a sofic model of `T`.

**Equivalent transport formulation.**  For a finite word set `W`, the coupling
`gamma_U = (x ↦ (U_h x)_{h∈W})_# mu` on `S^W` has every marginal equal to the
uniform measure `mu`, and for a tested product `gh = k` the multi-marginal
cost `c_{g,h,k}((x_a)) = ‖U_g x_h - x_k‖^2` has `gamma_U`-expectation equal to
the mean-square group-law defect.  So the microstate is a low-cost
multi-marginal *Monge* coupling, and the finite model wanted is a very special
*integral atomic* one: all marginals the same `N`-point set, every coordinate
map a permutation of it.  The claim is therefore an integrality statement for
multi-marginal transport with group-structured costs.

**Why it is worth separating from the amenable paradigm.**
`amenable-hyperlinear-rounds-to-sofic` proves the
desired same-dimension permutation rounding for amenable groups.  Its
extraction indexes an orthonormal block by a finite subset of the *group*, so
nonamenability shows up as a macroscopic boundary term and the technique stops
at amenable groups.  Here the finite model is indexed by a geometric codebook
in a homogeneous space; the boundary is replaced by degree/codegree conditions
on candidate graphs, and there is no Følner term to pay.  Whether that is a
real gain or only a relocation of the difficulty is the content of the claim.

## Attempts

- **Match each generator independently to its geometric nearest neighbours.**
  Fails, and the failure is the central difficulty, not a technicality:
  `sigma_g sigma_h(i)` and `sigma_{gh}(i)` may be two *different* sample points
  that are geometrically almost equal, and Hamming distance charges a full unit
  for that.  Positions round; indices do not.  Any proof must select the
  matchings jointly, with the group law as a hard constraint from the start —
  which is why the live decomposition goes through a hypergraph design
  (`geometric-schreier-design-via-hypergraph-absorption`) rather than through
  per-generator matching theorems.
- **Quote a general multi-marginal transport integrality theorem.**  There is
  none to quote: the Birkhoff miracle for two marginals does not survive to
  higher-dimensional stochastic tensors, and optimal multi-marginal couplings
  are routinely non-Monge and fractional.  So the theorem must use the special
  group-structured cost and the quasirandomness of a spherical codebook; a
  proof that does not use both is almost certainly proving something false.
- **Take the point cloud to be an epsilon-net and the matchings to be
  nearest-point maps.**  Dies for the same index reason as the first attempt,
  and additionally because a net fine enough to control one word is not
  automatically fine enough for products of words: the errors compose
  multiplicatively along the word while the net resolution is fixed.
- **Deferred:** the quantitative kill test is to look for exact orthogonal
  tables — zero defect — for which every finite cloud and every geometric
  shadowing choice has a fixed positive relation defect.  Such an example
  would refute this claim and would be evidence for a genuine integrality gap
  in the sense of `finite-table-quantum-classical-hamming-gap`.
