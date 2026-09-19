---
rg: 2
id: cone-product-laws-break-depth-uniform-atom-transport
kind: claim
title: "Bernoulli cone-product laws refute depth-free atom transport in C(C,Z) ⋊ V: at defect O(√p) the atom μ{χ[0^d] = 0} equals (1−p)^d, so it falls from 1−p to below 1/e at depth ⌈1/p⌉"
distinct_from:
  cantor-cone-phase-atom-comparison-is-depth-uniform: that open claim asks for an absolute K_0 with |μ{χ[U]=0} − μ{χ[[0]]=0}| ≤ K_0 ε for all representations, vectors and proper clopen U; this gives the counterexample, so it refutes that claim as stated and says which hypothesis any true version must add.
  cantor-integer-maps-pair-lacks-relative-property-t: that builds the same random cone-product laws to defeat relative (T) of (G, Y) for Y of unbounded depth, by making the character large on some y in Y; this reads a different quantity off them, the atom at 0 of one cone phase at each depth, and uses a specific non-atomic ξ that makes the atom exactly computable.
  cantor-central-witnesses-have-active-cone-phases: that proves the atom comparison with an error 16|h|_S ε that grows with depth; this shows the growth is genuinely needed for general vectors, so that node's uniform headline cannot be proved without using the absence of 1_C-invariant vectors.
  cantor-central-witnesses-have-long-range-dependence: that bounds the dependence of two cone phases in witnesses with no 1_C-invariant vector; this concerns general almost invariant vectors, all of whose spectral mass is 1_C-invariant.
---

**ESTABLISHED** by `cone-product-laws-break-depth-uniform-atom-transport-proof` (unreviewed).

**Setting.** As in `cantor-cone-phase-atom-comparison-is-depth-uniform`:
- `C = {0,1}^N`, `A = C(C,Z)`, `G = A ⋊ V`;
- `S = S_V ∪ {±1_{[0]}}` with `S_V` any finite generating set of `V`;
- for a unit vector `ξ` in a unitary representation `π`, `ε = max_{s∈S}‖π(s)ξ − ξ‖` and `μ` is the
  `A`-spectral law on `Â = Hom(A, R/Z)`.

Write `N_S` for the largest number of leaves of a tree-pair diagram of an element of `S_V`, and
`c_S = 2·max(1, N_S − 1)^{1/2}`.

**Theorem.** For every `p ∈ (0, 1)` there are a unitary representation `π_p` of `G` and a unit vector
`f_p` with
1. `ε(f_p) ≤ c_S·√p`;
2. `μ_p{χ[0^d] = 0} = (1 − p)^d` for every `d ≥ 1`;
3. `π_p(1_C) f_p = f_p`: all spectral mass lies on `{χ[C] = 0}`.

**Corollary (refutation).** No absolute `K_0` has
`|μ{χ[U] = 0} − μ{χ[[0]] = 0}| ≤ K_0·ε` for all `π`, `ξ` and all proper nonempty clopen `U`. Take
`U = [0^d]` with `d = ⌈1/p⌉`. The left side is `(1−p) − (1−p)^d ≥ 1 − p − e^{−1} ≥ 1/2` once
`p ≤ 1/10`, while the right side is at most `K_0 c_S √p → 0`. So
`cantor-cone-phase-atom-comparison-is-depth-uniform` is false as stated.

**Quantitative form.** Let `F(ε, d)` be nondecreasing in `ε`, with
`|μ{χ[U]=0} − μ{χ[[0]]=0}| ≤ F(ε, d)` for every vector of defect at most `ε` and every `U = [w]`
with `|w| = d`. Then `F(ε, d) ≥ (1 − ε²/c_S²)(1 − exp(−ε²(d−1)/c_S²))`. This follows by taking
`p = ε²/c_S²`. So no bound that is valid for general vectors can compare the cone-phase atoms at
depth much beyond `1/ε²`. The existing telescoping transport gives `O(dε)`, which says something
only at depth `o(1/ε)`. The window between `1/ε` and `1/ε²` is open.

**What this kills and what it leaves.**
- *Killed.* Every depth-free transport argument for cone-phase atoms that is valid for arbitrary
  almost invariant vectors. That includes averaging over the `V`-orbit of `[0]`, fixed-point estimates
  for `U ↦ μ{χ[U]=0}`, and exchangeability along ruler partitions. The counterexample has all of its
  mass `1_C`-invariant, so such an argument cannot tell it from a witness.
- *Invariant.* The atom `μ{χ[0^d] = 0}` counts the event that no proper prefix of `0^d` carries a
  cone factor. A single cone-product law makes that probability decay geometrically in `d`, while
  keeping the defect `O(√p)` at every generator.
- *Left open.* The restricted statement for vectors with no nonzero `π(1_C)`-invariant component,
  which is the only case the downstream class-kills need. If `(G, Z·1_C)` has relative (T) with
  Kazhdan pair `(Q, κ)`, then that restricted statement holds with `K_0 = L/κ`, where `L` bounds the
  `S`-lengths of the elements of `Q`. So refuting it would be progress on
  `cantor-integer-maps-central-direction-has-relative-t`, and proving it must use the central
  spectral hypothesis in the transport step. This matches the obstruction recorded on
  `cantor-integer-maps-central-direction-has-relative-t` (2026-09-18, w8), that a proof must use an
  input separating `z` from `A`.
