---
rg: 2
id: hamming-enemies-escape-finite-hull-pair-loeb-scales
kind: claim
title: In a sofic model of the Theorem E group, flat and finite-hull pieces of the Gamma-commutant commute with sigma(E), so Pauli walls do not extend and every enemy escapes every finite-hull pair scale
distinct_from:
  kt-sofic-monomial-commutant-core-is-normalized: that normalizes the monomial core (permutation centralizer plus invariant diagonal) through Kun--Thom 4.1; this applies Kun--Thom Theorem C to the tensor-square action on pairs and controls Fourier-spread elements, which lie off that core.
  kt-sofic-models-normalize-vn-commutants: that is the open full statement for sofic models; this proves it for every flat or finite-hull piece of the commutant and says exactly where a counterexample must put its mass.
  compressor-enemies-need-trace-invisible-hnn-defects: that kills gap transports of finite carriers and names Hamming transports as survivors; this kills the flat and finite-hull enemies of Hamming (permutation) transports themselves.
  monomial-kazhdan-hnn-is-rf-but-non-rfd-and-not-vfhs-stable: that builds sofic Pauli wall models of P_X semidirect V_T; Part A here proves that no such wall survives in a sofic model of G.
artifacts:
  - research/hamming-enemies-escape-finite-hull-pair-loeb-scales-proof.md
---

**ESTABLISHED (proposed; proof in
`hamming-enemies-escape-finite-hull-pair-loeb-scales-proof`).** It imports
Kun--Thom Theorems C and 4.1 verbatim
(`research/artifacts/kun-thom-2608-06222-verified.md`). The rest is proved in
full.

This answers the wave step on `approximate-collapse-for-kt-compressor`: can a
sofic Pauli wall model of `V_T` be extended to `G` over Hamming carriers? For
permutation carriers it cannot. For the enemies it leaves, the claim gives a
sharp location.

## Setting

- `G = EL_r(R) ⋊ SL_d(Z)` and `Gamma = EL_r(R_+)`, with `q`, `r, d >= 3` as
  in Kun--Thom Theorem E. Both groups are Kazhdan, and `Gamma` is infranormal.
- `E = EL_r(R)`. `t` is in `SL_d(N) \ A_d`, `Lambda = t Gamma t^-1`, and
  `u = e_12(x_1^-1)`.
- `sigma : G -> S_U` is an injective sofic representation with canonical
  trace. It is lifted by maps `phi_n : G -> Sym(Y_n)` and realized by
  permutation matrices in `M = prod_U M_(Y_n)`.
- `R = sigma(Gamma)' ∩ M`. An *enemy* is some `x` in `R` with
  `[x, sigma(u)] != 0`.
- Write an element `x = [x_n]` of `M` as its entry functions
  `f_n(a, b) = (x_n)_(ab)` on `W_n = Y_n × Y_n`. Then
  `||x||_2^2 = lim (1/|Y_n|) sum |f_n|^2`, and `Ad sigma(g)` acts on `f_n` by
  the diagonal (tensor-square) permutation `psi_n(g) = phi_n(g) × phi_n(g)`.

**Admissible pair scales.** A *pair scale* is a sequence of sets
`Z_n ⊆ W_n` with the following properties:

- (Z1) `|psi_n(g) Z_n Δ Z_n| = o(|Z_n|)` for every `g` in `G`;
- (Z2) `|Z_n ∩ (Fix phi_n(g) × Fix phi_n(g))| = o(|Z_n|)` for every
  `g != e`;
- (Z3) the row and column marginals of the uniform measure on `Z_n` are
  uniformly absolutely continuous: for every `eps > 0` there is `eta > 0`
  such that `|Z_n ∩ ((B × Y_n) ∪ (Y_n × B))| <= eps |Z_n|` whenever
  `|B| <= eta |Y_n|`, for `U`-almost every `n`.

A function `f = [f_n]` is *(Z, K)-dominated* if `f_n` vanishes off `Z_n`
and `|f_n| <= K (|Y_n| / |Z_n|)^(1/2)` there.

- `Z_n = W_n` is always a pair scale. The `W_n`-dominated elements are the
  *flat* ones: every entry is `O(|Y_n|^-1/2)`. Examples are the
  Fourier-spread projections, which lie off the monomial core.
- Let `c = [c_n]` be a permutation that commutes with `sigma(G)` in `S_U`.
  Then the graph of `c_n` is a pair scale of size `|Y_n|`. More generally, so
  is any finite union of such graphs.

## Theorem

**A (Pauli walls do not extend).** Let `tau` be a sofic representation of
`Pi_T = P_X ⋊ V_T`, with `X = V_T / Gamma`. Then there is no sofic
representation of `G` in the same `S_U` that agrees with `tau` on `V_T`.
More generally, no sofic representation `rho` of `V_T` extends to a sofic
representation of `G` if it has
`C_(S_U)(rho(Lambda)) != C_(S_U)(rho(Gamma))`. The wall lamps `tau(p_(t x_0))`
witness this inequality.

**B (pair-Loeb collapse).** Let `f` be a vector of the Hilbert ultraproduct
`H = prod_U l^2(W_n, counting / |Y_n|)` that is `psi(Gamma)`-invariant and
`(Z, K)`-dominated for some pair scale `Z`. Then `f` is `psi(E)`-invariant.
In particular, every flat element of `R`, and every element of `R` dominated
by a pair scale, commutes with `sigma(E)`, so it is not an enemy.

**C (where enemies live).** Let `x` be an enemy, and put
`delta = ||[x, sigma(u)]||_2`. Then for every pair scale `Z` and every `K`,

```text
|| x - chi_(Z,K)(x) ||_2  >=  delta / 2 .
```

Here `chi_(Z,K)` is the Lipschitz Schur truncation to `Z` at height
`K (|Y_n|/|Z_n|)^(1/2)` (proof, Section 3). Every enemy therefore has these
properties:

- it keeps 2-norm mass at least `delta/2` on entries of size much larger than
  `|Y_n|^-1/2` (take `Z = W`);
- it is not in the monomial core
  (`kt-sofic-monomial-commutant-core-is-normalized`);
- it does not concentrate, with bounded height, on any pair scale. A pair
  scale is a pair set that is asymptotically `G`-invariant at its own
  density.

What is left is an *infinite-hull wall*: an asymptotically `Gamma`-invariant
pair set of density `m_n / |Y_n|`, with `1 << m_n << |Y_n|` possible, whose
`E`-translates drift off in the Loeb measure of pairs. This is the
infinite-measure coset pattern `G/Gamma` at an intermediate scale. It is the
only place where Kun--Thom Theorem C, which holds only for probability
measures, does not reach.

## Consequences for the extension problem

- Over permutation (Hamming-transport) carriers, the extension of the Pauli
  wall model is impossible (Part A). Any sofic model of `G` whatsoever has
  enemies only of the infinite-hull kind (Parts B and C).
- Part B holds for every sofic representation. So it also covers transports
  through the permutation modules on `Y_n^k` and `k`-subsets. These are
  sofic representations of `G` via `phi_n^(×k)`, and their corners are cut
  by projections commuting with `sigma(G)`.
- Still open are Hamming-type carriers that are genuinely non-permutation:
  representations of `A_m`, with `m` unbounded, that are not corners of
  bounded-arity permutation modules, and non-monomial HS extensions of the
  Pauli models. For these, `approximate-collapse-for-kt-compressor` still
  asks for a statement like Theorem C for infinite-measure (Poisson-type)
  sofic actions, or an enemy of infinite-hull type.
