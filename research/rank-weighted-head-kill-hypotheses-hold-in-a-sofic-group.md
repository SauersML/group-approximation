---
rg: 2
id: rank-weighted-head-kill-hypotheses-hold-in-a-sofic-group
kind: claim
title: Every hypothesis of the rank-weighted head kill holds in a sofic group whose head survives, so no tracial transcription of it reaches the Jacobson head
distinct_from:
  uniform-finite-support-rank-gap-upgrades-compression-collapse: that is the operator-norm theorem; this shows its hypotheses, strengthened by simplicity and trivial centralizer of the locally finite kernel, do not imply the tracial or sofic conclusion, and locates the failing step at commutant transport.
  affine-finitary-linear-radical-is-the-whole-kernel: that computes D_G(L) = Rad_MF(G) = K for the group used here; this adds the tracial countermodel and the class kill it implies for tracial transcriptions of the rank-weighted head kill.
  ascending-hnn-finitary-linear-family-is-sofic-non-mf: that establishes the group used here as a sofic non-MF group; this reads it as a countermodel to the tracial form of the rank-weighted theorem and draws the consequence for the Jacobson head and the negative-root corner.
  binary-jacobson-el3-rank-radical-is-the-finitary-kernel: that records, inside EL_n(J), that the rank-model transfer reduces to one transport step for the cell's own data; this shows that no argument from the cell's abstract data can supply that step in tracial models, by an external sofic witness.
  jacobson-corner-compressor-hulls-carry-fredholm-index: that kills corner rigid-defect certificates in GL_N(J) by a Fredholm index on the compressor hull; this kills the complementary route, the tracial transcription of rank-weighted transport, and shows the index character is shared with the witness, so the separating invariant is its failure to extend to the ambient group.
  arbitrary-traced-coordinate-transport-fails: that shows faithful traces on infinite coordinates break Kazhdan transport for an exact regular representation; this uses matrix coordinates and a sofic group, so the failure is that of Hilbert-Schmidt approximation itself, not of infinite coordinates.
  ucp-hs-transport-kills-literal-mark: that concerns the central mark of the literal group; this has the head inside an infinite simple locally finite normal subgroup with trivial centralizer, the configuration of the Jacobson head.
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
---

**ESTABLISHED** (route `rank-weighted-head-kill-hypotheses-hold-in-a-sofic-group-proof`).

## Statement

Let `L = Z^3 x| SL_3(Z)` and `alpha(v,g) = (2v,g)`. Let
`V = <L, u | u l u^-1 = alpha(l)> = Z[1/2]^3 x| (SL_3(Z) x Z)` and `X = V/L`. Let
`K = GL_fin(F_2^(X))` (identity outside a finite block of the basis) and `G = K x| V`. This is the
group of `affine-finitary-linear-radical-is-the-whole-kernel` with `m = 2`, where the coset action is
faithful.

**Theorem.** `G` is finitely generated and sofic, and it carries data `(L, v, c, l, d)` with:

1. `L` has property (T), `v L v^-1 <= L`, `c in C_G(L)`, `l in L`;
2. `d = [v c v^-1, l]` is a transvection of `K`, so `d != 1` and `d^2 = 1`;
3. `K` is normal, infinite, simple and locally finite, `C_G(K) = 1`, and `G` has no nontrivial
   finite normal subgroup;
4. `K` is exhausted by finite groups `SL_m(F_2)`, `m >= 3`, each containing `d`, and for every
   finite-dimensional unitary representation `sigma` of each of them
   `dim (Fix sigma)^perp <= 4 rank(sigma(d) - I)`;
5. `K <= D_G(L)`, and every homomorphism from `G` to a norm matrix corona kills `K`;
6. `G` has a trace-preserving embedding into `U(R^omega)`, through permutation models, in which
   `d` has trace `0`, so its moving projection `p_d = (1 - d)/2` has trace `1/2`.

Items 1, 2 and 4 are the hypotheses of `uniform-finite-support-rank-gap-upgrades-compression-collapse`,
and item 3 adds the features of the Jacobson kernel. Item 5 is its conclusion. Item 6 shows the conclusion
fails once "norm matrix corona" is replaced by "tracial ultrapower", "Hilbert-Schmidt model" or
"sofic model".

## Corollary (class kill)

Let the class consist of the tracial transcriptions of the rank-weighted head kill: arguments that derive
the death of a mark in every Hilbert-Schmidt (or sofic) model using only the data in items 1 to 4. Every
member dies, because `G` satisfies all of that data and keeps `d`.

The step where each member dies is **commutant transport**.
- The finite-group lifting, the rank-weighted cutoffs and the weighted null subgroup (Sections 3 and 4 of
  the rank-weighted artifact) all hold exactly in `R^omega`. There the model is a genuine homomorphism,
  and in a head-seeing model `tau(p_d) > 0`, so the weight `r_n / d_n` stays bounded below.
- For the transported vector `pi(c) e`, `L`-centrality after `Ad pi(v)` is equivalent to `d` lying in
  the null subgroup, which is the conclusion itself.
- The operator-norm proof supplies this step from stable finiteness of the norm corona on the
  `d_n^2`-dimensional conjugation spaces. That in turn needs `Ad V_n` to be asymptotically multiplicative
  in operator norm, which a Hilbert-Schmidt model does not provide.

## Consequence for the Jacobson head and the negative-root corner

`jacobson-head-collapses-by-rank-weighted-transport` kills `x_13(Q)` in `EL_5(J)` from exactly the data in
items 1 to 4 (`H = EL_3(J)`, its compressor, its centralizer, `A = SL_fin`, `C = 4`).
- **The route has no tracial form.** No hyperlinear or Hilbert-Schmidt kill of the Jacobson head can be
  derived from that data. Here the Jacobson head means `x_13(q)` in `EL_20(J)`, the Toeplitz survivor
  input of `agent-leavitt-not-bcs-negative-root-corner`.
- **The shared invariant.** Compressors of the corner `EL_3(J) + 1` carry a positive relative index,
  which is a homomorphism on the compressor hull (`jacobson-corner-compressor-hulls-carry-fredholm-index`).
  `G` has the same feature: `[L : vLv^-1] = 8`.
- **The separating invariant is extension of that index.** In `G` the index character extends to all of
  `G`, as the stable-letter exponent `G -> Z`. The soficity proof consumes exactly this: `G` is a split
  `Z`-extension of a locally residually finite group. In `EL_n(J)`, `n >= 3`, the ambient group is
  Kazhdan and perfect, so the character does not extend.
- **What a nonhyperlinearity proof must use.** Any proof that `EL_n(J)` is nonhyperlinear while seeing the
  head must use ambient property (T), or some finer invariant that `G` violates. It must use it neither
  through corner rigid-defect certificates (killed by the Fredholm-index claim) nor through local
  compression-cell data (killed here).
