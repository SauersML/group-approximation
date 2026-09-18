---
rg: 2
id: planted-lifts-defeat-hilbert-level-gaussian-soficity
kind: claim
title: Planted lifts put the quasi-regular representation on G/Gamma into the equivariant Hilbert ultraproduct of every sofic approximation, so Gaussian soficity of Ad sigma must use marginal uniform integrability
distinct_from:
  gaussian-theorem-c-for-ad-sigma-is-equivalent-to-ccr: that reduces normalization to soficity of Gaussian suspensions of cyclic parts of Ad sigma on L^2(M); this shows that the Hilbert-level version of that soficity (for all asymptotically equivariant vectors of the lifted permutation representation) is false at every sofic sigma of the Kun-Thom group, and locates the true statement on the canonical marginally uniformly integrable part.
  hyperlinear-action-distills-to-stabilizer-coset-bernoulli: that manufactures the Gaussian Bernoulli shift over G/Delta from a genuine action with a set of stabilizer Delta; this manufactures the quasi-regular representation on G/Gamma inside the Hilbert ultraproduct of any sofic approximation by a Hamming-null change of lift, with no action at all.
  hamming-enemies-escape-finite-hull-pair-loeb-scales: that sorts enemies by pair scales and leaves the infinite-hull wall; this proves that the null-scale (planted) part of the pair space realizes the forbidden coset dynamics for every sigma and is orthogonal to L^2(M), so enemies can live only on the marginally uniformly integrable part.
  zero-entropy-compressors-preserve-fixed-algebra: that says an enemy forces positive compressor entropy on a Gamma-fixed Gaussian factor; this realizes such positive-entropy dynamics at every sigma, but only on vectors orthogonal to L^2(M).
artifacts:
  - research/planted-lifts-defeat-hilbert-level-gaussian-soficity-proof.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**ESTABLISHED (proposed; full proof in
`planted-lifts-defeat-hilbert-level-gaussian-soficity-proof`).** The proof
imports Kun--Thom Theorem C verbatim
(`research/artifacts/kun-thom-2608-06222-verified.md`). It also uses
standard facts: Gaussian actions, the multivariate central limit theorem, and
closure of Păunescu-sofic actions under factors, products and weak
containment (Part (4) uses the last one only). Everything else is proved.

This is the obstruction side of the wave step on
`approximate-collapse-for-kt-compressor` left by
`gaussian-theorem-c-for-ad-sigma-is-equivalent-to-ccr`: *is the Gaussian
suspension of `Ad sigma` a factor of a sofic action?* The natural way to try
this is "Gaussian of a sofic representation". It builds microstates for a
Gaussian action from vectors in the Hilbert ultraproduct of the lifted
permutation representations that are asymptotically equivariant. That method
is **false** here, and this node says exactly where.

## Setting

- `Gamma < G` is infranormal and not normal, `Gamma` and `G` are Kazhdan, and
  `N` is the normal closure of `Gamma`. The Theorem E pair is the main case.
- A *lift* is a sequence `s = (s_n)` with `s_n : G -> Sym(Y_n)` and
  `|Y_n| -> ∞`. It defines a sofic representation `sigma_s : G -> ∏_U Sym(Y_n)`
  modulo normalized Hamming-null sequences, and `sigma_s` is assumed to be a
  trace-faithful homomorphism. Two lifts with the same `sigma` are *equivalent*.
- `H_n = L^2(M_(Y_n), tr)` is the pair space. It is `ℓ^2(Y_n × Y_n)` with
  weight `1/|Y_n|`, and `s_n(g)` acts on it by `Ad`, that is, by the diagonal
  permutation of pairs. `H = ∏_U H_n` is the Hilbert ultraproduct.
  `H^eq(s)` is the closed subspace of `ξ` with
  `[Ad s_n(gh) ξ_n] = [Ad s_n(g) Ad s_n(h) ξ_n]` for all `g, h`. On `H^eq(s)`,
  `Ad s` is an orthogonal representation of `G`. `L^2(M) ⊂ H^eq(s)` for every
  lift, where `M = ∏_U M_(Y_n)` and `Ad s` restricts to `Ad sigma`.
- `ξ ∈ H` is *marginally uniformly integrable* (MUI) if its row masses
  `r_n(a) = Σ_b |ξ_n(a,b)|^2` and column masses `c_n(b)` are uniformly
  integrable over the uniform probability measure on `Y_n`, along `U`.
- `K_sof` is the class of orthogonal representations weakly contained in the
  Koopman representation `L^2(X)` of some sofic p.m.p. action `G ↷ X`.
- For `x ∈ M`, `K_x` is the closed span of `Ad sigma(G) x` in `L^2(M)`.

## Theorem

**(1) Planting.** Let `s` be any lift, `Omega` any countable `G`-set and
`m ≤ ∞`. There is an equivalent lift `s'` (so `sigma_(s') = sigma_s`, and `M`,
`L^2(M)` and `Ad sigma` do not change) and a `G`-equivariant isometry
`V : ℓ^2(Omega)^(⊕m) -> H^eq(s')`. It changes `s_n(g)` on at most
`2|P_n|` points, where `|P_n|/|Y_n| -> 0`. The image of `V` is supported on
rows and columns in `P_n`.

**(2) The Hilbert-level Gaussian principle is false.** Consider the statement

> (HGS) for every lift `s` of a sofic `sigma` and every separable
> `Ad s`-invariant subspace `K ⊂ H^eq(s)`, the Gaussian action of `K` is
> sofic (or a factor of a sofic action).

HGS fails at every sofic `sigma` of `G`. Take `Omega = G/Gamma` in (1). The
Gaussian action of `ℓ^2(G/Gamma)` is the Gaussian Bernoulli shift
`N(0,1)^(G/Gamma)`. Its coordinate at the base coset is `Gamma`-invariant and
not `N`-invariant, so it violates Theorem C's conclusion. It is not a factor
of a sofic action, which is also Corollary D. The same holds with `ℓ^2(Y_n)`
in place of the pair space.

So HGS is not a lever. For the Kun--Thom group it is equivalent to "`G` has
no sofic approximation", which is the flagship itself.

**(3) The enemy dynamics exists at every sigma, but is always orthogonal to L^2(M).**
In the planted lift `s'`, the Gaussian action of `V(ℓ^2(G/Gamma))` is
`N(0,1)^(G/Gamma)`, and its `Gamma`-fixed algebra `F_Gamma` is not
`G`-invariant. By (ZE3) of `zero-entropy-compressors-preserve-fixed-algebra`,
some compressor `s` (with `s Gamma s^(-1) ≤ Gamma`) does not have `F_Gamma`
inside its Pinsker algebra. At the Theorem E pair this is one of the
elementary substitutions `s_ij`. This is exactly the positive-entropy
compressor dynamics that the zero-entropy node asks of an enemy. The
brief's enemy-side construction therefore exists for *every* `sigma`. But
every planted vector (supported on rows and columns in a set of density
`o(1)`) is orthogonal to every MUI vector, and `L^2(M)` is MUI. So no enemy
comes out of planting.

**(4) The canonical part and the sharp remaining statement.**

- (a) `H^eq_MUI`, the MUI vectors of `H^eq(s)`, form a closed invariant
  subspace. It is the same for all lifts of `sigma` (lift-independent), and
  it contains `L^2(M)`.
- (b) Gaussian criterion: the Gaussian action of `K` is a factor of a sofic
  action iff `K ∈ K_sof` iff `K` embeds in the Koopman representation of a
  sofic action.
- (c) Representation Theorem C: if `π ∈ K_sof` then `π^Gamma ⊆ π^N`.

Hence:

- CCR for `sigma` follows from `K_x ∈ K_sof` for every
  `x ∈ sigma(Gamma)' ∩ M`. By (b), this is the Gaussian soficity input of the
  w9 node, rewritten as a statement about representations.
- By (2), that membership **cannot** be proved from equivariance alone. A
  proof must use marginal uniform integrability, which is lift-independent,
  or the operator-norm bound.
- *Flat* vectors are those whose entries `√|Y_n| ξ_n(a,b)` are uniformly
  integrable for the uniform measure on `Y_n²`. Flat vectors are MUI, and
  their cyclic representations lie in `K_sof` through the Loeb pair action.
  So the open part is carried by MUI vectors that are not flat: the
  mesoscopic, infinite-hull part.

**(5) Sharpness of planting.** Planting only ever works at density `o(1)`.
For any lift, the proportion of `a ∈ Y_n` fixed by `s_n(Gamma)` (on a
generating set) but moved by `s_n(u)`, for a fixed `u ∈ N`, tends to `0`. This
is Theorem C for the Loeb action of `s`. A positive-density planting of
`G/Gamma` would produce a diagonal enemy in `L^∞(Y) ⊂ M`.

## What is killed, and the exact failing step

**Killed:** every argument that proves soficity of the Gaussian suspension of
`Ad sigma`, or of any subrepresentation, through one of the following, and
uses nothing else about the vectors:

- the Hilbert ultraproduct of the permutation representations `ℓ^2(Y_n)` or
  `ℓ^2(Y_n²)`;
- Gaussian microstates `R^(Y_n)` driven by `s_n`;
- "Gaussian of a sofic representation";
- ultraproducts of Hayes-type Gaussian models over the sofic approximation.

The failing step is the inference

> `ξ ∈ H^eq(s)` asymptotically equivariant `⟹` Gaussian(`K_ξ`) admits sofic
> microstates.

It fails already for the planted `ξ = [√|Y_n| δ_(p_n,p_n)]`, which is exactly
equivariant for `s'`.

**Survives:** arguments that use MUI or the operator-norm bound. The row
model of the w9 node and the Loeb pair action are of this type, and they
reach only the flat or finite-hull part.

## Status of the wave step

The missing input is not decided. It is sharpened to

> (MUI-K) for sofic `sigma` of the Kun--Thom group, `K_x ∈ K_sof` for
> every `x ∈ sigma(Gamma)' ∩ M`,

or the weaker

> (MUI-C) every `Gamma`-invariant vector of `H^eq_MUI` is `N`-invariant.

(MUI-K) implies (MUI-C) on `L^2(M)` by (4c), and (MUI-C) implies CCR. The
non-MUI analogue of (MUI-C) is false by (1)–(2). No enemy can
be built by planting, since (3) and (5) exclude both density regimes.
