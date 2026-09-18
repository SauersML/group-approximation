---
rg: 2
id: gaussian-theorem-c-for-ad-sigma-is-equivalent-to-ccr
kind: claim
title: Theorem C for the Gaussian suspension of Ad sigma is equivalent to commutant normalization, so the Poisson-type Theorem C is not an easier statement
distinct_from:
  hamming-enemies-escape-finite-hull-pair-loeb-scales: that applies Theorem C to finite-measure pair scales and leaves the infinite-hull walls; this shows that the natural infinite-measure (Gaussian or Poisson suspension) form of Theorem C that would kill those walls is equivalent to the normalization statement itself.
  kt-sofic-models-normalize-vn-commutants: that is the open normalization statement for sofic models; this proves it equivalent to Theorem C's conclusion for the Gaussian suspensions of the models' conjugation representations, and sufficient that those suspensions are factors of sofic actions.
  kun-thom-nonsofic-wreath: Corollary D there is the special case in which the enemy's cyclic representation is the quasi-regular representation on G/Gamma, where the Gaussian suspension is the generalized Bernoulli shift with Gaussian base.
  hyperlinear-action-distills-to-stabilizer-coset-bernoulli: that passes hyperlinearity from an action to a coset Bernoulli shift; this passes an enemy of a matrix model to a Gaussian action that violates Theorem C's conclusion, with no hyperlinearity claim.
  zero-entropy-compressors-preserve-fixed-algebra: that proves the fixed-algebra conclusion for zero-entropy actions; combined with this node, any enemy yields a Gaussian action in which the compressor has positive entropy on the Gamma-fixed algebra.
artifacts:
  - research/gaussian-theorem-c-for-ad-sigma-is-equivalent-to-ccr-proof.md
---

**ESTABLISHED (proposed; proof in
`gaussian-theorem-c-for-ad-sigma-is-equivalent-to-ccr-proof`).** It imports
Kun--Thom Theorem C verbatim
(`research/artifacts/kun-thom-2608-06222-verified.md`) and the standard Wiener
chaos decomposition of Gaussian actions. Everything else is proved in full.

This answers the wave step on `approximate-collapse-for-kt-compressor`
opened by `hamming-enemies-escape-finite-hull-pair-loeb-scales`: can a
Theorem C for infinite-measure (Poisson-type) sofic actions kill the
infinite-hull walls? The natural form of that statement turns out to be
*equivalent* to the normalization it was meant to prove. The equivalence holds
for every trace-faithful carrier, so it also covers the non-permutation `A_m`
carriers.

## Setting

- `Gamma < G` is infranormal, `Gamma` and `G` are Kazhdan, and `N` is the
  normal closure of `Gamma` in `G`. At the Theorem E pair, `N ⊇ E = EL_r(R)`
  (`hamming-enemies-escape-finite-hull-pair-loeb-scales-proof`, Lemma 0).
- `sigma : G -> U(M)` is a homomorphism into `M = prod_U M_(d_n)` with
  `tr sigma(g) = 0` for `g != e` (trace-faithful). It is lifted by maps
  `sigma_n`. `C_sigma = sigma(Gamma)' ∩ M`. An *enemy* is an element of
  `C_sigma` that `Ad sigma(N)` does not fix (at the Theorem E pair, one that
  does not commute with `sigma(E)`). There is no enemy exactly when
  `sigma(G)` normalizes `C_sigma`, and then `C_sigma = sigma(N)' ∩ M`. In that
  case `sigma(t)` normalizes `C_sigma` and (CCR) holds for `sigma`.
- `pi_sigma` is the orthogonal representation `Ad sigma` on the real Hilbert
  space `L^2(M)_sa`. For a separable closed `G`-invariant subspace `K`,
  `G ↷ (Omega_K, mu_K)` is its Gaussian action (a p.m.p. action on a standard
  space).
- `sigma^(⊗k) = [sigma_n^(⊗k)]` maps `G` into `M_k = prod_U M_(d_n^k)`. It is
  again trace-faithful, since `tr(a^(⊗k)) = tr(a)^k`. If `sigma` is a sofic
  representation, so is `sigma^(⊗k)`: it is the permutation representation
  on `Y_n^k`.

"*Theorem C's conclusion holds for* `G ↷ X`" means that `L^∞(X)^Gamma` is
`G`-invariant.

## Theorem

**(1) Enemies make Gaussian actions that break Theorem C.** Let `x` be an
enemy of `sigma`. Then some self-adjoint enemy `x_0` exists, and for
`K_0 = closed span of pi_sigma(G) x_0` the Gaussian action `Omega_(K_0)` fails
Theorem C's conclusion. So `Omega_(K_0)` is not sofic and is not a factor of
any sofic p.m.p. action of `G`.

**(2) Sufficient condition.** If, for every self-adjoint `x` in `C_sigma`, the
Gaussian action of `K_x` is a factor of a sofic p.m.p. action, then `sigma`
has no enemy. In particular `sigma` then satisfies (CCR).

**(3) Exact equivalence.** For a trace-faithful `sigma` the following are
equivalent.

- (a) Theorem C's conclusion holds for `Omega_K` for every separable
  `G`-invariant `K ⊆ L^2(M_j)_sa` and every `j >= 1`, with `G` acting through
  `Ad sigma^(⊗j)`.
- (b) `sigma^(⊗k)` has no enemy for every `k >= 1`.

**(4) Class form.** Let `S` be a class of trace-faithful representations of
`G` closed under tensor powers, for example all sofic representations or all
trace-faithful unitary ones. Then every `sigma` in `S` normalizes
`C_sigma` if and only if every Gaussian suspension of every `Ad sigma`, for
`sigma` in `S`, satisfies Theorem C's conclusion.

## What this settles

- **The Poisson-type Theorem C is the wall, not a lever.** For a sofic
  `sigma`, `Ad sigma` is the Koopman representation of the infinite Loeb
  measure `counting/|Y_n|` on pairs (equation (2.2) of the Hamming node). Its
  Gaussian suspension has the same Fock space as the Poisson suspension, so
  it is the Poisson-type p.m.p. action attached to the infinite-hull walls.
  By (4) with `S` = sofic representations, "Theorem C holds for these
  Poisson-type actions" is *equivalent* to
  `kt-sofic-models-normalize-vn-commutants`. No proof of the infinite-measure
  analogue can avoid proving the normalization itself.
- **The obstruction has an exact step.** Kun--Thom's proof of Theorem C
  consumes a Păunescu model of `L^∞(X) ⋊ G`: diagonal functions permuted by
  permutation matrices. Any argument of that type for `Omega_(K_x)` must first
  build such a model of the Gaussian suspension of the enemy's cyclic
  representation. By (1), that model cannot exist when `x` is an enemy. So
  the missing input is exactly **soficity of Gaussian suspensions of
  conjugation representations**, and (2) shows it would suffice.
- **Calibration.** If the cyclic representation of the enemy is the
  quasi-regular representation on `G/Delta` with `Gamma ≤ Delta` and
  `N` not contained in `Delta`, then `Omega` is the generalized Bernoulli
  shift `N(0,1)^(G/Delta)`, and (1) recovers Kun--Thom Corollary D (Gaussian
  base) for it. The theorem proves nothing false: the Bernoulli shift of `G`
  is sofic, and `l^2(G)` has no nonzero `Gamma`-invariant vector.
- **Non-permutation carriers.** (1) and (3) need only trace-faithfulness. An
  enemy on an `A_m` carrier, or on any hyperlinear model, would give a
  Gaussian action of `G` violating Theorem C's conclusion. By
  `zero-entropy-compressors-preserve-fixed-algebra`, some compressor would
  have positive entropy on its `Gamma`-fixed algebra. An enemy
  construction must therefore produce positive-entropy Gaussian dynamics of
  `t` on a `Gamma`-fixed Gaussian factor. That is a concrete target for the
  flexible side.

## What stays open

Whether the Gaussian suspension of `Ad sigma`, for a sofic `sigma`, is a
factor of a sofic action. The natural row model (the Poisson process on each
row of `Y_n × Y_n`, read on `Y_n` itself) is `phi_n`-equivariant only if the
marked pairs are unions of `psi_n(G)`-orbits. It then sees an element only
along graphs of permutations that commute with `sigma(G)`, which are pair scales
(Part B of the Hamming node). So that model reproduces the finite-hull theorem
and nothing more. This is a heuristic remark, not a proved exclusion.
