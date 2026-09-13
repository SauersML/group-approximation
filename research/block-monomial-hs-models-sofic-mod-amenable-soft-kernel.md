---
rg: 2
id: block-monomial-hs-models-sofic-mod-amenable-soft-kernel
kind: claim
title: A block-monomial HS model is sofic modulo its soft kernel, which is amenable for bounded blocks and abelian for monomials
distinct_from:
  signed-monomial-tracial-images-are-sofic: that divides by the tracial identity kernel of +-1-labelled models and needs no group structure on it; this divides by the larger permutation kernel of models with arbitrary continuous U(k) labels and proves that kernel is an amenable normal subgroup.
  uniformly-discrete-block-monomial-images-are-sofic: that needs finite label groups with a uniform character gap so that HS and Hamming kernels coincide; this assumes no gap and instead identifies what the gap-free soft part can be.
  nonsofic-block-monomial-images-force-soft-kernel-labels: that says a nonsofic finite-label image must carry HS-null but literally active labels; this says, for bounded continuous blocks and regular trace, that the whole soft part is an amenable normal subgroup, so it is invisible to groups with trivial amenable radical.
  diagonal-normalizer-rigidity: that rounds an approximate normalizer of a full masa to a monomial and transfers multiplicativity to the permutation part; this handles the phases and the trace, which that transfer leaves unresolved.
  block-monomial-coordinate-collapse: that uses the same Hamming comparison to send block-monomial models of the Kun--Thom wreath with coordinate lamps to sofic actions; this identifies the kernel of the permutation skeleton for an arbitrary group and bounds it group-theoretically.
artifacts:
  - research/artifacts/ex-q34-frame-extraction-2026-09-12.md
---

**ESTABLISHED.**  Let `W_(n,k) = U(k) wr S_n` act block-monomially on
`C^n ⊗ C^k`, with normalized Hilbert--Schmidt norm, and let
`rho : G -> W_omega = prod_omega W_(n_m,k_m)` be a homomorphism of a
countable group into the metric ultraproduct.  The permutation parts give a
homomorphism

```text
psi : G -> prod_omega (S_(n_m), d_H),    A := ker psi   (soft kernel),
```

because `d_H(sigma, sigma') <= ||M - M'||_2^2 / 2` for block-monomials with
permutation parts `sigma, sigma'`.  That comparison is already used in
`block-monomial-coordinate-collapse`.  Then:

1. `G/A` is sofic, for arbitrary block sizes and arbitrary phases or
   rotations inside blocks.
2. If `k_m = k` is constant and `rho` is regular
   (`tau(rho(g)) = 0` for `g != e`), then `A` is **amenable**.  In fact `L(A)`
   embeds trace-preservingly into a tracial ultraproduct of `ℓ^∞_n ⊗ M_k`, so
   it satisfies the standard identity `S_(2k)` and is type I.
3. If `k = 1` (monomial models) and `rho` is injective, `A` is **abelian**.

**Corollary.**  A group with no nontrivial amenable normal subgroup (for
`k=1`: no nontrivial abelian normal subgroup) is sofic iff it has a regular
HS model in `U(k) wr S_n` for some fixed `k`.

The theorem says where phases can matter: only on an amenable (for monomials,
abelian) normal subgroup.  The trace cancellation of
`scalar-trace-of-diagonal-normalizer-is-permutation-blind` is the `A = G`
abelian case.  Model tests: a random-character diagonal model of an abelian
group is regular with `A = G` abelian; `n` Haar-random homomorphisms
`F_2 -> U(2)` give soft kernel `F_2` but are not regular, as (2) predicts; and
a sofic approximation has `A = 1`.  Bounded `k` is sharp: with unbounded blocks
every hyperlinear group has block-diagonal models, so `A = G` is possible.

Finitary, dimension-free form with explicit constants and rounding rate:
`standard-identity-witnesses-force-block-displacement`.  Frame-level input
(approximate normalizers of an equal-rank decomposition):
`coarse-frame-normalizers-are-near-block-monomial`.

## Attempts

Established; the proof is `block-monomial-hs-models-sofic-mod-amenable-soft-kernel-proof`.
