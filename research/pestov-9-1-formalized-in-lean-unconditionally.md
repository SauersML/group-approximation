---
rg: 2
id: pestov-9-1-formalized-in-lean-unconditionally
kind: claim
title: Lean proves with no hypotheses and only the standard axioms that some infinite simple Kazhdan group is sofic and hyperlinear
distinct_from:
  infinite-simple-kazhdan-hyperlinear-group: that is Pestov's existential question, answered by a reviewed prose proof; this is a kernel-checked Lean theorem stating the answer with no hypotheses.
  simple-kazhdan-lef-group-from-minimal-subshift: that is the mathematical theorem about one explicit group; this is its formal proof in the development, closing over propext, Classical.choice and Quot.sound only.
---

The development proves, in `GroupApproximation/Pestov91/Endpoint.lean`, the theorem
`GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_sofic_hyperlinear`:

`∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧ IsSofic E ∧ IsHyperlinear E`

with no hypotheses. Its axiom closure is exactly `[propext, Classical.choice, Quot.sound]`, so it uses no
`sorry`, no added axiom and no literature input stated as a hypothesis.

The predicates:
- `HasKazhdanPropertyT.{0, 0}` asks for a Kazhdan pair over real Hilbert spaces in `Type`
  (`GroupApproximation/Kazhdan/Kazhdan.lean`). The same pairs work in the complex-unitary form of Bekka--de la
  Harpe--Valette, Definition 1.1.3 (`hasKazhdanPropertyT_iff_complex`), which is the form of Pestov's question.
- `IsSofic` and `IsHyperlinear` ask for finite-set models, by permutations under the normalized Hamming distance and by
  unitary matrices under the normalized Hilbert--Schmidt distance (`GroupApproximation/Sofic/Sofic.lean`,
  `GroupApproximation/Sofic/Hyperlinear.lean`).

The witness is `EL_3(R)` for the crossed product `R = LC(X, F_2) ⋊ Z` of the Toeplitz subshift `X`. Its centre is
trivial, so it is its own quotient by the centre. The plan is the blueprint
`research/artifacts/pestov91-lean-blueprint-2026-09-13.md`, items G1--G9.

**Status: open.** No binder-free theorem is on main yet.

## Attempts

- **Assembly from explicit leaves (pc-assembly, 2026-09-13; in progress).**
  - Landed on main and consumed:
    - `Kazhdan.lean`: property (T) for `EL_n` over finitely generated rings, by Ershov--Jaikin-Zapirain, proved in
      the repository.
    - `Centre.lean` and `CentreSkew.lean`: the centre, and infiniteness.
    - `RingSimple.lean`: simplicity of `LC(X, K) ⋊ Z` for a free minimal system.
    - `SplitSimplicity.lean`: `EL_n(R)` simple from ring simplicity, centre `{0, 1}` and split annihilators.
    - `Assembly.lean`.
    - `LEFHyperlinear.lean`: LEF gives sofic and hyperlinear.
    - `CrossedProduct.lean` and `CrossedProductFG.lean`: covariance, normal form and finite generation criteria.
  - The reduction `EndpointOfLeaves.lean` takes the remaining ingredients as explicit hypotheses. It is not yet
    landed; it lands after a green probe.
  - It stops at the witness-level leaves of the blueprint:
    - G1: the Toeplitz shift is free and minimal, on a compact totally separated space.
    - G7: the witness ring as a crossed product, with `hconj`, `hspan` and `Infinite`.
    - G2: the witness ring is simple.
    - G3: its central elements are `0` or `1`.
    - G5: it is finitely generated.
    - G6: `EL_3` of it is LEF, through local matrix models.
  - The binder-free endpoint (G8) applies the ring-leaves form to those theorems once they land.
