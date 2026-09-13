---
rg: 2
id: pestov-9-1-formalized-in-lean-unconditionally
kind: claim
title: Lean proves with no hypotheses and only the standard axioms that some infinite simple Kazhdan group is sofic and hyperlinear
distinct_from:
  infinite-simple-kazhdan-hyperlinear-group: that is Pestov's existential question, answered by a reviewed prose proof; this is a kernel-checked Lean theorem stating the answer with no hypotheses.
  simple-kazhdan-lef-group-from-minimal-subshift: that is the mathematical theorem about one explicit group; this is its formal proof in the development, closing over propext, Classical.choice and Quot.sound only.
---

The development proves, in `GroupApproximation/Pestov91/WitnessAssembly.lean`, the theorem
`GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef`:

`∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E`

with no hypotheses. `Palomar/Pestov91Solution.lean` derives from it the two theorems compared by
`Palomar/comparator-pestov91.json`, `Pestov91.exists_infinite_simple_propertyT_hyperlinear` and
`Pestov91.exists_infinite_simple_propertyT_sofic`, whose statements use Mathlib and the challenge's own
definitions only. The `Palomar check` workflow runs `scripts/PalomarPestov91Axioms.lean`, which prints the
axiom closure of both compared theorems and fails unless it lies inside `[propext, Classical.choice, Quot.sound]`.
Runs 34762687202 (be41521bf) and 34765520365 (174e3006d) print exactly those three axioms for each, so neither
uses `sorry` or an added axiom, and neither takes a literature input as a hypothesis.

The predicates:
- `HasKazhdanPropertyT.{0, 0}` asks for a Kazhdan pair over real Hilbert spaces in `Type`
  (`GroupApproximation/Kazhdan/Kazhdan.lean`). It is equivalent to the complex-unitary form
  (`hasKazhdanPropertyT_iff_complex`), which is the challenge's `HasPropertyT`.
- `IsLEF` is local embeddability into finite groups; `isSofic_of_isLEF` and `isHyperlinear_of_isSofic` give the
  finite-set models by permutations under the normalized Hamming distance and by unitary matrices under the
  normalized Hilbert--Schmidt distance (`GroupApproximation/Sofic/Sofic.lean`,
  `GroupApproximation/Sofic/Hyperlinear.lean`), which the Solution repackages into the challenge's
  `IsSoficGroup` and `IsHyperlinearGroup`.

The witness is `EL_3(R)` for the crossed product `R = LC(X, F_2) ⋊ Z` of the Toeplitz subshift `X`. Its centre
is trivial, so no quotient is taken.

**Status: established (2026-09-13).** The Palomar theorems landed at 5f9c16b7b on the witness modules below.
The `Palomar comparator` workflow with NanoDa passed on `Palomar/comparator-pestov91.json` at e32bac3f3
(run 34751904895), and again at 174e3006d (run 34765532993).

## Proof architecture, as formalized

- `Toeplitz.lean`, `ToeplitzModel.lean`, `Subshift.lean`, `SubshiftAlgebra.lean`, `SubshiftMinimal.lean`: the
  Toeplitz sequence `n ↦ parity of ν₂(3n - 1)`, its `2^K`-periodic models, the subshift `X`, freeness and
  minimality of the shift.
- `CrossedProduct.lean`, `CrossedProductFG.lean`, `WitnessRing.lean`, `RingFinitelyGenerated.lean`: the ring `R`
  as a skew monoid algebra and its finite generation.
- `RingSimple.lean`, `WitnessCentre.lean`, `WitnessSimple.lean`: `R` is simple with centre `{0, 1}` for a free
  minimal action, by the diagonal cut.
- `SplitSimplicity.lean`: `EL_3(R)` is simple, from ring simplicity, the centre and split annihilators, by root
  extraction; no division and no stable range.
- `Kazhdan.lean`, `KazhdanUnitary.lean`: property (T), by the Ershov--Jaikin-Zapirain theorem proved in the
  repository, in real and complex forms.
- `LEFCrossedProduct.lean`, `LEFWitness.lean`, `LEF.lean`, `LEFHyperlinear.lean`: `R` is an LEF ring by
  periodic models on cycles `Z/N`, so `EL_3(R)` is LEF, sofic and hyperlinear.
- `Assembly.lean`, `WitnessAssembly.lean`: the endpoint.

This is narrower than the three-part prose write-up (`research/artifacts/pestov-9-1-writeup-2026-09-13-part1.md`
and its parts 2 and 3), which treats every finite field and every infinite minimal subshift and proves
simplicity modulo the centre by a tower argument. The registered theorem is the existence statement through
this one witness; the general prose theorem is not formalized.

## History

- **Assembly from explicit leaves (pc-assembly, 2026-09-13).** Historical: the leaves G1--G8 of the blueprint
  `research/artifacts/pestov91-lean-blueprint-2026-09-13.md` were landed one by one (subshift 9f5b9477d, LEF
  59d538039, WitnessRing 1dc71ce96, LEFWitness cdc493958, SimpleModCentreCrossed 4cacfbe04, CrossedProduct
  21147debe, WitnessSimple and WitnessAssembly with the Solution at 5f9c16b7b). The reduction
  `EndpointOfLeaves.lean` and the combined endpoint `exists_infinite_simple_kazhdan_sofic_hyperlinear` named
  by earlier versions of this page were never landed; the Solution takes soficity and hyperlinearity from
  `IsLEF` instead.
