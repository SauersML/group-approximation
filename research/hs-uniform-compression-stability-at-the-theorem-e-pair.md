---
rg: 2
id: hs-uniform-compression-stability-at-the-theorem-e-pair
kind: claim
title: Approximately commuting unitaries stay approximately commuting after conjugation by the two Kun--Thom compressors, uniformly in the dimension
distinct_from:
  kt-centralizer-normalization-hs: that asks normalization for trace-preserving representations into tracial ultraproducts; this is a dimension-uniform matrix inequality at one explicit rigid presentation, quantified over all approximate representations with no trace condition, and equivalent to normalization for every homomorphism.
  hyperlinear-groups-kill-rigid-compression-defects: that is the criterion for all hyperlinear groups and all rigid pairs; this is one finitary instance whose two outcomes already reach both landmarks.
  kt-canonical-hs-normalization-fails: that is the existence of a non-normalizing Connes-embeddable model with arbitrary trace; this is the uniform inequality whose failure is a sequence of finite matrix counterexamples.
refuted_by:
  - hs-compression-stability-fails-at-the-theorem-e-pair
artifacts:
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

**OPEN, and a win--win at one explicit presentation.** Take the Kun--Thom Theorem E pair with
`d = 3`, `r >= 3` and `q` a prime power:

```text
Gamma = EL_r(F_q[x_1,x_2,x_3]),   G = EL_r(F_q[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) x| SL_3(Z),
B = I + E_12,   A = C B,          G = <Gamma, A, B>,
```

as in `kt-two-positive-compressors-generate-full-obstruction`, and a finite symmetric
generating set `F` of `Gamma`. The claim: for every `eta > 0` there are `eps > 0` and `R`
such that for all `n`, every map `u` from the `R`-ball of `G` to `U(n)` with `u_1 = 1` and
`||u_g u_h - u_(gh)||_2 <= eps` (normalized trace), and every unitary `z` with
`||[z, u_s]||_2 <= eps` for `s in F`,

```text
||[u_t z u_t^*, u_s]||_2 <= eta        for all s in F and t in {A, B}.
```

## The two outcomes

- **If it holds:** the Kun--Thom wreath is not hyperlinear, which gives
  `non-hyperlinear-group` (route `non-hyperlinear-via-hs-uniform-compression-stability`).
- **If it fails:** some hyperlinear group carries a nontrivial rigid defect, hence is
  nonsofic, and Pestov's Question 3.4 has a negative answer (route
  `hyperlinear-rigid-defect-from-hs-compression-instability`).

By [[kazhdan-commutant-compression-stability-is-finitary]] the claim is equivalent to
normalization of `C(sigma(Gamma))` by `sigma(G)` for every homomorphism
`sigma : G -> U(prod_U M_n)`.
- The same then holds in every Connes-embeddable finite tracial algebra `M`: embed `M` in a matrix
  ultraproduct and intersect the larger centralizer with `M`, which `sigma(G)` preserves.
- Conversely, a non-normalizing model in such an `M` has a countably generated witness, which
  embeds in a matrix ultraproduct.
- So at this pair the claim is the negation of the Connes-embeddable form of
  `kt-canonical-hs-normalization-fails`.

At the nine-leaf Leavitt pair the same inequality is exactly equivalent to nonhyperlinearity of the
Leavitt unit group (`leavitt-unit-group-outside-class-iff-compression-stability`). For fixed rational `eta, eps` and integers `R, n`, the inner
statement is a first-order sentence over the reals, decidable by Tarski--Seidenberg. This uses
that `G` has solvable word problem: its elements are pairs of a matrix over
`F_q[x_1^(+-1),x_2^(+-1),x_3^(+-1)]` and a matrix in `SL_3(Z)`. So the claim is a `Pi^0_3`
sentence (`forall eta exists eps, R forall n`).

## What would prove it

Section 3 of the artifact isolates the inputs. Every established row spends property (T) as
rounding (R), localization (L) or lift (K).
- In the Hilbert--Schmidt row, (R) is vertex rounding (`hs-stable-vertex-rounding-for-every-model`),
  and (L) is a liftable masa of the actor commutant
  (`hs-block-gap-iff-liftable-masa-of-actor-commutant`).
- One model with both inputs normalizes (`hs-rounding-and-actor-gap-force-ccr`).
- The Hamming row gets both inputs from Kun's decomposition. The operator-norm row needs no
  (L), because its finite-stage Kazhdan projections have exact integer rank.

## Model tests

- It holds with `eta = O(eps)` for presentations whose compressors normalize `Gamma`.
- For the same pair and presentation, the inequality holds with Hamming models (Kun--Thom 4.1)
  and fails with operator-norm models
  (`weak-mf-groups-can-carry-rigid-defects`).
- It holds on the subclass of genuine representations of `G`
  (`ccr-holds-for-all-genuine-fd-coordinate-models`).

## Attempts

- **Transcribe the Hamming proof.** Dies at one-piece transport. Compressors can act
  non-monomially on multiplicity spaces, even in exact representations
  (`nonmonomial-multiplicity-obstructs-hs-compressor-transport`).
- **A conjugation-invariant size.** Dies at faithfulness: the trace is refinement-blind
  (`invariant-size-collapse`).
- **Drop a compressor.** Dies: with one compressor the actor is not Kazhdan. Its wreath is
  sofic with a nontrivial defect (`kt-single-compressor-canonical-lamps-do-not-exactify-actor`),
  so localization (L) is necessary, not only convenient.
- **Conditional closure.** Holds for every model satisfying (H1) and (H2')
  (`hs-rounding-and-actor-gap-force-ccr`). Both inputs are open for all models.
- **Scale counting.** Under (H1) with transported defect `delta_n`, the excess is at most
  `18 (N_n delta_n)^(1/3)`, where the number `N_n` of occupied dyadic aspect windows is at most
  `2 log_2 n + 2` (`ccr-under-vertex-rounding-from-few-aspect-scales`).
  - A counterexample sequence with (H1) therefore needs `delta_n log n` bounded below.
  - Finite-dimensional search at moderate `n` cannot find one.
