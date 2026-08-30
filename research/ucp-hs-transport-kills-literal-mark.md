---
rg: 2
id: ucp-hs-transport-kills-literal-mark
kind: claim
title: Unital completely positive Hilbert--Schmidt models of the literal group kill the central mark
distinct_from:
  literal-central-mark-corona-invisible: that is the operator-norm statement, proved in the tree; this asks the same conclusion for u.c.p. models that are only Hilbert--Schmidt asymptotically multiplicative, which is strictly harder and known to FAIL for merely bounded models because E is sofic.
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

For every sequence of u.c.p. maps `φₙ : C*(E) → M_{kₙ}` with
`‖φₙ(ab) − φₙ(a)φₙ(b)‖₂ → 0` and `tr ∘ φₙ → τ_E`, necessarily
`tr φₙ(u_w) → 1` for the central mark `w ≠ 1`.  Since `τ_E(u_w) = 0`, this is
the same as: no such sequence exists, i.e. `τ_E` is not amenable.

## Why u.c.p. could succeed where bounded fails

`E` is sofic, so BOUNDED Hilbert--Schmidt models exist
(`canonicalMaximalTrace_isHyperlinearTrace_of_isSofic`) and do NOT kill the
mark; any proof here must use complete positivity.  The one tool that does is
Kirchberg's lemma (Brown, Mem. AMS 184 (2006), Lemma 4.1.11, from Kirchberg
Math. Ann. 299 (1994)): for a Kazhdan group `K`, u.c.p. Hilbert--Schmidt
asymptotically multiplicative maps on `C*(K)` are trace-close to HONEST
finite-dimensional representations.  The base `B` of `E` (the six-generator
Kazhdan--Clifford group) has property (T), so on `C*(B)` the model is
character-close to honest representations `πₙ`, and the compression relations
`t vᵢ t⁻¹ = vᵢ²` make `φₙ(u_t)` a Hilbert--Schmidt approximate intertwiner
between the doubling twist of the base representation and its restriction.

## What has to be overcome

Kirchberg's lemma gives closeness of CHARACTERS, not of the models pointwise;
the manuscript's transport (`Sofic/LiteralNonMFEndpoint.lean`,
`kazhdanPinning`, `negativeCorner_kazhdanTransport_contradiction`) consumes
operator-norm control to build the conjugation representation, and the printed
remark (`manuscriptFullRadicalsDoNotEntailNonsoficity`) records that
Hilbert--Schmidt approximations do not supply it.  So the open question is
exactly whether property (T) plus complete positivity recovers enough of the
transport: (i) upgrade character-closeness on `B` to corner-wise unitary
conjugacy of honest representations (a second use of (T), on `π ⊗ π̄'`
approximate invariant vectors); (ii) run the doubling/Clifford sign count on
the large corner; (iii) control the lamp `c` and the mark
`w = [tct⁻¹, v₁ (tct⁻¹) v₁⁻¹]` there.  Step (ii) is where the sofic
block-tower models must, and do, escape: they are not u.c.p., and their
corners are permutation corners on which the Clifford sign is invisible.

Open in both directions; failure of (i)-(iii) is not evidence for
`literal-group-factorization-property` either.

The absolute (T) case is now typed and consumed:
`KirchbergKazhdanQuasidiagonalInput` (Brown Lemma 4.1.11 / Prop 4.1.12) in
`GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean` yields `problemX1_restricted_to_kazhdan` and
`not_hasFactorizationProperty_of_kazhdan_not_operatorMF`.  What this claim
asks beyond it is exactly the RELATIVE version: running the rigidity of the
Kazhdan base of `E` through models of the whole non-Kazhdan group.

## Depth calibration against the flexible-stability frontier

Step (i) — upgrading the u.c.p. models POINTWISE (not just in character) on
the Kazhdan base — is precisely a flexible Hilbert--Schmidt stability
statement for that base.  The graph already carries flexible HS-stability of
arithmetic groups as live routes into `non-hyperlinear-group`
(`non-hyperlinear-from-hnn-over-sl2-z`, `non-hyperlinear-from-hnn-over-sln-z`,
`non-hyperlinear-from-sl3-z-weak-ucp-stability`; Dogon arXiv:2211.10492 for
`Sp₂g(ℤ)`, Dogon--Vigdorovich arXiv:2506.20843 for `SL₂(ℤ[1/p])` and the
character-rigidity equivalence for higher-rank lattices).  So establishing the
stability input here would simultaneously advance the program's root, and
conversely: this leaf is at least as deep as that frontier, and any partial
stability theorem for the literal base should be checked against both
consumers.  Kirchberg's character-level lemma is what remains after
stability is subtracted, which is why the absolute Kazhdan case closed
(`KazhdanQuasidiagonalTraces.lean`) while this relative case is open.

## Attempts

**Exact-commutation normal form (2026-08-30 recon).**  Let
`φ : C*(E) → M_k` be u.c.p. and δ-multiplicative in the normalized 2-norm
with `tr ∘ φ ≈ τ_E`.  Stinespring `φ = V^* π(·) V` with `π` a genuine
representation of `E`, and let `P = VV^*`.  Kirchberg's property-(T)
perturbation (Brown, Lemma 4.1.11 mechanism) applied to the conjugation
representation of the Kazhdan base `B` on the Hilbert--Schmidt space
replaces `P` by a projection `P'` with `‖P − P'‖_2/√k` small that commutes
with `π(B)` EXACTLY.  Consequences, all exact or 2-small:

1. `ρ := P'π(·)P'|_{C*(B)}` is an honest finite-dimensional representation
   of `B` with `tr̄ ∘ ρ ≈ δ_e` (regular-like);
2. `φ'(c) = P'π(c)P'` commutes with `ρ(B)` exactly (the leakage
   `(1−P')π(b)P'` vanishes, `P'` commuting with `π(b)`);
3. `X := φ'(tct^{-1})` commutes with `ρ(B_1)` exactly, where
   `B_1 = tBt^{-1} = 2Z^3 ⋊ SL_3(Z)` (index 8 in `B`, NOT normal), because
   `P'` commutes with `π(B_1) ⊆ π(B)`;
4. `φ'(t)` is 2-close to a unitary `U` (Hilbert--Schmidt polar correction),
   and `Uρ(b)U^* ≈_2 ρ(tbt^{-1})` with error independent of `b`;
5. Kazhdan projections are 2-stable: spectral-gap functional calculus gives
   `‖U q_B U^* − q_{B_1}‖_2̄ ≤ Cδ/κ` for the invariant-vector projections
   on `P'H`, so the finiteness step of the corona argument survives at the
   Hilbert-space level.

**The one remaining gap.**  The corona proof concludes by showing
`X` almost commutes with all of `ρ(B)`; then
`u = [tct^{-1}, v_1]` maps 2-close to `1`, `w = u^2` likewise,
contradicting `tr̄ φ(w) → τ_E(w) = 0`.  At the u.c.p. level the available
statement is `X ∈ ρ(B_1)'` exactly, and the needed statement is `X`
almost-invariant under `Ad ρ(B)` on the Hilbert--Schmidt space.  Since
`B_1` is not normal in `B`, `Ad ρ(B)` does not preserve `ρ(B_1)'`, and a
vector exactly invariant under the finite-index `Ad ρ(B_1)` need not be
almost invariant under `Ad ρ(B)` (sign-representation phenomena).  The
corona regime closes this with the super-operator estimate
`‖Ad(V) − Ad(V')‖ ≤ 2‖V − V'‖_op`, which costs exactly the operator-norm
multiplicativity that u.c.p. models lack; a normalized-super-trace count
(`dim ρ(B_1)' ≈ 8 · dim ρ(B)'`, both `o(k²)`) is too weak to force one
specific unit vector across.

**Equivalent finite-dimensional question.**  The factorization property of
`E` is thereby equivalent to: do there exist finite-dimensional
representations `ρ_n` of `B` with `tr̄ ∘ ρ_n → δ_e`, almost-unitaries
`X_n ∈ ρ_n(B_1)'` and `T_n` almost-implementing the doubling twist, and
`C_n ∈ ρ_n(B)'`, satisfying the remaining relations of `E`
2-approximately, with `‖[X_n, ρ_n(v_1)]‖-type defects bounded away from
triviality (so that `tr̄` of the mark word stays near `0`)?  A negative
answer for all such data establishes this claim and kills
`stw99-x1-fails-via-literal-group`; a positive answer with genuine models
refutes this claim and, through Brown 4.1.9, refutes STW Problem X(1).
The hyperfinite-representation theorem
(`literal-group-mark-invisible-to-hyperfinite-representations`) is the
EXACT version of this claim: when the almost-relations are exact and the
model is an injective finite von Neumann algebra, the mark dies; it says
nothing about the 2-approximate matrix regime, where soficity shows the
mark survives non-u.c.p. models.
