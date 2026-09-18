---
rg: 2
id: higman-v-step-b-core-local-conjugation-and-f-obstruction
kind: claim
title: Cone-local balanced conjugation settles every per-cycle-symmetrizable instance of the Higman-V Step-B core, and an explicit instance with infinite-order product shows the rest needs Thompson-F rewriting
---

**ESTABLISHED (lane `bh-pal-met-join`, lane proof, paper only; not formalized, not reviewed).**
It concerns `Envelope.HigmanVCStepBCoreStatement` (Lean, `EnvelopeHigmanVCStepBCore.lean`),
which is input H1 of the smallest conditional root for the metabelian T2/T3 targets
(`bhNagaoUncond_fpMetabelian_routeA`). The statement is not closed here.

## Setting

We use the notation of `EnvelopeHigmanVCStepBClosed`:
- `Q` is the all-swaps free group modulo the standard relators, with the four families
  comparable, involution, conjugation and split;
- `ℓ(x,y)` is a letter, `E : Q → V_d` is the evaluation, and `U` is the balanced subgroup;
- `H_A` is the antichain subgroup, and `S = U · ⋃_A H_A · U`.

For a word `e` below a code word `c`, write `e = c·addr(e)`. The core has the following data:
- a complete code `C`;
- `h ∈ H_C \ U`, with permutation `π` of `C`;
- an antichain `D` that refines `C` and is strictly deeper;
- `P ∈ H_D \ U`.

Its claim is `hP ∈ S`. The proved cases are `h ∈ U`, `P ∈ U`, and `D ⊆ C ⋆ T` for a single
complete code `T`.

## Claim A (cone-local conjugation)

Fix `m ≥ 1` and permutations `v_c` of the words of length `m`, one for each `c ∈ C`. Let `u` be
the product, over `c`, of the letters realizing `c t ↦ c v_c(t)`. These letters are balanced,
so `u ∈ U`.

Then `h u h⁻¹ = u^π` in `Q`, where `u^π` acts on the cone of `π(c)` by `v_c`, so again
`u^π ∈ U`.

*Proof.* Every letter of `h` is `ℓ(c₁,c₂)` with `c₁, c₂ ∈ C`. Each letter `ℓ(c t, c t')` of
`u` has both cones inside a `C`-cone, so every letter of `h` maps them by prefix replacement.
The conjugation relator, applied letter by letter, therefore transports it to
`ℓ(π(c) t, π(c) t')`. ∎

## Claim B (per-cycle symmetrization)

Suppose there are:
- `m`, with every `D`-address of length `≥ m`, and a `u` as in Claim A;
- for each nontrivial `π`-cycle `γ`, one complete code `T_γ`;
- for each `π`-fixed `c`, any antichain `A_c`;

such that `u(D) ⊆ A := ⋃_{γ} ⋃_{c ∈ γ} c·T_γ ∪ ⋃_{c fixed} c·A_c`. Then `hP ∈ S`.

*Proof.*
1. `u P u⁻¹ ∈ H_{u(D)} ⊆ H_A`: push each `D`-letter through `u`, which is possible since
   `D` is at least as deep as `u`'s letters, and then use monotonicity of `H`.
2. `h ∈ H_A`. By faithfulness of `H_C`, `h` equals a product of transpositions inside its
   cycles. Split each of these along `T_γ`.
3. `hP = h u⁻¹ (uPu⁻¹) u = (u^π)⁻¹ · (h · uPu⁻¹) · u`, which lies in `U · H_A · U ⊆ S`. ∎

This strictly contains the proved symmetric case (`u = 1`, with one global `T`). A second
cheap escape is also always available: `hP = (hPh⁻¹)·h`, and `hPh⁻¹ ∈ H_{h(D)}`. So whenever
`hPh⁻¹ ∈ U`, we get `hP ∈ U·H_C ⊆ S`. For example, `h = ℓ(0,10)` and `P = ℓ(0,100)` give
`hPh⁻¹ = ℓ(10,00)`.

## Claim C (a hard instance, with explicit data)

Take `d = 2`, `C = {0,10,11}`, `h = ℓ(0,10)` and `D = {0t, 1000t : |t| = 2}`, and let
`P = ∏_t ℓ(0t,1000t)`. This `P` is the split of `ℓ(0,1000)` below depth 3.

1. **Every core hypothesis holds.** `D` is non-symmetric, because the addresses `t` and `00t`
   would both have to lie in one `T`. Neither `h` nor `P` is balanced.
2. **No data as in Claim B exists, even after refining each pair `(0t, 1000t)` by its own code
   `R_t`.**
   - The cycle `(0 10)` forces `T_γ` to contain `v_0(Z)`, where `Z = ⋃_t tR_t` is complete. So
     `T_γ = v_0(Z)`.
   - `T_γ` must also contain `v_{10}(00Z)`. Then `z ↦ v_0⁻¹ v_{10}(00z)` would be an injection
     `Z → Z` that raises length by 2. That is impossible at a word of maximal length.
   - `hPh⁻¹ = ∏_t ℓ(10t, 000t)` is unbalanced and has the mirror obstruction.
3. **`E(hP)` has infinite order.** It sends `0s ↦ 000s`, `1000s ↦ 10s`, `1001s ↦ 001s` and
   `101s ↦ 01s`, and fixes `11`.
4. **The `S`-form in `V`.** In `V`, `E(hP) = E(ℓ(00,10)) ∘ E(σ)`, where
   `σ = ℓ(00,1000)·c`, `c` is the 3-cycle `01 → 1001 → 101 → 01`, and
   `σ ∈ H_A` for the antichain `A = {00,01,1000,1001,101,11}`. This was checked by hand, cone by
   cone.
5. **So the required `Q`-identity is `ℓ(0,10)·ℓ(0,1000) = ℓ(00,10)·σ`.** This is ONE explicit
   equation in `Q`. The naive rewriting diverges: split, then conjugate, then split again
   produces letters of ever greater depth (`ℓ(10,00000)`, `ℓ(01,00001)`, …).

## What this means for H1

The core contains infinite-order (Thompson-`F`-like) products. No choice of antichain,
refinement or cone-local balanced conjugation can bring such a product into a single finite
`H_A`. Any proof of H1 must derive `Q`-identities of the form of item C.5 from the split and
conjugation relators. This is the content that a Thompson-`F` normal form supplies (Cannon–Floyd–Parry for `F`), glued to the symmetric groups. The lane-93f reduction
does not avoid it.

Recommended next steps:
1. **Calibration.** Derive the single identity C.5 in `Q`, by hand or by a bounded
   Knuth–Bendix / coset search on MSI in the finite sub-presentation on the letters of depth
   ≤ 5. Then transcribe it to Lean as a finite certificate. It is a model test for any
   general proof.
2. **Route (proposed, unverified).** Formalize the `F` normal form inside `Q`. The target would be the subgroup
   generated by the one-sided pivots `ℓ(a, b)` with `|b| = |a| + 1` along a fixed ray, shown
   faithful. Then try to close the core with Claim B plus that faithfulness; that this suffices is NOT shown here.
3. **Source to read.** Bleak–Quick (GGD 2017) derive their finite presentations of `V` from an
   infinite presentation by cone transpositions. Whether their completeness argument transfers
   verbatim to `HigmanVCAllAntichainStatement` at `d = 2` should be checked at source. We have
   not read their proof.

**Lesson for general BH.** Local symmetrization makes all the finite, torsion bookkeeping
cheap: cone-local conjugation settles every per-cycle-symmetrizable configuration. The
irreducible content of `V`'s presentation is the infinite-order part, i.e. Thompson's `F`.
The prefix swindle (lane bh-hig-02) likewise reaches only torsion information. It yields only `z^(d−1) = 1` for central kernel elements, and it is itself conditional
on the product identity. A proof of H1 must supply an `F` normal form; bookkeeping of
torsion or centrality alone cannot close it.
