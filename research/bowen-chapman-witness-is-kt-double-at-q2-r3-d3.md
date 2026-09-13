---
rg: 2
id: bowen-chapman-witness-is-kt-double-at-q2-r3-d3
kind: claim
title: The Bowen--Chapman Lean witness is the Kun--Thom double at (2, 3, 3), and its hyperlinearity is the bit the (H1) chain decides
distinct_from:
  kt-pair-group-double-is-nonsofic: that is Kun--Thom Theorem A for the double of every Theorem E pair; this identifies the formalized Lean group with one such double and puts its hyperlinearity in the established equivalence class
  kun-thom-group-doubles-are-surjunctive: that proves the doubles surjunctive; this is about hyperlinearity of one double and which open nodes decide it
  kt-wreath-hyperlinear-iff-double-hyperlinear: that is the wreath, double and RE/C equivalence for the abstract Theorem E pair; this adds the Lean group, the free action and wreath-extendable actor models to the same class at one parameter
  kt-wreath-models-never-round-on-the-vertex: that is the pointwise obstruction for wreath models; this uses it to name the one bit that both the non-hyperlinear chain and the hyperlinear-nonsofic lane target at the Lean witness
  surjunctive-nonsofic-group-exists: that is the existence of a finitely generated surjunctive nonsofic group; this asks whether the Lean witness is also hyperlinear, which would answer Pestov Q3.4 negatively
artifacts:
  - research/artifacts/q34-bc-witness-hyperlinear-2026-09-12.md
  - research/artifacts/bowen-chapman-lean-review-2026-09-12.md
  - GroupApproximation/BowenChapman/Endpoint.lean
  - GroupApproximation/BowenChapman/LaurentPair.lean
---

**ESTABLISHED.**

**Identification.** The Lean theorem `GroupApproximation.BowenChapman.symmetricDouble_fg_surjunctive_not_isSofic`
(`GroupApproximation/BowenChapman/Endpoint.lean`) concerns `E = SymmetricDouble Ambient Peripheral`.
`GroupApproximation/BowenChapman/LaurentPair.lean` defines:
- `Laurent = F_2[Z^3]` and `Poly = F_2[N^3]`, with `polyToLaurent` injective (`polyToLaurent_injective`);
- `Actor = EL_3(Z)`, acting on exponents by `v ↦ Mv` (`exponentAction`), on `Laurent` by `x^v ↦ x^(Mv)`
  (`substitution`), and entrywise on `EL_3(Laurent)` (`actorAction`);
- `Ambient = EL_3(Laurent) ⋊ Actor`;
- `Peripheral`, the image of `EL_3(Poly)` under the injective `peripheralHom` (`peripheralHom_injective`).

`SymmetricDouble G Γ` is the `PushoutI` of two copies of `G` along the inclusion of `Γ`
(`GroupApproximation/Sofic/WeakMFNonsoficDouble.lean`), that is, `G *_Γ G`.

**Why this is the Kun--Thom double.**
- `Z` is Euclidean, so `EL_3(Z) = SL_3(Z)`.
- Theorem E (`kun-thom-nonsofic-wreath`) lets `SL_d(Z)` act on `F_q[x^(±1)]` by monomial substitution.
  Substitution through the standard representation, `x^v ↦ x^(Mv)`, is the Lean action. Substitution through the
  contragredient is the Lean action composed with the automorphism `φ(M) = (M^T)^(-1)` of `SL_3(Z)`.
- `(l, M) ↦ (l, φ(M))` is an isomorphism of the two semidirect products. It is the identity on `EL_3(F_2[x^(±1)])`,
  so it fixes `Γ`.

So `E` is isomorphic to the double `D = G *_Γ G` of the Theorem E pair at `q = 2`, `r = d = 3`. The isomorphism
takes the two copies of `Ambient` to the two copies of `G`, and `Peripheral` to `Γ = EL_3(F_2[x_1, x_2, x_3])`.

**Equivalence.** At `(q, r, d) = (2, 3, 3)` the following are equivalent.
1. The Lean witness `E` is hyperlinear.
2. The double `D = G *_Γ G` is hyperlinear.
3. The wreath `W = (⊕_(G/Γ) Z/2) ⋊ G` is hyperlinear.
4. `L(Γ) ⊆ L(G)` is relatively embeddable over the scalars (`RE/C`).
5. The Kun--Thom free nonsofic action of `G` is hyperlinear.
6. Some trace-preserving `σ : G -> U(∏_U M_n)` extends to a trace-preserving model of `W`.
7. Some trace-preserving `σ : G -> U(∏_U M_n)` extends to `W` and has no (H1) rounding on `Γ`.

Derivation: `bowen-chapman-witness-is-kt-double-at-q2-r3-d3-proof`.

**The conflict, recorded.** Two groups of open nodes decide this one bit at `(2, 3, 3)`.
- **Towards "not hyperlinear".**
  - `non-hyperlinear-group`, via `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding`. It is open only through
    (H1), `hs-stable-vertex-rounding-for-every-model` (commit 9919a5637).
  - (H1) and `theorem-e-vertex-rounds-to-unit-type-representations` are stated for every parameter, so they include
    `(2, 3, 3)`. If either is established, 1–7 are false there.
  - The Laurent sibling `laurent-vertex-rounds-for-every-model` also includes `r = 3`. Its reduction to property (T)
    of the mixed-level root group `K_i` (commit 44267adad) needs `r >= 5`, so this (T)-style handle does not reach
    the Lean parameter.
- **Towards "hyperlinear".**
  - `hyperlinear-wreath-model`, through `hyperlinear-nonsofic-free-action-from-kt-wreath`.
  - The double routes into `hyperlinear-nonsofic-group` that use `kt-pair-group-double-is-nonsofic`, for example
    `hyperlinear-nonsofic-from-kt-ce-stabilizer`.
  - The finitary normalizer lift `kun-thom-finitary-action-lifts-to-normalizer`.
  - Success at `(2, 3, 3)` makes 1–7 true there. By item 7 it refutes (H1) at that parameter, and it answers Q3.4
    negatively with a group whose nonsoficity is formalized.
- **Both cannot succeed at one parameter.**
  - The general (H1) would refute every hyperlinearity route at every parameter.
  - A hyperlinearity proof at any one parameter refutes the general (H1).
  - Restricting (H1) to wreath-extendable models is no easier than the target, because that restriction *is* the
    target (`kt-wreath-models-never-round-on-the-vertex`, corollary 1).

## Attempts

- **A shortcut specific to the parameter.** None found. The value `q = 2, r = d = 3` enters none of the equivalence
  proofs. The one rank-sensitive handle, property (T) of `K_i`, needs `r >= 5`. Artifact §8.
