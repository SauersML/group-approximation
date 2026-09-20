---
id: fix-bhpalomar-graphproducts-main
kind: claim
rg: 2
title: "Fix GroupApproximation.BHPalomar.GraphProducts.Main: conditional on EnvelopeInput (BFFHZ Theorems C and E); chain unprobed"
---

**Status.** OPEN.

Route target (moved from frontmatter): `pbh-class-closed-under-graph-products`.

**Module.** `GroupApproximation/BHPalomar/GraphProducts/Main.lean`. It proves
`question31_of_envelopeInput : EnvelopeInput → Question31`, where `Question31` is BFFHZ
(arXiv:2503.21882v2) Question 3.1 with a positive answer: a graph product over a finite simple
graph of groups satisfying PBH satisfies PBH. It sits on the chain

`Statement → FreeProductMap → Twist → Semidirect → Embedding → Reduction`, and
`Statement → Restrict → Insert`, and `ProductClosure → ProductInput`, with all three joining in `Main`.

All files are on main as of 70e4d3e8e4. They are not wired into the root.

**First error.** None known. No trusted build has run: the empty-overlay probe of
`GroupApproximation.BHPalomar.GraphProducts.Main` was DEFERRED on 09-18 ~21:15, because Slurm
submission is blocked for the group (`AssocMaxSubmitJobLimit`). The pre-probe hardening pass is
ab84f925c9 and 70e4d3e8e4.

**Kind.** A conditional endpoint, plus an unprobed chain.

**What is proved from Mathlib alone.** This is the new mathematics of `pbh-graph-product-closure-proof`:

- Steps 1–5: `retractAmalgam_embeds_in_relAut`. If `C` is a retract of `X`, and `X` and `K` embed in a group `H` so
  that `C` and `K` commute, then `X *_C (C × K)` embeds in `Aut_H(H ∗ F₂)`.
- Step 6: `question31_of_retractAmalgamClosure`. Graph products are iterated retract amalgams.
- `ProductInput` (Zaremsky, arXiv:2405.18354, Proposition 5.5): PBH is closed under direct products, via the
  disjoint-union action (`productInput_holds`).

**Inputs (nearest red imports).** `fix-bh-palomar-graph-products-product-closure`. Fix those first: errors here may be knock-on.

**What it needs.** One hypothesis remains: `EnvelopeInput`. A group with an action of type (A) embeds in a group
`H` such that `Aut_H(H ∗ F₂)` satisfies PBH. That is BFFHZ Theorem C (i) ⇒ (iv) followed by Theorem E at `n = 2`. It
imports Zaremsky's Theorem A (finitely presented twisted Brin–Thompson groups), BBMZ Proposition 5.4, Hull–Osin
Theorem 5.9, and BFFHZ §§2–4 (the finite presentation of `Aut_G(G ∗ F_n)`, finitely generated stabilizers, and
2-transitivity on `Hom_G(G ∗ F_n, G)`). None of this is in Mathlib, and it is a long formalization. Until it is
done, T7 is a conditional solution, and it must be labelled that way on the Palomar surface.

**Resolve when.** A trusted build of `GroupApproximation.BHPalomar.GraphProducts.Main` is green with no sorry, and
`EnvelopeInput` is discharged by a Lean proof. When only the build is green, record the green commit here and
keep `status: OPEN` for the hypothesis.
