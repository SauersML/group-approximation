---
rg: 2
id: free-group-doubles-over-any-subgroup-are-sofic-proof
kind: route
title: Feed the free-actor theorem into the sofic coset-action double theorem
target: free-group-doubles-over-any-subgroup-are-sofic
requires:
  - gkp-free-group-actions-are-sofic
  - sofic-coset-action-makes-amalgam-double-sofic
---

Let `F` be a countable free group and `Γ ≤ F` any subgroup.

**Step 1: the actor is sofic.** Free groups are residually finite (Magnus),
and residually finite groups are sofic. So `F` is sofic.

**Step 2: the coset action is sofic.** `X = F/Γ` is countable and
`F ↷ X` is an action of a free group on a countable set. By
`gkp-free-group-actions-are-sofic` (GKP Theorem 2.19) it is a sofic action.
No property of `Γ` is used.

**Step 3: apply the double theorem.** `sofic-coset-action-makes-amalgam-double-sofic`
takes countable `Γ ⊂ H` with `H` sofic and `H ↷ H/Γ` sofic. It proves:
- `H *_Γ H` is sofic, through the canonical injective difference-cocycle map
  into the free generalized wreath product `F_X ⋊ H`, which is sofic by GKP
  Theorem 3.7;
- `L(H) *_{L(Γ)} L(H) = L(H *_Γ H)` is Connes embeddable;
- `L(Γ) ⊂ L(H)` is `RE/C`.

With `H = F`, Steps 1 and 2 give exactly its hypotheses. This proves items
1--3 of the target.

**Step 4: the classical comparison and the nonsofic-quotient example.**
- For finitely generated `Γ`, M. Hall's theorem makes `Γ` closed in the
  profinite topology of `F`. The classical separable-double criterion, not
  re-verified here, then makes `D` residually finite. This check is
  independent and not needed above.
- For normal `Γ` with `Q = F/Γ`, the fold `D → F` splits. Its kernel is the
  free group on `F/Γ` minus a point, by the Bass--Serre computation in
  `coset-difference-cocycle-embeds-double-proof`.
- `D/Γ ≅ Q * Q`: both copies of `F` map onto `Q` and agree on `Γ`, which is
  killed. So `D` is a sofic group with quotient `Q * Q`. Soficity does not
  pass to quotients, so a nonsofic `Q` gives no contradiction. ∎

**Mihailova instance.** Put `H = E = F_m` and `Γ = N = ker(E → Q)`. This
gives the stated consequence. The equivalence between hyperlinearity of the
ordinary binary coset wreath and `RE/C` of the vertex inclusion is item 1 ⇔ 6
of `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`. It is cited
there as a reading aid and is not required for items 1--3.
