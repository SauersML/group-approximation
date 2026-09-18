---
rg: 2
id: hyperlinear-nonsofic-free-action
kind: claim
title: Some countable group has a free p.m.p. action that is hyperlinear but not sofic
root: true
distinct_from:
  hyperlinear-nonsofic-group: that is Pestov's Question 3.4 for groups; this is the same separation for free p.m.p. actions and their orbit equivalence relations; that one implies this one (`hyperlinear-nonsofic-free-action-from-hyperlinear-nonsofic-group`), and the converse is not known
  kun-thom-free-nonsofic-action: that supplies nonsoficity of one free action; this asks for an action that is in addition hyperlinear
  kt-free-action-hyperlinear-iff-wreath-hyperlinear: that is the established equivalence for the specific Kun--Thom action; this is the existence question it feeds
---

**OPEN.** There is a countable group `G` and an essentially free p.m.p. action
`G ↷ (X,μ)` such that `L^∞(X) ⋊ G` embeds in `R^ω` (hyperlinear action, Păunescu
Definition 1.3) but no embedding carries `L^∞(X)` into the diagonal and `G` into
permutations (not sofic, Definition 1.4).

Equivalently, since for free actions the crossed product is the orbit relation's
algebra and soficity of the action equals soficity of the relation (Păunescu
Example 1.11 and Proposition 1.15): **some p.m.p. equivalence relation generated
by a free action is not sofic but has Connes-embeddable von Neumann algebra.**
This is Question 3.4's analogue one level up, for measured equivalence relations,
where nonsofic examples now exist (`kun-thom-free-nonsofic-action`).

## Attempts

* **Through the Kun--Thom wreath (live route).**
  `hyperlinear-nonsofic-free-action-from-kt-wreath`: the Kun--Thom free action is
  nonsofic, and by `kt-free-action-hyperlinear-iff-wreath-hyperlinear` it is
  hyperlinear exactly when `W = (⊕_(G/Γ) Z/2) ⋊ G` is. Open because
  `hyperlinear-wreath-model` is open.
* **Other actions over the same pair.** Any action with the generalized Bernoulli
  action over `G/Γ` as a factor contains `L(W)` in its crossed product, so it can
  be hyperlinear only if `W` is. A separation not passing through `W` must use a
  Theorem-C obstruction whose `Γ`-fixed functions generate a non-product
  invariant measure on `K^(G/Γ)`, or a different obstruction altogether.
* **From a hyperlinear nonsofic group.** If `H` were hyperlinear and nonsofic, its
  Bernoulli shift would be free and nonsofic (a sofic action makes the acting
  group sofic, Kun--Thom p. 4). Its crossed product is `L(Z/2 ≀ H)`, and
  Hayes--Sale's wreath permanence assumes the acting group sofic, so
  hyperlinearity of that crossed product is not supplied. So this direction
  needs a permanence theorem that does not exist here.
* **Containment seeds (solve-sofic-actions, 2026-09-13).** A host action containing a nonsofic group's free
  relation is nonsofic (`free-action-containing-nonsofic-group-relation-is-nonsofic`), but its crossed product
  contains `L(R_H)`, so a hyperlinear host needs a hyperlinear nonsofic seed relation: Pestov's Question 3.4 one
  level up again. No new route; Bernoulli seeds of simple Kazhdan nonsofic groups are dead in any case
  (`simple-kazhdan-bernoulli-relation-hosts-contain-the-group`).
* **Gaussian distillation (sw-121, 2026-09-17): every Theorem-C separation is a coset-wreath separation.**
  `hyperlinear-action-distills-to-stabilizer-coset-bernoulli`: a hyperlinear action with a family of sets of
  common stabilizer `Δ` makes `W_Δ = (⊕_(G/Δ) Z/2) ⋊ G` hyperlinear (products, tensor powers of a vector peaking
  exactly on `Δ`, central limit, weak-star closure). Consequences: (i) the "non-product invariant measure" escape of
  the second Attempt is closed, since `theorem-c-separation-iff-infranormal-coset-wreath` shows a hyperlinear action
  with non-invariant `Γ`-fixed algebra exists iff `W_Δ` is hyperlinear for some `Γ ≤ Δ`, `⟨⟨Γ⟩⟩ ⊄ Δ`, and the
  minimal such `Δ_hl` is infranormal; (ii) the third Attempt's gap is closed outright:
  `hyperlinear-nonsofic-free-action-from-hyperlinear-nonsofic-group` shows the Bernoulli shift of any hyperlinear
  nonsofic group is a free hyperlinear nonsofic action (free-product permanence plus the established tensor-Gaussian
  equivalence at the trivial pair make `Z/2 ≀ H` hyperlinear), so this root is implied by Pestov's Question 3.4. Live route
  `hyperlinear-nonsofic-free-action-from-infranormal-coset-wreath`, open at
  `kt-pair-hyperlinear-floor-below-normal-closure`.
