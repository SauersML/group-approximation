---
rg: 2
id: rf-lamp-wreath-surjunctivity-by-marked-site-peeling
kind: route
title: Transplant to marked-site coset spaces and peel stabilizer-coset strata by the coset-region lemma
target: rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive
requires: []
artifacts:
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Complete direct proof, Sections 1--5 of the linked artifact.

* **Lemma 1.1.** Transplanting to any right coset space preserves
  injectivity.
* **Lemma 1.2.** Surjective transplants along a separating family force
  surjectivity.
* **Lemma 2.1.** The subgroups `H_(S,A_0)`, fixing lamp classes modulo a
  finite-index normal `A_0` at finitely many sites `S`, separate `W`. This
  uses residual finiteness of `A`.
* **Lemma 2.2.** On `(A/A_0)^S x G` the rule is uniform off the strata `Z_s`.
  Each `Z_s` is a finite union of right cosets of `Stab_G(s)`, and the rule
  commutes with left translation by the pointwise stabilizer of `S`.
* **Lemma 2.3.** Away from the strata of `U\V`, the `U`-transplant is the
  slicewise `V`-transplant.
* **Lemma 3.1 (coset-region lemma).** Let `rho` be an injective finite-memory
  map that is the identity off finitely many right cosets of a surjunctive
  `K`, with `K`-invariant rules on them. Then `rho` is a cellular automaton
  over `K` with boundary labels, hence bijective with a finite-memory inverse.
* **Proposition 4.1.** Induct over the subsets `U` of `S` in order of
  cardinality. Composing `tau_U` with slicewise inverses for all proper
  subsets makes it the identity off finitely many right cosets of
  `G_U = intersection_(s in U) Stab_G(s)`. Lemma 3.1 then applies with
  `K = G_U`, which is surjunctive because it is a subgroup of `G`.

The converse direction is subgroup heredity of surjunctivity. The standard
background used is Curtis--Hedlund--Lyndon over arbitrary groups (the inverse
of a bijective automaton is an automaton), subgroup heredity, and
compactness.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 1 of
the verification artifact).
