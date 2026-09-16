---
rg: 2
id: automatic-va-or-free-subsemigroup-proof
kind: route
title: Pump a regular language with uniqueness into a free submonoid, or get polynomial growth and use Gromov and the nilpotent case
target: automatic-groups-virtually-abelian-or-free-subsemigroup
requires:
  - automatic-groups-admit-structures-with-uniqueness
  - gromov-and-milnor-wolf-growth-alternatives
  - finite-index-subgroups-of-automatic-groups-are-automatic
  - automatic-nilpotent-groups-are-virtually-abelian
artifacts:
  - research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md
---

The full proof is Sections 1–3 of the artifact. It is outlined here.

1. **Linear length (Lemma 1).** Take an automatic structure `(A, λ, L)` with uniqueness
   (`automatic-groups-admit-structures-with-uniqueness`). Let `S` bound the number of
   states of deterministic automata for the multiplier languages `M_a`. If
   `|w_{gλ(a)}| > |w_g| + S`, the run on the padded pair `(w_g, w_{gλ(a)})$` repeats a
   state in its `($, x)` tail. Pumping that segment down gives a shorter word of `L`
   representing `gλ(a)`, which contradicts uniqueness. So `|w_g| <= S|g| + |w_1|`, and
   `β_L(n) <= β_G(n) <= β_L(Sn + |w_1|)`.
2. **Language dichotomy (Lemma 3).** Take a trim deterministic automaton for `L`.
   - If some state has two distinct first-return loops `u ≠ v`, then `{u, v}` is a prefix
     code and `a ↦ u`, `b ↦ v` is injective on `{a, b}*`.
   - Otherwise every nontrivial strongly connected component is a single cycle, and
     `β_L(n) <= K(n + 1)^s`.
3. **Polynomial case.** `G` has polynomial growth by step 1, so it is virtually nilpotent
   by `gromov-and-milnor-wolf-growth-alternatives`. A nilpotent subgroup of finite index is
   automatic (`finite-index-subgroups-of-automatic-groups-are-automatic`), hence
   virtually abelian (`automatic-nilpotent-groups-are-virtually-abelian`). So `G` is
   virtually abelian.
4. **Pumping case.** With `q_0·x = q` and `q·z` accepting, `x φ(α) z ∈ L` for all `α`.
   Distinct `α` give distinct words, and by uniqueness distinct elements
   `λ(x) ψ(α) λ(z)`, where `ψ = λ ∘ φ`. Cancelling `λ(x)` and `λ(z)` shows that `ψ` is
   injective. So `λ(u)` and `λ(v)` freely generate a free submonoid, and its nonempty
   words form a free subsemigroup of rank 2.

The outcomes are exclusive because a free subsemigroup of rank 2 forces exponential
growth, while virtually abelian groups grow polynomially.
