---
rg: 2
id: compiled-hnn-stages-are-capped-inside-brin-thompson-groups
kind: claim
title: Identity-edge HNN stages compiled inside Brin-Thompson groups cannot beat coNP however they are iterated there, and in V such a stage need not embed back into V
requires:
  - machine-labelled-lamp-products-are-nv-centralizers
  - pbh-coset-wreaths-iff-identity-edge-hnns
distinct_from:
  machine-labelled-lamp-products-are-nv-centralizers: that realizes machine-coded subgroups as centralizers in one Brin-Thompson host and puts the identity-edge HNN in B_A; this asks whether that HNN returns to a Brin-Thompson group so that the compiler can iterate, and shows that iteration there is capped either way.
  type-a-actors-with-arbitrarily-hard-word-problem: that is the open hard-actor claim; this identifies it as the only recorded way for an iterated compiler to beat a fixed complexity class.
---

**ESTABLISHED, conditional on two recalled imports** (lane proof, bh-invent-11, 2026-09-18; not
reviewed). The imports were not read at source here:
- (B) Birget, *The word problem of the Brin–Thompson groups is coNP-complete* (J. Algebra, 2020):
  the word problem of `nV` is in coNP for every `n`;
- (BS) Bleak and Salazar-Díaz, *Free products in R. Thompson's group V* (Trans. AMS, 2013):
  `Z^2 * Z` does not embed in `V`.

## Statement

1. **The cap does not depend on embedding back.** Let `H_0 ≤ n_0 V` be finitely generated. Let
   `H_0 ≤ H_1 ≤ H_2 ≤ ...` be any tower in which each `H_(k+1)` is an identity-edge HNN extension
   `H_k *_(C_k) (C_k × Z)` that embeds in some Brin–Thompson group `n_(k+1) V`. Then every `H_k`
   has word problem in coNP.

   So a positive answer to "does the compiled HNN embed back into some `NV`?" lets the compiler of
   `machine-labelled-lamp-products-are-nv-centralizers` iterate, but never beyond coNP. The
   one-host cap is a Brin–Thompson cap.
2. **In V the answer is no.**
   - Let `x, y ∈ V` have infinite order, with supports in the cones `[0]` and `[1]`. Choose `y`
     as the conjugate `σx'σ` of some `x'` by the cone swap `σ : 0w ↔ 1w`. Choose `x'` so that
     `x^i ≠ x'^j` whenever `(i, j) ≠ (0, 0)`: for example, `x` has an attracting fixed point that
     `x'` moves.
   - Then `Z^2 = ⟨x, y⟩` and `C_(Z^2)(σ) = 1`, so the trivial subgroup satisfies condition (e) of
     `pbh-coset-wreaths-iff-identity-edge-hnns` inside `V`.
   - Its identity-edge HNN extension is `Z^2 * Z`, which does not embed in `V` by (BS).
   - So a stage compiled inside `V` need not return to `V`.
3. **The only recorded escape leaves Brin–Thompson groups.**
   - Condition (e) puts the compiled stage in `B_A` through the relative-automorphism construction
     in the proof of `pbh-coset-wreaths-iff-identity-edge-hnns`, not in a Brin–Thompson group. The
     word problems of the resulting simple hosts are not bounded by `nV`.
   - The recorded hosts of unbounded complexity are twisted Brin–Thompson groups `SV_Γ`, whose word
     problem is the orbit problem of the actor (`twisted-brin-thompson-wp-equals-actor-orbit-problem`).
   - So an iterated compiler beats a fixed class only if the actors it produces do, which is the
     open claim `type-a-actors-with-arbitrarily-hard-word-problem`.

## Proof

**(1).** Each `H_k` is a finitely generated subgroup of `n_k V`. A word of length `ℓ` in its
generators rewrites to a word of length `O(ℓ)` in fixed generators of `n_k V`, so (B) puts its word
problem in coNP. The tower structure plays no role. The HNN stages cannot add hardness beyond that
of the ambient `n_k V`.

**(2).** The supports of `x` and `y` are disjoint, and both have infinite order, so `⟨x, y⟩ ≅ Z^2`.
- Conjugation by `σ` swaps the cones, so `σ x^i y^j σ = (σxσ)^i x'^j`, with `σxσ` supported in
  `[1]` and `x'` in `[0]`.
- Equality with `x^i y^j` forces `x'^j = x^i` on `[0]`. By the choice of `x'` this means
  `i = j = 0`.
- The identity-edge HNN extension over `C = 1` is `⟨Z^2, t⟩ = Z^2 * Z`.
- Condition (e) holds with `M = V ∈ B_A`. This is consistent: `Z^2 * Z` is in `B_A` (it lies in a
  right-angled Artin group), just not in `V`.

**(3)** restates the cited nodes. `∎`

## Open

- **Embedding into higher-rank groups.** Does every identity-edge HNN compiled inside `nV` embed
  in some `NV` with `N >= 2`? It suffices that the `G`-conjugates of the detector `m` form a free
  family meeting `G` trivially. That would make `⟨G, m⟩ = (∗_(G/C) ⟨m⟩) ⋊ G`.
- **Where the free conjugates fail.** In the lamp compiler they fail: `[m, a^C m a^(-C)]` acts
  trivially on the whole machine orbit, because each branch emits once. A positive answer needs
  ping-pong dynamics for `m` off the orbit, where the completion of the machine can be chosen
  freely.
- **Z²∗Z.** Whether `Z^2 * Z` embeds in `2V` is not settled here.

## Lesson for general BH (and for CAP)

- **Iterating is not the issue.** Iterating the in-host compiler cannot beat a complexity cap as
  long as each stage lands back in a Brin–Thompson group. Every subgroup of every `nV` has coNP
  word problem.
- **Where the question lies.** "Does the compiled HNN embed back?" is a question about the class of
  subgroups of Brin–Thompson groups. The answer is already no in `V` (`Z^2 * Z`). It is not a
  complexity question.
- **For CAP.** A machine-simulating HNN tower (rung 1c) that beats CAP must leave Brin–Thompson
  groups at some stage. Its hosts must be twisted Brin–Thompson groups over actors that are
  themselves harder. So the rung reduces to hard type (A) actors, not to compilers.
