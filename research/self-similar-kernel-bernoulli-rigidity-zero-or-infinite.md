---
rg: 2
id: self-similar-kernel-bernoulli-rigidity-zero-or-infinite
kind: claim
title: Over a group isomorphic to its quotient by a nontrivial finite normal subgroup, the least non-rigid Bernoulli level is 0 or infinity, so over P x G the rigidity threshold is equivalent to one collapse
distinct_from:
  bernoulli-rigidity-threshold-equals-rokhlin-supremum: that is the open claim r = s at every group of finite supremum; this proves r is 0 or infinity on self-similar-kernel hosts, so there the claim is equivalent to the existence of one collapse, and it fails when 0 < s < infinity.
  zero-rokhlin-supremum-forces-bernoulli-collapse: that asks for one collapse at supremum zero; this proves that on self-similar-kernel hosts, including every P x G with finite supremum on G, one collapse makes every positive level non-rigid.
  bernoulli-isomorphism-collapse-set-is-a-subgroup: its item 8 gives s = 0 from a collapse on dichotomy hosts; this gives, on self-similar-kernel hosts, that D is closed under division by the kernel order, R is empty or everything, and on P x G that D is a Q-vector space.
  bernoulli-collapse-is-null-or-eventually-total: that splits collapse above the supremum into eventual total collapse and the threshold claim, and gives formal models separating them; this collapses the threshold half into the weak collapse on self-similar-kernel hosts and excludes the threshold model there.
  rokhlin-excess-never-drops-under-bernoulli-transfers: that proves transfers in the class T cannot lower the excess; this uses finite-kernel descent, outside T, to divide the excess on hosts isomorphic to their quotient.
  rokhlin-supremum-of-torsion-products-is-zero-or-infinite: that is a 0-infinity law for the Rokhlin supremum of P x G; this is a 0-infinity law for the least non-rigid Bernoulli level on the same hosts.
artifacts:
  - research/artifacts/bernoulli-collapse-finite-kernel-descent-2026-09-17.md
---

Proof: [[self-similar-kernel-bernoulli-rigidity-zero-or-infinite-proof]], with full details in the
artifact (Sections 3–5).

**Setting.** Notation as in `bernoulli-collapse-descends-along-finite-normal-quotients`. H2(Γ) is
`bernoulli-rigidity-threshold-equals-rokhlin-supremum` at `Γ`, and T1(Γ) is
`bernoulli-shifts-above-rokhlin-supremum-are-isomorphic` at `Γ`. A **self-similar-kernel host** is a countably
infinite group `Γ` with a finite normal subgroup `N`, `n = |N| ≥ 2`, such that `Γ/N ≅ Γ`.

**Theorem B.** Let `Γ` be a self-similar-kernel host.
1. `r(Γ) ∈ {0, ∞}`. Equivalently, `R(Γ)` is `∅` or `(0, ∞)`.
2. `D(Γ)` is closed under division by `n`.
3. If `D(Γ) ≠ {0}`, then `s(Γ) = 0` and every level in `(0, ∞)` is non-rigid. So H2(Γ) holds.
4. If `s(Γ) < ∞`, then H2(Γ) holds iff `s(Γ) = 0` and `D(Γ) ≠ {0}`. If `0 < s(Γ) < ∞`, then H2(Γ) fails and
   base entropy classifies Bernoulli shifts over `Γ`.
5. If `s(Γ) = 0`, then T1(Γ) holds iff `D(Γ) = R`.

**Theorem 4.2 (P × G).** Let `P = ⊕_(n ≥ 1) Z/nZ` and let `G` be countably infinite. Then `P × G` is a
self-similar-kernel host for every kernel order `k ≥ 2`: removing the summand `Z/kZ` leaves a group isomorphic to
`P`, because every `Z/p^e Z` occurs with infinite multiplicity. Put `Γ = P × G`.
1. `D(Γ)` is a `Q`-vector subspace of `R`, and `R(Γ)` is `∅` or `(0, ∞)`.
2. `D(G) ⊆ D(Γ)`. So one nontrivial Bernoulli isomorphism over `G` makes every positive level over `Γ` non-rigid.
3. If `s(G) < ∞`, then `s(Γ) = 0`, and three conditions are equivalent:
   - H2(Γ);
   - the conclusion of `zero-rokhlin-supremum-forces-bernoulli-collapse` at `Γ`;
   - `D(Γ) ≠ {0}`.

   Also, T1(Γ) holds iff `eventual-bernoulli-collapse-at-finite-rokhlin-supremum` holds at `Γ`.
4. If `s(G) = ∞`, then `s(Γ) = ∞`, and H2(Γ) and T1(Γ) are vacuous.

**Reading.**
- **Class kill, partly lifted.** The formal threshold model "`a ≈ b` iff `a = b` or `a, b ≥ M`" satisfies the
  one-group calculus and fails H2. It is not realizable at any self-similar-kernel host, since it has
  `R = [M, ∞)` with `M > 0`. The dense-subgroup model with `s = 0` and `C = Q` is closed under descent, so descent
  still does not give eventual collapse.
- **Gottschalk hosts.** `positive-rokhlin-via-classification-and-collapse` needs
  `zero-rokhlin-supremum-forces-bernoulli-collapse` at `P × G` for `G` with `s(G) < ∞`. At those hosts,
  - H2 is equivalent to that prerequisite;
  - T1 is equivalent to eventual total collapse;
  - one collapse at `G` itself would already give H2 at `P × G`.
- **Not done.** Nothing here proves any collapse, or H2 at a group that is not a self-similar-kernel host.
