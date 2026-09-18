---
rg: 2
id: bernoulli-collapse-descends-along-finite-normal-quotients
kind: claim
title: A Bernoulli isomorphism over a quotient by a finite normal subgroup gives one over the group at levels divided by the kernel order, plus any positive translation
distinct_from:
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that proves permanence of collapse to overgroups (levels kept) and finite-index subgroups (levels multiplied by the index); this proves descent along finite normal quotients, which divides levels by the kernel order.
  rokhlin-excess-never-drops-under-bernoulli-transfers: that proves the excess over the supremum never drops under translation, co-induction and finite-index restriction; this is a transfer outside that class, which divides the excess by the kernel order on groups isomorphic to their quotient.
  coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli: that is the absorption theorem for co-induced shifts over one group; this applies it to generalized shifts over a finite normal quotient to move Bernoulli isomorphisms from the quotient to the group.
  rokhlin-entropy-quotient-formula-for-finite-normal-subgroups: that compares Rokhlin entropies of an action and its quotient by a finite normal subgroup; this moves Bernoulli isomorphisms, not entropy values.
  bernoulli-collapse-ascends-to-universal-hosts: that pushes collapse up to supergroups and universal hosts; this pulls collapse from a quotient back to an extension with finite kernel.
  bernoulli-rigidity-threshold-equals-rokhlin-supremum: that is the open claim that non-rigid levels reach down to the supremum; this bounds the least non-rigid level of an extension by that of the quotient divided by the kernel order.
artifacts:
  - research/artifacts/bernoulli-collapse-finite-kernel-descent-2026-09-17.md
---

Proof: [[bernoulli-collapse-descends-along-finite-normal-quotients-proof]], with full details in the artifact
(Sections 1–2).

**Setting.**
- `Γ` is countably infinite, `N ◁ Γ` is finite with `n = |N|`, and `Q = Γ/N`.
- `X_h` is the Bernoulli shift of base entropy `h`, and `s(·) = h^Rok_sup(·)`.
- `D(·)` is as in `bernoulli-isomorphism-collapse-set-is-a-subgroup`. `R(·)` and `r(·)` are as in
  `bernoulli-collapse-is-null-or-eventually-total`.

**Theorem A.** If `0 < a, b < ∞` and `X_a ≅ X_b` over `Q`, then `X_(c + a/n) ≅ X_(c + b/n)` over `Γ` for every
`c ∈ (0, ∞)`.

**Corollary.**
1. `D(Q)/n ⊆ D(Γ)`.
2. `r(Γ) ≤ r(Q)/n`. More precisely, if `a ∈ R(Q)`, then `(a/n, ∞) ⊆ R(Γ)`.
3. `s(Γ) ≤ r(Q)/n`.
4. If base entropy classifies Bernoulli shifts over `Γ`, then it classifies them over `Γ/N`.

**Mechanism.**
- `Γ` acting on `L^Q` through `Q` is the co-induction `Coind_N^Γ(L)` with trivial `N`-action, because `N` is normal.
- Corollary D of `coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli` absorbs it: `L^Q × K^Γ ≅ X_(H(K) + H(L)/n)`.
- A `Q`-isomorphism `L_a^Q ≅ L_b^Q` is `Γ`-equivariant, so multiplying by `K^Γ` gives the theorem.

**Reading.**
- This transfer is not in the class `T` of `rokhlin-excess-never-drops-under-bernoulli-transfers`. On a group with
  `Γ/N ≅ Γ`, it divides levels by `n`, so the excess Lyapunov function of that node can decrease.
- The consequences on such groups are `self-similar-kernel-bernoulli-rigidity-zero-or-infinite`.
