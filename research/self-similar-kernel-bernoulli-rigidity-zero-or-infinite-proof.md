---
rg: 2
id: self-similar-kernel-bernoulli-rigidity-zero-or-infinite-proof
kind: route
title: Transport collapse data along the isomorphism with the quotient and apply finite-kernel descent, which divides the least non-rigid level by the kernel order
target: self-similar-kernel-bernoulli-rigidity-zero-or-infinite
requires:
  - bernoulli-collapse-descends-along-finite-normal-quotients
  - bernoulli-collapse-is-null-or-eventually-total
  - bernoulli-isomorphism-collapse-set-is-a-subgroup
  - rokhlin-supremum-of-torsion-products-is-zero-or-infinite
artifacts:
  - research/artifacts/bernoulli-collapse-finite-kernel-descent-2026-09-17.md
---

"Section n" refers to the artifact. The prerequisites supply:
- descent `D(Q)/n ⊆ D(Γ)` and `r(Γ) ≤ r(Q)/n` for `Q = Γ/N` (items 1–2 of the first);
- `R(Γ) ⊆ [s, ∞)`, upward closed, non-empty iff `D ≠ {0}`, and T1 ⇔ (`D = R` and `r = s`) (items 3–4 of the second);
- `D` is a subgroup, with permanence to overgroups (items 3 and 7 of the third);
- `s(P × G) = 0` if `s(G) < ∞`, and `= ∞` otherwise (items 1–2 of the fourth).

**Theorem B (Section 3).**
- An isomorphism `Γ/N ≅ Γ` transports Bernoulli shifts and Rokhlin entropy. So `D`, `R`, `r` and `s` agree for
  `Γ/N` and `Γ`.
- Item 1: descent gives `r(Γ) ≤ r(Γ)/n` with `n ≥ 2`, so `r(Γ) ∈ {0, ∞}`. Then upward closure gives
  `R(Γ) ∈ {∅, (0, ∞)}`.
- Item 2: descent with `D(Γ/N) = D(Γ)`.
- Item 3: `D ≠ {0}` makes `R ≠ ∅`, so `r = 0`, and `s ≤ r` gives `s = 0`.
- Item 4: H2 with `s < ∞` gives `r = s < ∞`, so `r = 0 = s` and `D ≠ {0}`. If `0 < s < ∞`, item 3 gives `D = {0}`.
- Item 5: if `s = 0` and `D = R`, then item 3 gives `r = 0 = s`, and T1 follows from the second prerequisite.

**Theorem 4.2 (Section 4).**
- *Lemma 4.1.* By the Chinese remainder theorem, `P` and `P' = ⊕_(n ≠ k) Z/nZ` are direct sums of the `Z/p^e Z`.
  Each summand has countably infinite multiplicity in both, so `P' ≅ P`, and `(P × G)/(Z/kZ) ≅ P × G`.
- Item 1: Theorem B(1)–(2) for every `k`, together with the subgroup property.
- Item 2: permanence `D(G) ⊆ D(P × G)`, with Theorem B(3).
- Items 3 and 4: the fourth prerequisite, with Theorem B(4)–(5).

**Formal models (Section 5).** The threshold model has `R = [M, ∞)` with `M > 0`, which item 1 excludes. The
dense model with `C = Q` and `s = 0` is closed under division by every `n`.
