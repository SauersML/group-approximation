---
rg: 2
id: binary-three-address-strict-automata-linear-proof
kind: route
title: Balance leaves seventeen rules; single flips, coset backgrounds and a selector flip system kill all but parity outside cyclic or order-three memory groups
target: binary-three-address-strict-automata-are-linear
requires:
  - three-address-binary-injective-rules-are-balanced
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/binary-three-address-strict-automata-linear-2026-09-16.md
---

Artifact, Sections 1 to 6. Scripts are in
`experiments/every-group-is-binary-surjunctive-2026-09-16/`.

- **Facts (Section 1).**
  - `tau = tau' o R_g`, where `tau'` has memory `M g^-1`.
  - A memory inside `H` makes `tau` a product of copies of `tau_H`, one for each coset of `H`.
  - So a sofic `<M m^-1>` forces injective automata to be surjective (`sofic-groups-are-surjunctive`).
- **Reduction (Section 2).**
  - Minimal memory has at most three elements.
  - The rule is balanced (`three-address-binary-injective-rules-are-balanced`).
  - `mu(0) != mu(1)`.
  - Sizes zero, one and two die at once.
  - At size three, a hand table gives seventeen normalized rules. `three_address_classify.py`
    confirms the count.
- **Majority (Section 3).** `tau(delta_k) = tau(0)`, since at most one address reads `k`.
- **Twelve rules (Section 4).** Each has `r` with `mu(e_r) = mu(e_p + e_q)`. With `U = <m_q m_p^-1>`,
  either `m_r m_p^-1 in U`, and then the memory group is `U`, which is cyclic; or `1_{U m_p}`, or its
  complement, has constant image.
- **Selector rules (Section 5).**
  - After translating the selector to `1`, flipping `x(1)` is invisible iff three edge equations over
    `F_2` hold: `y(a) = y(b)`, `y(a^-1) != y(a^-1 b)` and `y(b^-1) != y(b^-1 a)`.
  - The only obstruction is an equality edge doubled by an inequality edge. That forces `a^3 = 1` and
    `b = a^-1`, so the memory group has order three.
- **Conclusion (Section 6).** Parity is left, and the memory group is not sofic.
  - Proposition 6.2 is linear algebra: `L` is the transpose of right multiplication by `gamma`, so
    strictness of `L` means `gamma` is left invertible and not a unit.
- **Cross-checks (Section 7).** Evidence only.
  - Brute-force injectivity over finite groups agrees with every prediction.
  - The Lemma C backgrounds and the flip criterion were checked directly, including on `S4`, `D8` and
    `Z3 x S3`. The `A5` run did not finish within the time cap.
