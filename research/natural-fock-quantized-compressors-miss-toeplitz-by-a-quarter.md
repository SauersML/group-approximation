---
rg: 2
id: natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter
kind: claim
title: Second quantization of the forced truncated compressor shifts fails the Toeplitz commutator by normalized rank exactly one quarter
distinct_from:
  natural-compressor-extension-fails-at-toeplitz-commutator: that computes the one-particle defect, a single transvection; this computes its second quantization on the Fock space, where the defect has normalized rank exactly 1/4 at every level.
artifacts:
  - research/artifacts/fock-local-rank-models-2026-09-12.md
---

**ESTABLISHED** (proof: Section 3 of the linked artifact, route
`natural-fock-compressor-toeplitz-quarter-proof`).

**Statement.**
- **The forced solution.** Proposition 7 of `research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md`
  gives, on `W_N = F_2^N ⊕ F_2^N ⊕ F_2^N`, `X^ = 1 + T_N E_12`, `Y^ = 1 + S_N E_23`, `Z^ = 1 + E_13`, with
  `Z^^(−1)[X^, Y^] = u_13(N−1, N−1)`.
- **Fock identity.** `Λ(Z^)^(−1)[Λ(X^), Λ(Y^)] = Λ(u_13(N−1, N−1))` on `Λ(W_N)`.
- **Rank.** For any transvection `u = 1 + v ⊗ φ` with `φ(v) = 0` on a space of dimension `n >= 3`, over any
  field, `Λ(u) − 1 = v ∧ i_φ` has rank `dim Λ / 4`, and the same proportion on `Λ^odd` and on `Λ^even`.

**Consequence.** Fock quantization of the natural compressor extension fails the Toeplitz commutator
`[x_12(t0), x_23(s0)] = x_13(1)` by normalized rank exactly `1/4` at every level, so the error does not
decay. Fock-local constructions must represent the compressor pair by abstract non-level letters, and
the Toeplitz commutator is a relation between letters with overlapping supports, which locality does not
supply.
