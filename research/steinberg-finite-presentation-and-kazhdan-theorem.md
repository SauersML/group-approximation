---
rg: 2
id: steinberg-finite-presentation-and-kazhdan-theorem
kind: claim
title: Steinberg groups over finitely presented unital rings are finitely presented in rank at least four and have property T
artifacts:
  - research/artifacts/boone-higman-steinberg-cover-correction-2026-09-08.md
  - research/artifacts/gq-steinberg-q-krstic-mccool-source.md
---

For a finitely presented unital associative ring R and n>=4, St_n(R)
is finitely presented and has property (T). It maps onto EL_n(R).

The finite-presentation statement is about St_n(R). No conclusion that
EL_n(R) is finitely presented follows without controlling the kernel of
this surjection. No centrality assertion for that kernel over an arbitrary
noncommutative ring is included.

## Attempts

1. **Source record (lane `gq-steinberg-q`, 2026-09-17).** The finite-presentation part is Krstić–McCool,
   J. Pure Appl. Algebra 141 (1999) 175–183, DOI 10.1016/S0022-4049(98)00022-X, Theorem 3: `St_n(B)` is finitely
   presented for every finitely presented associative unital ℤ-algebra `B` and every `n >= 4`.
   - It is quoted verbatim in two independent secondary sources: Ershov–Jaikin-Zapirain arXiv:0809.4095v2
     (e-print lines 2496–2501, via route `steinberg-finiteness-kazhdan-citation`) and Khanh arXiv:2609.08428v1.
   - The primary text is still unread; it is paywalled.
   - The bound `n >= 4` is sharp in general, by their Corollary 2 on `St_3`.
   - The explicit form over a quotient of a free ring is `st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`.
   - Details: `research/artifacts/gq-steinberg-q-krstic-mccool-source.md`.
