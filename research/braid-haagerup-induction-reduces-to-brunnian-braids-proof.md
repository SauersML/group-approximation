---
rg: 2
id: braid-haagerup-induction-reduces-to-brunnian-braids-proof
kind: route
title: Strand-deleting maps control everything outside finitely many Brunnian cosets
target: braid-haagerup-induction-reduces-to-brunnian-braids
requires: []
artifacts:
  - research/artifacts/zp-braid-haagerup-b4-attacks-2026-09-13-part3.md
---

(⇒) Restrict a proper cnd function.

(⇐) Let `ψ_{n−1}` be proper cnd on `P_{n−1}`, let `d_i` delete strand `i`, and put `ψ_0 = Σ_i ψ_{n−1} ∘ d_i`.
Let `ψ_K` be cnd on `P_n` and proper on `Brun_n`, and set `ψ = ψ_0 + ψ_K`.

- If `ψ(g) ≤ R`, the tuple `(d_1(g), …, d_n(g))` lies in a finite set. Its kernel is `Brun_n`, so `g` lies in
  finitely many cosets `g_j Brun_n`.
- `√ψ_K` is subadditive, since `ψ_K = ‖b‖²` for a cocycle `b` with `b(xy) = b(x) + π(x) b(y)`. So `k ∈ Brun_n`
  with `g_j k` in the sublevel set satisfies `√ψ_K(k) ≤ √ψ_K(g_j^{-1}) + √R`, and there are finitely many
  such `k`.

So `ψ` is proper on `P_n`, and `B_n` has the property by induction to the finite-index overgroup.

`Brun_n ≤ ker(P_n → P_{n−1}) ≅ F_{n−1}` is free. It is infinite for `n ≥ 3`: for example
`[[A_{14}, A_{24}], A_{34}] ∈ Brun_4`, a nontrivial commutator of free basis elements.

Full text: §1 of `research/artifacts/zp-braid-haagerup-b4-attacks-2026-09-13-part3.md`.
