---
rg: 2
id: sl3z-ozawa-corona-kernel-dichotomy-proof
kind: route
title: Reduce to the corona, descend quasitraces that vanish on the trace kernel to the exact reduced algebra, and use the unique trace for the converse
target: sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible
requires: [kazhdan-block-algebras-contain-their-block-ideal, sl3z-ozawa-block-corona-has-unique-trace]
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

Full proof: `research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md` §§3–4.

1. **Reduce to the corona.** By `kazhdan-block-algebras-contain-their-block-ideal`,
   (1) is equivalent to linearity of bounded 2-quasitraces on `A`.
2. **(2) ⟹ linearity.** Let `σ` be a quasitrace on `A` with `σ|_K = 0`. Then
   `K ⊂ N_σ`, the square-null ideal. So `σ` factors through `A/N_σ`, a quotient
   of `A/K = C*_r(SL(3,Z))`. That algebra is exact, because `SL(3,Z)` has property
   A. By Haagerup's theorem the descended quasitrace is a trace.
3. **Linearity ⟹ (2).** Suppose `σ(a) ≠ 0` for some `a ∈ K_+`. If `σ` were a
   trace, uniqueness of the trace would give `σ = σ(1) τ_0`, and `τ_0(a) = 0`.
4. **Exact `K`.** `σ` restricted to `C*(K, 1)` is a trace by Haagerup, so `σ|_K`
   is a bounded trace on `K`. By the ideal-extension lemma of
   `sl3z-ozawa-block-corona-unique-trace-proof`, step 4, this is zero.
5. **Infinitesimal elements.** Suppose `⊕_m (a − ε)_+ ≲ e_11 ⊗ 1`. Then there are
   rows `s_n` with `s_n* s_n → ⊕_m (a − ε)_+`. By continuity,
   `m σ((a − ε)_+) = lim σ(s_n s_n*) ≤ σ(1)`. Letting `m → ∞` and then `ε → 0`
   gives `σ(a) = 0`.

Literature imports:
- Haagerup's theorem, as in `blackadar-rordam-haagerup-k0-states-are-traces-citation`;
- exactness of countable linear groups [GHW04], as in
  `stw01-kun-thom-reduced-group-algebras-are-qt-linear`;
- extension of 2-quasitraces to `M_n(A)` and norm continuity (Blackadar–Handelman),
  checked against Milhøj–Rørdam arXiv:2309.17412 §2.
