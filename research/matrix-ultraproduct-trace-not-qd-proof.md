---
rg: 2
id: matrix-ultraproduct-trace-not-qd-proof
kind: route
title: Push the amenable non-QD group trace forward into the ultraproduct
target: matrix-tracial-ultraproduct-trace-not-quasidiagonal
requires: [stw99-problem-x1-fails-on-full-group-algebras]
artifacts:
  - research/artifacts/x2-popa-formulations-ingestion-2026-08-30.md
---

**Pullback lemma (routine).**  Quasidiagonal traces pull back along
unital \*-homomorphisms: if `π : A → B` is a unital \*-homomorphism and
`σ` is a quasidiagonal trace on `B`, then `σ ∘ π` is quasidiagonal —
for a finite `F ⊂ A`, compose a model `ψ` for `σ` that is
norm-multiplicative on `π(F)` with `π`; `ψ∘π` is u.c.p., its
multiplication defect on `F` is `ψ`'s on `π(F)` (exactness of `π`), and
`tr∘ψ∘π ≈ σ∘π` on `F`.

**Forward map from the witness.**  By the premise there is a countable
group `G` (the literal group `E`) whose canonical trace `τ_G` on the
separable algebra `C*(G)` is amenable and not quasidiagonal.
Amenability gives u.c.p. maps `φ_j : C*(G) → M_{m_j}` with
Hilbert--Schmidt multiplication defects `→ 0` on a dense sequence and
`tr∘φ_j → τ_G` pointwise.  For an arbitrary size sequence `k_n → ∞`,
transport `φ_j` into `M_{k_n}`: block-embed `⌊k_n/m_j⌋` copies of
`M_{m_j}` and pad by a rank-`(k_n mod m_j)` corner on which the map is
`τ_G(·)·1`; this is still u.c.p., block-diagonal (no cross terms), and
it adds `O(√(m_j/k_n))` to the normalized Hilbert--Schmidt
multiplication defect (the corner contributes
`|τ_G(xy) − τ_G(x)τ_G(y)| · √((k_n mod m_j)/k_n)`) and `O(m_j/k_n)` to
the trace distortion.  Choosing `j(n)`
slowly, the sequence `ψ_n : C*(G) → M_{k_n}` has all defects `→ 0`
along `ω`, so it descends to a map

```text
π : C*(G) → Q = ∏_ω M_{k_n} / J_HS
```

which is unital, \*-preserving, and multiplicative (defects die in the
`J_HS` quotient on the dense sequence; all maps are complete
contractions, so multiplicativity extends to the norm closure by joint
norm-continuity of the product on bounded sets), with
`τ_ω ∘ π = τ_G`.

**Conclusion.**  If `τ_ω` were quasidiagonal on `Q`, the pullback lemma
would make `τ_G = τ_ω ∘ π` quasidiagonal — contradicting the premise.
So `τ_ω` is not quasidiagonal, for every `k_n → ∞` and every free `ω`.

Model check on the lemma's one subtle point: the models for `σ` must be
defined on all of `B` (u.c.p. globally, multiplicative only on the given
finite set) — that is Brown's definition, and it is what composition
with a globally defined \*-homomorphism preserves; no lifting of any
quotient is used anywhere.
