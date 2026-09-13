---
rg: 2
id: sofic-free-actions-are-soe-invariant-proof
kind: route
title: Truncate the sheets of a subset meeting every class, amplify by finite full relations, and pass to the limit
target: sofic-free-actions-are-soe-invariant
requires:
  - cordeiro-sofic-relation-permanence
  - paunescu-sofic-action-class-permanence
artifacts:
  - research/artifacts/paunescu-class-measure-equivalence-2026-09-12.md
---

# Proof

Full text: Section 2 of the artifact. "Sofic relation" is Cordeiro's Definition
2.1, which agrees with Păunescu's Definition 1.13 (artifact Section 1).

**Amplification.** Normalize `m(W) = 1`.

1. Feldman--Moore gives a countable group `K = {k_1 = id, k_2, ...}` of
   `m`-preserving automorphisms generating `R`. Put `i(w) = min{i : k_i w ∈ V}`
   and `W_i = {i(w) = i}`. These cover almost all of `W`.
2. For `P_n = ⊔_{i<=n} W_i` the map `ι_n(w) = (k_{i(w)} w, i(w)) ∈ V × [n]` is
   injective, measure preserving onto its image, and carries `R|_{P_n}` onto the
   restriction of `R|_V × [n]^2` to `ι_n(P_n)`. The finite full relation `[n]^2` is
   sofic (Cordeiro Corollary 3.5), the product is sofic (Theorem 3.6), and the
   restriction is sofic (Proposition 3.2(a)). So `R|_{P_n}` is sofic.
3. Put `δ_n = m(W ∖ P_n) → 0` and `c_n(φ) = 1_{P_n} φ 1_{P_n}`. Then `c_n` moves
   every `φ ∈ [[R]]` by at most `2δ_n`, is multiplicative up to `2δ_n`, and moves
   traces by at most `δ_n`. Composing an almost morphism of `R|_{P_n}` that is
   accurate on the words of length at most four in `c_n(F ∪ F·F)` with `c_n` gives
   an `(F, ε)`-almost morphism of `R` once `δ_n < ε/20`. Approximate isometry on
   those words follows from the trace formula for the distance recorded in
   Cordeiro's Theorem 2.2.

**SOE invariance.** `a` sofic ⟹ `R_a` sofic (Păunescu Proposition 1.15) ⟹
`R_a|_A` sofic (Cordeiro 3.2(a)) ⟹ `R_b|_B` sofic ⟹ `R_b` sofic (amplification)
⟹ `b` sofic (1.15). Symmetric.

**Connes embeddability.** `M(R|_A) = 1_A M(R) 1_A`, and if `A` meets almost every
class then `M(R)` is a corner of `M_n(M(R|_A))` for the truncations above, up to
the same limit. Corners, matrix amplifications and increasing unions preserve
embeddability in `R^ω`.
