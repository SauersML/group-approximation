---
rg: 2
id: confined-subgroup-pigeonhole-commutator-lemma
kind: claim
title: "A subgroup confined by a set of r elements contains a conjugate of [p, g_i g_j^{-1}] for some p in the set and two of any r+1 chosen conjugators"
artifacts:
  - research/artifacts/sk-cstar-genericity-2026-09-14-part1.md
distinct_from:
  unit-group-confined-subgroups-idempotent-commutator-lemma: that puts rigid subgroups into confined subgroups through idempotent displacement configurations; this is the formal pigeonhole step that puts commutators with arbitrary chosen conjugators into any confined subgroup, with no configuration
---

**ESTABLISHED (unreviewed).** Let `H ≤ Γ` be confined by a finite `P ⊆ Γ∖{1}` (`gHg^{-1} ∩ P ≠ ∅` for all `g ∈ Γ`), `|P| = r`, and `g_1, …, g_{r+1} ∈ Γ`. Then some `p ∈ P` and `i ≠ j` satisfy `g_i^{-1}[p, g_ig_j^{-1}]g_i ∈ H`, where `[a,b] = aba^{-1}b^{-1}`.

**Consequences.**
- (R′) If for every finite `P` and every `n` some `g_1..g_n` make every `[p, g_ig_j^{-1}]` (`p ∈ P`, `i ≠ j`) of infinite order, then every confined subgroup contains an element of infinite order.
- (R″) With `[p, g_ig_j^{-1}]^e ≠ 1` instead, no nontrivial subgroup of exponent dividing `e` is confined.

**Why it matters.** It reduces (L3) of the idempotent route to C*-simplicity of `G_X` (excluding confined subgroups inside `B_4 ∪ {1}`, of exponent dividing 420 by `polynomially-small-units-have-order-dividing-420`) to single-element statements about commutators.
