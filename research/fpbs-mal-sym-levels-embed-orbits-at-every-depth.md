---
rg: 2
id: fpbs-mal-sym-levels-embed-orbits-at-every-depth
kind: claim
title: For d >= j+2 the Cayley level of Sym(d) with a = (0 1) and b = (0 1 ... d-1) has L_j acting as Sym(d-j) on d-j points, and every component of its folded L_j-graph embeds in the level; at d = j+2 all L_j-orbits have size 2 with a and t_j acting as the same swap
distinct_from:
  fpbs-mal-overfold-merges-never-help: that is the open exchange statement deep_j = law_j; this is a structural fact about one explicit family of levels, which forces every overfold seed on it and on all of its covers to join two different L_j-orbits.
  fpbs-mal-depth-promotion-equals-overfold-merge-number: that defines deep_j and law_j and computes Q_j from them; this computes the L_j-orbits and the embedding of Gamma_j on the Sym(d) levels and says nothing about merge numbers.
  fpbs-mal-twisted-level-seed-density-uniform-witness: that is a lower bound on r(Q_m^(j)) on random-lift towers over a point; this is a statement about L_j-orbit structure on a fixed finite level.
artifacts:
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/elevels.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/ecensus.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/small_h.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/eb_verify.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/eb_family.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/family_d4_d10.txt
---

**ESTABLISHED** through `fpbs-mal-sym-levels-embed-orbits-at-every-depth-proof`.

**Setting.** Notation is as in
[[fpbs-mal-depth-promotion-equals-overfold-merge-number]].
- `L = F(a, b)` acts on the right. `φ(a) = a`, `φ(b) = b a b^{-2}`,
  `t_j = φ^j(b)` and `L_j = φ^j(L) = <a, t_j>`.
- `C_j` is the Stallings graph of `L_j` (the folded bouquet of `a` and
  `t_j`), with base vertex `o`. For a vertex `c`, `u_c` is the label of any
  path `o → c`. Distinct vertices `c` give distinct cosets `L_j u_c`.
- `X_d = {0, …, d−1}`. The homomorphism `π_d : L → Sym(d)` sends `a` to
  `α = (0 1)` and `b` to `β : x ↦ x+1 mod d`. Permutations act on the right:
  `x·(gh) = (x·g)·h`. Write `x·w` for `x·π_d(w)`.
- `H_j = π_d(L_j) = <α, τ_j>`, where `τ_j = π_d(t_j)`.
- The **Cayley level** `Q = Sym(d)` is the finite `L`-set with
  `g·w = g π_d(w)`. It is transitive, since `α` and `β` generate `Sym(d)`.
  Its `L_j`-orbits are the left cosets `g H_j`.
- **(E) at depth `j`**: no two distinct vertices of one component of
  `Γ_j(Q)` lie over the same point of `Q`.

**Claim.** Let `d ≥ 3` and `0 ≤ j ≤ d − 2`.

1. `L_j` fixes a set `T_j ⊆ X_d` of exactly `j` points, and acts on the other
   `d − j` points as the full symmetric group. So `H_j ≅ Sym(d − j)`.
2. The map `V(C_j) → X_d^{T_j}`, `c ↦ (x·u_c)_{x ∈ T_j}`, is injective.
   Hence the right cosets `H_j π_d(u_c)`, `c ∈ V(C_j)`, are pairwise
   distinct.
3. The Cayley level of `Sym(d)` satisfies (E) at depth `j`. So does every
   finite `L`-set `Q̃` with an `L`-equivariant map onto it.
4. At `d = j + 2`: `H_j = <α>` has order 2 and `τ_j = α`. So every
   `L_j`-orbit of the Cayley level `B_j` of `Sym(j+2)` has exactly two
   points, and `a` and `t_j` both act on it as the same swap `g ↦ gα`.

**Consequence for overfolds.** Let `Q̃` cover `B_j`. By item 3, two distinct
vertices of `Γ_j(Q̃)` over the same point lie in different components, that
is, over different `L_j`-orbits. An overfold seed of
[[fpbs-mal-overfold-merges-never-help]] is a same-fibre pair `(v, v')` of
`Γ_{j+1}(Q̃)` with `m(v) ≠ m(v')`. So on every cover of `B_j`, **every
overfold seed joins two different `L_j`-orbits**. The within-orbit overfold
seeds, which the open claim must also control on a general level, do not
occur there.

**Checks.** `eb_family.py 4 10 9` gives `family_d4_d10.txt`. For
`d = 4, …, 10` and every `j ≤ d − 2`, it reports `|H_j| = (d−j)!`, (E) at
depth `j`, and `τ_{d−2} = α`. At `j = d − 1`, `τ_j = id` and (E) fails, so
the bound `j ≤ d − 2` is sharp for this family.
