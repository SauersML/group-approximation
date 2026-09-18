---
rg: 2
id: proper-sft-cover-quotient-and-microstate-count-proof
kind: route
title: Lift one coset or one separated color class at a time, then count words that avoid a forbidden pattern
target: proper-sft-covers-exclude-finite-orbits-and-sofic-constants
requires: []
artifacts:
  - research/artifacts/constant-point-domain-count-2026-09-17.md
---

The full proof is in the artifact, §1–§3. Outline:

**Local lift rule (§1).** Validity of a rewrite of `x` on `Φ` (landing in `X`, changing the output only at
`1`, to a prescribed value) is checked on the finite set `K = Φ(W⁻¹W ∪ N⁻¹N)`. Taking the least valid
rewrite gives a rule that is defined at every genuine point of `X`, because the strong lift supplies one
valid rewrite. Rules at sites `g_i` with `g_i⁻¹g_j ∉ KK⁻¹` commute and compose to a point of `X`.

**Part 1 (§2).** Let `x ∈ X` be `H`-fixed. Apply the rule at `g_0` and copy the rewrite to every `hg_0Φ`,
`h ∈ H`. When `H ∩ ΦUΦ⁻¹ = {1}`, every window and every memory set meets at most one copy, so the result is an
`H`-fixed point of `X` whose image is `F(x)` with the coset `Hg_0` changed. Repeating once per coset makes `F`
map `Fix_H(X)` onto `Fix_H(A^G)`, which has `|A|^{[G:H]}` points. But `H ∩ PP⁻¹ = {1}` makes the forbidden
pattern `p` embed in `H\G`, so `|Fix_H(X)| ≤ |A|^{[G:H]} − |A|^{[G:H]−|P|}`. For residual finiteness, pass
from the stabilizer of a finite orbit to a deeper finite-index normal subgroup avoiding `B`.

**Part 2 (§3).** Take a sofic model `V` and a proper coloring of the `KK⁻¹`-graph with `k` colors. Starting
from the constant word `a^V`, apply the rule at the very good points of color `j` in round `j`. By induction,
each very good point sees a window equal to the window of a genuine point of `X` (the constant point is the base
case). So the final word has the prescribed output at every very good point and avoids `p` there. This gives
`|A|^{(1−ε)|V|}` words avoiding `p` at `(1−ε)|V|/|PP⁻¹|` disjoint places, which is impossible for small `ε`.
