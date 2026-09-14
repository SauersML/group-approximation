---
rg: 2
id: fp-subexponential-growth-forces-sqrt-mod-p-betti-bound
kind: claim
title: "A finite presentation of a group of subexponential growth has deficiency at most one, and finite-index subgroups of index j have mod-p first Betti number at most 2 + 2√(j(|R| − |X| + 1))"
distinct_from:
  fp-intermediate-growth-witness-exclusions: that collects cover, normal-subgroup, gap and endomorphic-presentation constraints; this is a Golod–Shafarevich count on the presentation and on the mod-p homology of finite-index subgroups
  fp-intermediate-growth-iff-subexponential-truncation: that is the truncation equivalence; this bounds the homology of finite-index subgroups of any finitely presented group of subexponential growth
---

**ESTABLISHED** through `fp-subexponential-growth-sqrt-mod-p-betti-proof`.

Let `G = ⟨X | R⟩` be a finite presentation of a group of subexponential growth, and let `p` be a
prime. Write `c = |R| − |X| + 1` and `d_p(U) = dim_{F_p} H₁(U; F_p)`.
1. `c ≥ 0`, that is, `|X| − |R| ≤ 1`.
2. Every subgroup `U` of finite index `j` with `d_p(U) ≥ 2` satisfies `(d_p(U) − 2)² ≤ 4jc`. Hence
   `d_p(U) ≤ 2 + 2√(jc)`.
3. If `c = 0` (a deficiency-one presentation), then `d_p(U) ≤ 2` for every finite-index subgroup `U`
   and every prime `p`.

No novelty is claimed. The claim directly combines the imported Golod–Shafarevich presentation test
with the generator and relator counts of covering presentations.

Examples:
- `Z² = ⟨a,b | [a,b]⟩` has `c = 0` and polynomial growth, with `d_p(U) = 2` for all `U`.
- `Z³` with its balanced presentation has `c = 1`.
