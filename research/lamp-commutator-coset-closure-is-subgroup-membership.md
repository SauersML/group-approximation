---
rg: 2
id: lamp-commutator-coset-closure-is-subgroup-membership
kind: claim
title: The reversed commutator lamp lies in the coset-parity closure iff two subgroup memberships hold
distinct_from:
  kun-thom-wreath-lamp-quotient-nonsurjunctive: that asks for a non-closed lamp submodule giving a strict automaton; this decides, for the weight-four commutator generator, exactly when its reversal enters the coset-parity closure, and resolves that test negatively for free generators.
  residually-permutational-lamp-extensions-are-surjunctive: that proves closed submodules give surjunctive quotients using all permutation maps; this isolates the coset-projection sub-family and computes one closure membership as a pair of subgroup memberships.
artifacts:
  - research/artifacts/lamp-commutator-coset-closure-2026-09-12.md
---

**ESTABLISHED** by `lamp-commutator-coset-closure-subgroup-membership-proof`, after a correction
from w3-vf-nonlinear (Section 21 of its verification artifact). The first landing (330d3b39cb)
stated a single membership. That equivalence was false; the corrected statement below has two.

Let `P = F_2[G/Gamma]`, `a, b in G`, and

    v = (1+a)(1+b) e_Gamma,   w = (1+b)(1+a) e_Gamma,   m = b^-1 a^-1 b a,   U = F_2[G] v.

Let `U^c` be the **coset-parity closure** of `U`: the intersection of the kernels of the coset
projections `pi_S : P -> F_2[G/S]`, `e_(g Gamma) -> e_(g S)`, over all subgroups `S >= Gamma` with
`pi_S(U) = 0`. Put `S_0 = <Gamma, ab, a^-1 b>` and `S_1 = <Gamma, b>`. Then

    w in U^c   <=>   m in S_0   and   a^-1 b a in S_1.

Because `U <= U-bar <= U^c` (the permutation closure uses more maps), **either `m notin S_0` or
`a^-1 b a notin S_1` implies `w notin U-bar`**: the reversed commutator is not in the permutation
closure.

**Calibration (w3-vf-nonlinear).** The single-membership version fails: in `G = S_3`, `Gamma = 1`,
`a = (12)`, `b = (13)`, `S_0 = A_3` contains `m`, yet `S = <b>` has `pi_S(v) = 0` and
`pi_S(w) = e_(aS) + e_(baS) != 0`, because `a^-1 b a = (23) notin <b>`.

**Consequences.**
- **Smallest test of the root is negative for free generators.** In `F(a,b)`,
  `m notin <ab, a^-1 b>` (Stallings folding, artifact Lemma 2.1) and `a^-1 b a notin <b>`. So whenever
  `a, b in N` lie in a free subgroup with `<a,b> cap S_0 = <ab, a^-1 b>` (or `<a,b> cap S_1 = <b>`),
  the reversed commutator `w notin U-bar`, and Example 5.4 of
  `kun-thom-wreath-lamp-quotient-nonsurjunctive` resolves negatively, just as the single fibre pairs
  of Example 3.4 did.
- **Coset parity suffices (artifact Lemma 0.1).** If `U = U^c` then `U = U-bar` and `W/U` is
  surjunctive by `residually-permutational-lamp-extensions-are-surjunctive`; `U^c` is idempotent
  and `W/U^c` is surjunctive for every `U`. So the only room for a counterexample is the gap
  `U-bar / U`.
- **Residue for the commutator class.** A non-closed weight-four commutator submodule needs both
  `m in <Gamma, ab, a^-1 b>` and `a^-1 b a in <Gamma, b>`, while `w` is still separated from `U` by
  some Hecke operator with cancellation. No such pair is known.
