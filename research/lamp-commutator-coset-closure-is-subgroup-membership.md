---
rg: 2
id: lamp-commutator-coset-closure-is-subgroup-membership
kind: claim
title: The reversed commutator lamp lies in the coset-parity closure iff a commutator lies in a finitely generated subgroup
distinct_from:
  kun-thom-wreath-lamp-quotient-nonsurjunctive: that asks for a non-closed lamp submodule giving a strict automaton; this decides, for the weight-four commutator generator, exactly when its reversal enters the coset-parity closure, and resolves that test negatively for free generators.
  residually-permutational-lamp-extensions-are-surjunctive: that proves closed submodules give surjunctive quotients using all permutation maps; this isolates the coset-projection sub-family and computes one closure membership as a subgroup membership.
artifacts:
  - research/artifacts/lamp-commutator-coset-closure-2026-09-12.md
---

**ESTABLISHED** by `lamp-commutator-coset-closure-subgroup-membership-proof`.

Let `P = F_2[G/Gamma]`, `a, b in G`, and

    v = (1+a)(1+b) e_Gamma,   w = (1+b)(1+a) e_Gamma,   m = b^-1 a^-1 b a,   U = F_2[G] v.

Let `U^c` be the **coset-parity closure** of `U`: the intersection of the kernels of the coset
projections `pi_S : P -> F_2[G/S]`, `e_(g Gamma) -> e_(g S)`, over all subgroups `S >= Gamma` with
`pi_S(U) = 0`. Then, with `S_0 = <Gamma, ab, a^-1 b>`,

    w in U^c   <=>   m in S_0.

Because `U <= U-bar <= U^c` (the permutation closure uses more maps), **`m notin S_0` implies
`w notin U-bar`**: the reversed commutator is not in the permutation closure.

**Consequences.**
- **Smallest test of the root is negative for free generators.** In `F(a,b)`,
  `m = b^-1 a^-1 b a notin <ab, a^-1 b>` (Stallings folding, artifact Lemma 2.1). So whenever
  `a, b in N` lie in a free subgroup with `<a,b> cap S_0 = <ab, a^-1 b>`, the reversed commutator
  `w notin U-bar`, and Example 5.4 of `kun-thom-wreath-lamp-quotient-nonsurjunctive` resolves
  negatively, just as the single fibre pairs of Example 3.4 did.
- **Coset parity suffices (artifact Lemma 0.1).** If `U = U^c` then `U = U-bar` and `W/U` is
  surjunctive by `residually-permutational-lamp-extensions-are-surjunctive`; `U^c` is idempotent
  and `W/U^c` is surjunctive for every `U`. So the only room for a counterexample is the gap
  `U-bar / U`.
- **Residue for the commutator class.** A non-closed weight-four commutator submodule needs
  `m in <Gamma, ab, a^-1 b>` while `m` is seen by a Hecke operator with cancellation but by no
  coset projection. No such pair is known.
