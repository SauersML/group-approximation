---
rg: 2
id: finite-dimensional-chart-reps-kill-one-transvection-lift
kind: claim
title: The one-transvection lift of s0 has no left inverse supported in GL_2 of any chart subalgebra with a nonzero finite-dimensional representation, the Jacobson algebra included
distinct_from:
  one-transvection-ternary-s0-lift-is-left-invertible: that is the open lift claim; this restricts where a left inverse can be supported and does not decide it
  leavitt-unit-hosts-exclude-matrices-over-commutative-rings: that excludes finite-dimensional hosts for the whole ternary unit group with z -> -1; this uses finite-dimensional representations of proper subgroups such as GL_2(F_3<s0,t0>), which exist, and shows that one lift stays non-invertible there
  depth-monotone-configurations-cannot-force-ternary-minus-one: that places configurations in depth-monotone subalgebras to get a weakly finite image of the whole summand; this needs no depth monotonicity, since the Jacobson chart mixes both directions, and shows one element is not invertible in a tensor-cube representation
artifacts:
  - research/artifacts/ternary-one-transvection-two-piece-lift-2026-09-12.md
---

**ESTABLISHED** (proof: artifact Section 8, route `finite-dimensional-chart-reps-kill-one-transvection-lift-proof`).
Verified: `w4-vf-linear-b` PASS (Section 41 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, 110282f9eb).

**Setting.** `G = L_(F_3)(1,2)^x`, `S_- = eps_- F_3[G]`, `d1 = 1 + s1 t1`, `P1 = 2(1 - [d1])`, and
`h = [[0,1],[-1,s0]]` in the `{0,1}` chart, as in `one-transvection-ternary-s0-lift-is-left-invertible`.

**Theorem** (artifact Proposition E). Let `H <= G` contain `z, d1, h`. Suppose `H` has a representation `psi0`
on a nonzero finite-dimensional space `V` over a field of characteristic 3, with `psi0(z) = -1`, such that
`psi0(h)` carries the `+1`-eigenspace `V+` of `psi0(d1)` onto the `-1`-eigenspace `V-`. Then `P1[h]P1` has no
left inverse in `P1 eps_- F_3[H] P1`.

**Why.**
- `rho = psi0 ⊗ psi0 ⊗ psi0*` is a unital ring map on `eps_- F_3[H]`.
- It sends `P1` to the projection onto the odd blocks `V_a ⊗ V_b ⊗ V_c*`, those with `abc = -1`.
- A left inverse would make the compression of `rho(h)` to the odd part onto.
- Its image misses `V+ ⊗ V+ ⊗ V-*`, because `psi0(h)` has no `V+ -> V+` block and `psi0(h)^(-1)` has no
  `V- -> V-` block.

**Instances** (artifact Corollaries E.1 and E.2). Take `H = GL_2(A)` for any chart subalgebra `A ∋ s0` with a
unital map `A -> M_n(K)`, `n >= 1`, or `H = GL_C(A)` in the chart of a complete prefix code `C`, when `A`
contains the chart entries of `h` and `h^(-1)`:
- `F_3[s0]`, `F_3<s0,s1>`, and every residually finite-dimensional `A`;
- the Jacobson algebra `F_3<s0,t0>`, which carries the partner `k = [[0,-1],[1,t0]]` and the finitary
  involution `diag(1, 1 + e)`, where `e = 1 - s0 t0`;
- `F_3<s0,t0,t1>`.

These groups need not be residually finite, and their soficity plays no role.

**Consequence.** The chart entries of the support of any left inverse generate an algebra with no nonzero
finite-dimensional representation. An example is one containing `s0, t0, s1, t1`, as the Thompson unit
`[[s0, s1 t0],[0, t1]]` does. The open claim is not refuted.
