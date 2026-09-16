---
rg: 2
id: binary-three-address-strict-automata-are-linear
kind: claim
title: Over every group, an injective non-surjective binary automaton with at most three memory elements is a parity rule on a non-sofic memory group
distinct_from:
  three-address-binary-injective-rules-are-balanced: that excludes unbalanced rules at memory size three; this uses it and then excludes every balanced non-affine rule, so only the parity rule survives, and it identifies the survivor with support-three direct finiteness over F_2.
  binary-strict-pairs-need-a-memory-with-four-elements: that excludes strictness when encoder and decoder memories both have at most three elements; this allows a decoder of any size, and instead of excluding strictness it pins the encoder rule down to parity.
  monotone-binary-injective-rules-are-copies: that excludes monotone rules at every memory size through constant backgrounds; this handles every rule at memory size three, using single flips, coset backgrounds and a flip parity system.
  single-patch-ternary-rules-reduce-to-linear-strictness: that reduces ternary rules one patch away from affine to linear strictness; this reduces every binary three-address rule, with no distance assumption.
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse over a finite field into a strict linear automaton; this is the converse for binary automata with three memory elements, linear or not.
artifacts:
  - research/artifacts/binary-three-address-strict-automata-linear-2026-09-16.md
---

**Statement.** Let `G` be a group and `tau : {0,1}^G -> {0,1}^G` an injective, non-surjective cellular
automaton, `tau(x)(h) = mu(x(h m) : m in M)`, whose memory has at most three elements. Then:
- its minimal memory `M = {m_0, m_1, m_2}` has exactly three elements;
- `mu = x_0 + x_1 + x_2 + epsilon` for some `epsilon in F_2`;
- the group `<M m_0^-1>` is not sofic.

Equivalently, `L(x)(h) = x(h m_0) + x(h m_1) + x(h m_2)` is a strict linear automaton over `F_2`. The
same holds iff `1 + a + b in F_2[G]`, with `a = m_1 m_0^-1` and `b = m_2 m_0^-1`, has a left inverse
but is not a unit (artifact, Proposition 6.2).

**Consequence.** Binary automata with at most three memory elements are surjunctive over `G` iff
`F_2[G]` has no support-three one-sided unit that is not a unit. That remaining question is
`f2-support-three-one-sided-units-are-units`.

**Proof sketch** (artifact, Sections 2 to 6).
- **Seventeen rules.** Balance and the constant test leave, up to output complement, seventeen rules
  on three effective addresses:
  - majority;
  - parity;
  - six multiplexers and six rules `x_a + x_b (1 + x_c)`;
  - three selector rules `x_s ? AND : OR`.
- **Majority.** A single flip on the zero background is invisible.
- **Lemma C rules.** With `u = m_q m_p^-1`, `v = m_r m_p^-1` and `U = <u>`, the background
  `1_{U m_p}` or its complement collides with a constant, unless `v in U`. In that case the memory
  group is cyclic.
- **Selector rules.** Flipping the selector site is invisible iff a three-equation system over `F_2`
  is solvable. It is unsolvable only when `M m_s^-1` is a subgroup of order three.
- **Soficity.** Right translation and restriction to `<M m^-1>` show that a sofic memory group forces
  surjectivity.
