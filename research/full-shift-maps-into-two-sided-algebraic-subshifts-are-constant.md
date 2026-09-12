---
rg: 2
id: full-shift-maps-into-two-sided-algebraic-subshifts-are-constant
kind: claim
title: Every automaton from a full shift into a two-sided algebraic subshift over an icc group is constant
distinct_from:
  full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant: that closes coset shifts with infinite stabilizers; this closes linear subshifts cut out by a nonzero two-sided ideal of F_p[G] over an icc group, where stabilizers are trivial, including the Leavitt kernel subshift.
  subshift-self-embedding-carries-no-surjunctivity-content: that shows the Leavitt subshift self-embedding also runs over a surjunctive free group; this shows no full shift maps nonconstantly into that subshift at all, which closes absorption designs.
  leavitt-kernel-annihilator-strict-self-embedding: that builds a strict self-embedding of the Leavitt kernel subshift; this shows the same subshift receives only the zero automaton from every full shift.
artifacts:
  - research/artifacts/gottschalk-table-realization-and-evasion-2026-09-12.md
---

**ESTABLISHED** by `algebraic-subshift-rigidity-proof`.

**Theorem.** Let `G` be a group whose nontrivial conjugacy classes are all infinite,
`p` a prime, `I` a nonzero two-sided ideal of `F_p[G]`, and

    X_I = { x in F_p^G : sum_g x(g) r_g = 0 for all r in I }.

For every finite alphabet `A`, every continuous equivariant map `A^G -> X_I` is
constant. Its value is a constant configuration `c` with `c eps(r) = 0` for all `r`
in `I`.

**Leavitt case.**
- Take `G = L_(F_2)(1,2)^x` and `I = ker(F_2[G] -> L_(F_2)(1,2))`. Then `X_I` is the
  subshift of `leavitt-kernel-annihilator-strict-self-embedding`.
- `I` contains `[1] + [g] + [g^2]`, where `g = (1+s_0t_1)(1+s_1t_0)` is the standard
  unit of order three. Its augmentation is `1`.
- `G` is icc because it is infinite and simple
  (`binary-leavitt-unit-group-is-simple`).

So every automaton from any full shift into `X_I` is zero.

**Consequences for Gottschalk designs.**
- **No absorption.** No full shift is conjugate to `W × X_I`: the projection would
  be a nonzero automaton into `X_I`. So the self-similarity `X_I ≅ X_I × X_I`
  cannot be absorbed into a full shift to give `A^G ≅ A^G × X_I`.
- **No factors.** No full shift factors onto `X_I`, even through nonlinear
  intermediate subshifts.
- **Other quotient rings.** The same holds over any icc group for the dual subshift
  of any quotient ring of `F_p[G]` with nonzero kernel. The quotient defect of
  `direct-finiteness-not-inherited-by-quotients` is invisible to full shifts.

**The right-ideal hypothesis is essential.** For a left ideal `F_p[G]a`, the
subshift `X_I` is the kernel of the linear automaton of `a`. It receives the linear
automaton of any `b != 0` with `ab = 0`. The Kaplansky lane works in such kernels,
and this claim does not touch it.
