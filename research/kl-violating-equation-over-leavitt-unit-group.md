---
rg: 2
id: kl-violating-equation-over-leavitt-unit-group
kind: claim
title: A Kervaire--Laudenbach-violating equation over the binary Leavitt unit group
refuted_by: [kl-holds-over-binary-leavitt-unit-group]
distinct_from:
  kervaire-laudenbach-holds-for-hyperlinear: that is the established positive theorem for hyperlinear groups; this asks for a violation over one specific group, which would refute hyperlinearity of that group
  openai-leavitt-unit-nonsofic: that is the nonsoficity of the same group; this concerns its hyperlinearity, which that result explicitly does not decide
---

Exhibit a one-variable equation `w in Z * R^x`, where
`R^x = L_(F_2)(1,2)^x` is the binary Leavitt unit group, with nonzero total
exponent `epsilon(w) != 0`, that has **no** solution in any group containing
`R^x`.

By `kervaire-laudenbach-holds-for-hyperlinear` such an equation cannot exist
over a hyperlinear group, so producing one would prove `R^x` nonhyperlinear.

**Explicitly conjectural, and hard for a reason that must be stated.**  No
Kervaire--Laudenbach-violating equation is known over **any** group at all.
Nitsche--Thom record that the conjecture is one "to which to date no
counterexamples are known".  So this claim does not merely ask for a
computation over a particular group: it asks to refute the
Kervaire--Laudenbach conjecture itself, and to do so over a group whose
hyperlinearity is exactly what is in question.  Nobody should treat it as a
tractable target.

**Its real value is as an instrument, in two directions.**

1. *Falsification.*  It is a cheap sanity check on any candidate: before
   investing in a nonhyperlinearity argument for a group, one may look for
   an obvious KL obstruction, and finding none costs little.
2. *Structural constraint.*  Contrapositively, any proof that a group is
   nonhyperlinear must be consistent with KL-solvability over it — every
   one-variable equation of nonzero total exponent must still be solvable in
   some overgroup, or else the argument has proved something far stronger
   than intended and should be suspected.  This is a standing consistency
   condition on the whole `non-hyperlinear-group` programme, not only on this
   route.

The binary Leavitt unit group is a reasonable place to look only because it
is unusually concrete for equation-solving — explicit generators and
relations, a prefix-code normal form — and because it is the one group now
known to be nonsofic whose hyperlinearity is open.

**Additional necessary condition from the 2026-09-07 matrix-root argument.**
`nonsingular-adjunction-preserves-approximation-radicals` proves that any
nontrivial coefficient killed by such an equation must lie in both the MF
and hyperlinear radicals of the coefficient group. Moreover,
`nonsingular-equations-preserve-matrix-certificates` shows that a finite
normal-closure identity using `A` old-relator factors must already furnish
the old coefficient norm bound with constant `A`; occurrences of the new
nonsingular equation contribute zero after exact matrix root substitution.
These are necessary conditions, not a construction of a violating word.

**2026-09-11: where the lane now sits.**  `R^x` is simple
(`binary-leavitt-unit-group-is-simple`), so a violation kills every
coefficient and is equivalent to
`leavitt-degree-kernel-normally-generated-by-one-word` (the route pair
`leavitt-kl-violation-via-total-cyclic-collapse` /
`leavitt-kl-violation-forces-kernel-normal-generation`).  The lane lives
inside the stable branch of `leavitt-steinberg-hs-stability-fork`
(`leavitt-kl-violation-selects-the-stable-steinberg-branch`), and the unstable
branch refutes it (`kl-leavitt-holds-on-the-unstable-steinberg-branch`, into
the negation `kl-holds-over-binary-leavitt-unit-group`).  Coefficient packets
whose entries generate a residually finite-dimensional subalgebra of `L`
inject at every length (`leavitt-rfd-entry-packets-satisfy-kl`), so a
candidate must carry non-residually-finite-dimensional entry behaviour such as
a one-sided inverse pair.  From ten variable occurrences on, a candidate must
also be nearly periodic: a word without an exact repeated block of about a
sixth of its length satisfies relative `C'(1/6)` and injects every coefficient
group (`kl-small-cancellation-words-inject-every-coefficient-group`).  A
candidate whose `t`-exponents are all `+-1` must have same-sign corner labels
that are not free, or a sign-change coefficient absorbed by them
(`kl-unit-exponent-words-inject-when-same-sign-corners-are-free`).  This covers
all window cyclic-cover words and settles the length-six classes `+++-+-` and
`++-++-` generically (`kl-length-six-four-sign-change-words-inject`).

What remains is the conjunction of two independent problems.  The analytic
problem is the stable branch: `R^x` must have full hyperlinear radical.  The
combinatorial problem is a collapse mechanism.  Even over a coefficient group
with no nontrivial tracial approximations nothing forces a nonsingular word to
normally generate the degree kernel.  Whatever the certificate does, it must
interleave old relators between uses of `w`.  Every equality or conjugacy
between coefficient words derived from `w` alone already holds in the free
group on the coefficient letters: free groups satisfy the conjecture, their
finite-dimensional unitary representations extend across the equation, and
free groups are conjugacy separable.
