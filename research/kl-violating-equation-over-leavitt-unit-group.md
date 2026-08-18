---
rg: 2
id: kl-violating-equation-over-leavitt-unit-group
kind: claim
title: A Kervaire--Laudenbach-violating equation over the binary Leavitt unit group
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
