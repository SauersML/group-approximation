---
rg: 2
id: canonical-reverse-kleene-compiler-equivalence-proof
kind: route
title: Use a constant nonhyperlinear seed and the existing canonical reverse-Kleene diagonals
target: canonical-reverse-kleene-compiler-is-goal-equivalent
requires:
  - canonical-profile-kleene-higman
  - one-mark-gram-collapse-suffices-for-reverse-kleene
---

For either compiler-to-seed implication, apply the corresponding reverse
Kleene theorem.  It produces a recursively presented nonhyperlinear group and
then an effective Higman embedding into a finitely presented nonhyperlinear
host.

Conversely, hard-code one finitely presented nonhyperlinear group `H` and the
unit mark.  This is a total constant compiler.  Hyperlinearity of `H` is
equivalent to existence of a full canonical-profile microstate sequence, so
the sequence domain quantified by `(CPK2)` is empty.  For `(MGC4)`, its
additional hypothesis that `H` is hyperlinear is false.  Both NONHALT clauses
are therefore vacuous, while the unit mark supplies the HALT nonvanishing
clause.

No effective passage from an arbitrary description of a nonhyperlinear group
to this compiler is asserted.  The forward construction begins only after a
specific finite presentation of a nonhyperlinear seed has been supplied.
