---
rg: 2
id: canonical-reverse-kleene-compiler-is-goal-equivalent
kind: claim
title: A bare canonical-profile reverse-Kleene compiler is equivalent to finitely presented nonhyperlinearity
distinct_from:
  threshold-free-mf-compiler-equivalence: that classifies the operator-norm MF-radical compiler and uses a marked non-MF seed; this is the normalized-Hilbert--Schmidt/canonical-trace analogue, where the seed direction is vacuous because a nonhyperlinear group has no full canonical microstate sequence.
  canonical-profile-kleene-higman: that proves the useful compiler-to-nonhyperlinear direction; this adds the converse and audits the exact existential strength of the bare compiler interface.
  one-mark-gram-collapse-suffices-for-reverse-kleene: that weakens the NONHALT endpoint needed by the diagonal; this observes that even that weaker bare endpoint has a vacuous constant compiler once a nonhyperlinear seed is assumed.
---

**ESTABLISHED.**  The following existence statements are equivalent.

1. There is a finitely presented nonhyperlinear group.
2. There is a total computable compiler to uniformly recursively presented
   marked groups satisfying `(CPK1)--(CPK2)` of
   `canonical-profile-kleene-higman`.
3. There is a total computable compiler satisfying `(MGC1)--(MGC4)` of
   `one-mark-gram-collapse-suffices-for-reverse-kleene`.

The converse directions already contain the mathematical content: `2 => 1`
is `canonical-profile-kleene-higman`, and `3 => 1` is
`one-mark-gram-collapse-suffices-for-reverse-kleene`.

For `1 => 2,3`, fix a finite presentation of a nonhyperlinear group `H` and
use the constant compiler

```text
Gamma_e=H,                 p_e=1 in Q[H]
```

for every machine index `e`.  The HALT survival clauses hold because `1` is
nonzero.  A finitely generated group is hyperlinear exactly when it admits a
full canonical-profile normalized-HS microstate sequence.  Hence `H` admits
no such sequence, and the universal NONHALT clause `(CPK2)` is true over the
empty collection of canonical sequences.  In the mark-Gram formulation,
the antecedent of `(MGC4)` explicitly includes that `Gamma_e` is hyperlinear;
for this constant compiler that antecedent is false.

This direction is deliberately vacuous.  It gives no decoder, no quantitative
collapse, no canonical sequence, and no algorithm which discovers a
nonhyperlinear seed.  It is only a nonuniform existence implication after a
particular finite presentation of `H` has been fixed.  Consequently the bare
`CPK` or mark-Gram interface is not by itself a source of nonhyperlinearity.
A productive compiler theorem must impose independently checkable structure
on its output, give a nonvacuous NONHALT collapse mechanism, or otherwise be
constructed without assuming the desired seed.

