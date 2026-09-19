---
rg: 2
id: bounded-output-energetic-decoder-gives-the-canonical-ceiling
kind: claim
title: A bounded-output energetic decoder gives the reverse-Kleene canonical ceiling without a modulus
distinct_from:
  cyclic-carrier-energy-stability: that asks for the energy ceiling on every small-defect tuple in arbitrary dimension; this asks only for bounded-dimensional decoded tuples along canonical-profile microstate sequences.
  trace-conditioned-reverse-kleene-collapse: that directly bounds a marked word on tuples satisfying finitely many canonical moment tests; this extracts an exact energetic representation by compactness in a bounded output dimension.
  subhomogeneous-energetic-carrier-no-strict-gap: that rules out making the whole source carrier subhomogeneous; this only bounds the nonfunctorially decoded output and places no type-I condition on the source corner.
  gowers-hatami-finite-group-hs-stability: that corrects an approximate multiplication table for one finite group in a dimension comparable to the input; this may shrink an arbitrarily large canonical microstate to an unrelated dimension bounded once and for all.
---

Let `G=<X|R>` be finitely presented and let `E` be a finite continuous
rational trace-polynomial energy.  Suppose there is an integer `D` with the
following qualitative decoder property.

For every canonical-profile microstate sequence `U_n` for `G`, there are
integers `1<=r_n<=D` and tuples `V_n in U(r_n)^X` such that

```text
def_R(V_n)->0,
liminf_n (E(V_n)-E(U_n))>=0.                             (BOD1)
```

Then

```text
G is nonhyperlinear OR E_reg<=beta_fd.                  (BOD2)
```

No computable modulus, input/output dimension comparison, or operator
correction is needed.  In a reverse-Kleene compiler, `D` may depend on the
machine index.  It is enough that the NONHALT branch prove `(BOD1)` under the
hypothesis that a canonical-profile microstate sequence exists.

The word “bounded” must apply to the decoded output, not to a C-star carrier
containing the energy.  By
`subhomogeneous-energetic-carrier-no-strict-gap`, making
the entire central finite-packet/normalizer carrier uniformly
subhomogeneous forces `E_reg<=beta_fd` for every trace and therefore cannot
also furnish the strict regular gap.  The live target is a nonfunctorial,
canonical-profile-dependent extraction of one bounded tuple.
