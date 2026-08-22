---
rg: 2
id: atlas-q14-finite-quotient-is-simple-overgroup-test
kind: claim
title: The augmented Atlas quotient has a finite escape exactly when a larger finite simple group carries one marked pair of A8 copies
distinct_from:
  atlas-a4-finite-quotient-escape-fence: that gives the injective-or-trivial chart dichotomy and turns any finite quotient into a matrix escape; this removes solvable radicals and all extension data from the augmented finite-quotient question.
  atlas-a4-19243-classical-collapse: that excludes relative automorphism alignments inside A8; this identifies the exact finite-simple overgroup condition left after that exclusion.
  atlas-q14-augmented-zero-set-has-x30-one-escape: that equates exact matrix escape with existence of some finite quotient; this reduces the latter existence question to one explicit finite-simple marked-pair test.
---

Let

```text
Gamma_+=(A8*A8)/<<thirty A4 packet words,q_19243,q_14>>. (SOT1)
```

Then `Gamma_+` has a nontrivial finite quotient if and only if there are a
nonabelian finite simple group `S` and injective maps

```text
i_1,i_2:A8 -> S                                      (SOT2)
```

whose images generate `S` and which satisfy the following finite marked
system:

1. the twelve distinct cross-chart pair-cube relations carried by the
   `K_(2,2) disjointUnion K_(2,4)` packet graph;
2. the single marked word `q_19243(i_1,i_2)=1`;
3. the commuting-involution relation

   ```text
   [i_1(t23),i_2(t23)]=1.                            (SOT3)
   ```

The simple group in `(SOT2)` must be strictly larger than `A8`.  Thus the
augmented finite-quotient fork has no hidden solvable-radical, extension, or
multiplicity issue: its exact residue is the existence of one larger finite
simple overgroup containing a generating marked pair of `A8` subgroups with
the twelve packet incidences, collision `19243`, and the one commuting pair
in `(SOT3)`.

This is an exact reduction, not a construction or a nonexistence theorem.
It rules out `S=A8`, but it does not rule out a larger finite simple overgroup.
In particular it does not by itself settle whether the augmented matrix zero
set is empty.
