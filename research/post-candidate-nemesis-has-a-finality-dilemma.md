---
rg: 2
id: post-candidate-nemesis-has-a-finality-dilemma
kind: claim
title: A post-candidate nemesis cannot be both new and tested by its own witness
distinct_from:
  halt-now-certificate-area-still-needs-a-crossing-envelope: that precomputes the hypothetical halt certificate and finds the quantitative crossing obstruction; this first rules out appending a challenge only after recognizing a candidate.
  kleene-self-destroying-microstate-lemma: that searches one fixed open window for an already compiled presentation; this proves a candidate-triggered moving presentation is not an instance of that lemma.
---

**ESTABLISHED.**  Suppose a self-referential machine recognizes a rational
tuple `U` for the relators emitted so far and then appends a finite nemesis
packet `E(U)` satisfying

```text
every extension of U to E(U) has E(U)-defect >=gamma(U)>0. (PCN1)
```

There are only two schedules.  If the machine halts after testing only the
old prefix, `U` was never tested against the final presentation containing
`E(U)`, so halting soundness for final microstates says nothing about it.  If
the halt test also requires `E(U)`-defect below
`delta(U)<gamma(U)`, `(PCN1)` prevents the halt.  New generators have the
same issue: before the update `U` does not assign them; afterward no accurate
assignment exists.

The nonmoving implementation puts a universal simulator and every challenge
template in the presentation from the start.  A hypothetical halt transcript
then selects one pre-encoded payload.  This repairs finality but is exactly
`halt-now-certificate-area-still-needs-a-crossing-envelope`: if semantic
transport costs `A(U)`, the candidate must cross a window such as

```text
Def(U)<b/A(U).                                         (PCN2)
```

Computing `A(U)` from its complete code, dimension, defect and proposed
challenge makes the test semidecidable, but hyperlinearity supplies no
candidate-dependent crossing rate.  Hence appending is unsound, testing is
self-blocking, and pre-encoding restores the diagonal-rate obstruction.

Reverse-Kleene proof introspection is different: it never treats a pre-update
tuple as a model of a post-update group, and instead requires qualitative
collapse of one fixed mark in the already final presentation.

